(* Example 1 *)

(*
This is one way to prove the goal using Rocq tactics.
We introduce the variables and premises, which instantiates
X and Y of type Prop, H of type X (from the first premise of the implication),
and H0 of type Y (from the second premise of the implication).
The proof goal is X, which is easily discharged using H.
*)
Goal forall X Y : Prop, X -> Y -> X.
  intros. apply H.
Qed.

(*
In fact, this proof is so simple, that it can be discharged immediately 
using `auto`.
But what does `auto` actually *do*?
`Show Proof` allows us to inspect the actual proof term constructed via tactics.
In this case, we see that the proof term is a function with four curried arguments:
fun (X : Prop) => fun (Y : Prop) => fun (H : X) => fun (_ : Y) => H
Think of the proof term as saying,
"If you give me propositions X and Y, a proof of X, and a proof of Y,
I will give you a proof of X".
Then the function body can just immediately return the proof of X that was
supplied as the third argument to the function.
*)
Goal forall X Y : Prop, X -> Y -> X.
  auto.
  Show Proof. (* (fun (X Y : Prop) (H : X) (_ : Y) => H) *)
Qed.

(* We can prove the goal in Rocq by supplying the proof term directly. *)
Goal forall X Y : Prop, X -> Y -> X.
  exact (fun X Y H _ => H).
Qed.

(* Example 2 *)
(*
Now our goal is: given three propositions X, Y, and Z,
a proof that X -> Y -> Z, and a proof that X -> Y, supply a proof that X -> Z
(Alternatively, you can read the last part without the parentheses, so that the
last premise supplies a proof of X, and the goal is to prove Z).
First, we introduce variables for the three propositions X, Y, and Z, as well as
the premises H1 (X -> Y -> Z), H2 (X -> Y), and HX (X).
Remember, these names are arbitrary.
Our proof goal is Z.
H1 gives us an implication whose conclusion is Z, so we can apply H1 and now we
just have to show that the premises of H1 hold.
This gives us two goals: X and Y
If we `Show Proof` at this point, we can see the partially-constructed proof term:
(fun (X Y Z : Prop) (H1 : X -> Y -> Z) (H2 : X -> Y) (HX : X) =>
 H1 ?Goal ?Goal0)
We have a function of 6 arguments, whose body is a call to H1, but we haven't
filled in the arguments to H1 yet, so we have two holes (shown as ?Goal and ?Goal0)
We discharge the first proof obligation directly with HX.
Showing the Proof again results in:
(fun (X Y Z : Prop) (H1 : X -> Y -> Z) (H2 : X -> Y) (HX : X) => H1 HX ?Goal)
Now we just have one hole remaining-- we need to prove Y.
We can do this using H2, which gives us X -> Y, and HX, which gives us X.
Our completed proof term is
(fun (X Y Z : Prop) (H1 : X -> Y -> Z) (H2 : X -> Y) (HX : X) =>
 H1 HX (H2 HX))

Worth noting that we have two cases in the Rocq proof (shown using - bullets).
These correspond to the two arguments to H1 in the proof term.
*)
Goal forall X Y Z : Prop,
  (X -> Y -> Z) -> (X -> Y) -> (X -> Z).
  intros X Y Z H1 H2 HX.
  apply H1. Show Proof. 
  - apply HX. Show Proof.
  - apply H2. apply HX.
  Show Proof. (* (fun (X Y Z : Prop) (H1 : X -> Y -> Z) (H2 : X -> Y) (HX : X) => H1 HX (H2 HX)) *)
Qed.

(*
Totally possible to prove the Goal in Rocq just by constructing the proof term
(which, remember, is a function of 6 arguments, whose body is evidence of the
thing we are trying to prove) directly.
*)
Goal forall X Y Z : Prop,
  (X -> Y -> Z) -> (X -> Y) -> (X -> Z).
  exact
    (fun
      (X Y Z : Prop) (H1 : X -> Y -> Z) (H2 : X -> Y) =>
        fun (HX : X) => H1 HX (H2 HX)).
Qed.

(* Another way to prove the Goal by constructing the proof term, slightly more concise. *)
Goal forall X Y Z : Prop,
  (X -> Y -> Z) -> (X -> Y) -> (X -> Z).
  exact (fun X Y Z H1 H2 HX => H1 HX (H2 HX)).
Qed.

(* Example 3 *)
(*
Now let's talk about induction! Induction is a bread-and-butter tactic in Rocq
proofs-- here, we're doing induction on x, which is a nat, so we get two cases:
1. Prove the property for x = 0
2. Prove the property for x = n + 1, assuming the property holds for n
This proof is pretty simple, so both cases can be hammered out with just simpl
and auto. This one-line proof is pretty typical for how Rocq programmers would 
probably prove this goal.
*)
Goal forall x y z : nat, x + (y + z) = (x + y) + z.
  induction x; simpl; auto.
Qed.

(*
Before we get into the proof terms, let's write out the proof using tactics,
but a little more explicitly, without relying on `auto`.
In the first case, we need to prove forall y z : nat, 0 + (y + z) = 0 + y + z,
which is discharged using reflexivity since the left- and right-hand sides of
the equality are syntactically equal (aside from parentheses, but Rocq can
take care of that implicitly for us).
In the second case, we have a new hypothesis above the line:
IHx: forall y z : nat, x + (y + z) = x + y + z
and our proof goal is forall y z : nat, S x + (y + z) = S x + y + z
We instantiate the variables y and z and simplify, so now the proof goal is
S (x + (y + z)) = S (x + y + z)
Now, this is in a shape where we can apply our induction hypothesis! Rewriting,
we get S (x + y + z) = S (x + y + z), which is discharged using reflexivity.
*)
Goal forall x y z : nat, x + (y + z) = (x + y) + z.
  induction x.
  - reflexivity.
  - intros. simpl. rewrite IHx. reflexivity.
  Show Proof.
Qed.

(*
Completing this proof using tactics was pretty straightforward, but what does
the proof term look like? Show Proof prints this:
(fun x : nat =>
 nat_ind (fun x0 : nat => forall y z : nat, x0 + (y + z) = x0 + y + z)
   (fun y z : nat => eq_refl)
   (fun (x0 : nat) (IHx : forall y z : nat, x0 + (y + z) = x0 + y + z)
	  (y z : nat) =>
    eq_ind_r (fun n : nat => S n = S (x0 + y + z)) eq_refl (IHx y z)
    :
    S x0 + (y + z) = S x0 + y + z) x)
which is.... kind of intimidating to look at. But let's break it apart piece by piece.
*)

(*
One thing that's helpful is that we can mix and match writing proof terms
directly and using tactics (it's all the same under the hood anyways).
So immediately, we see this `nat_ind` thing in the proof term, which might be
unfamiliar, so we can `pose` it, which just brings it into scope in the proof
view, so that we can take a look at it more closely:
p:= nat_ind
 : forall P : nat -> Prop,
   P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
Now that we've gotten some practice reading proof terms, we can hopefully pick
apart what's going on here:
For all properties P with type nat -> Prop,
  if we have a proof of P 0
  and we have a proof of the property `forall n, P n -> P (S n)`
  then we can conclude that for all n, P n holds.
That feels a lot like our two cases for inductive proofs, doesn't it?

In this proof, we partially apply nat_ind, providing just the property
in the form of the anonymous function fun a => forall b c, a + (b + c) = (a + b) + c)
which has type nat -> Prop, as desired.
This is the property we would like to prove by induction (it exactly matches
the property in the Goal).
We are left with 2 Goals, corresponding to the third and fourth arguments 
to nat_ind, respectively:
nat_ind (fun a : nat => forall b c : nat, a + (b + c) = a + b + c) 
   ?Goal ?Goal0)

Here, we use tactics to solve these two Goals.
- In the first case, we need to prove 0 + (b + c) = 0 + b + c,
which is discharged with reflexivity.
- In the second case, we need to prove
forall n : nat,
(forall b c : nat, n + (b + c) = n + b + c) ->
forall b c : nat, S n + (b + c) = S n + b + c
And (after intros) we now have an additional premise above the line:
H: forall b c : nat, n + (b + c) = n + b + c
This is our inductive hypothesis.
From here, we can easily solve the goal by simplifying, rewriting with H, and reflexivity.
*)
Goal forall x y z : nat, x + (y + z) = (x + y) + z.
  pose nat_ind.
  pose (fun a => forall b c, a + (b + c) = (a + b) + c).
  apply (nat_ind (fun a => forall b c, a + (b + c) = (a + b) + c)).
  Show Proof.
  - reflexivity.
  - intros. simpl. rewrite H. reflexivity.
Qed.

(*
In the previous proof, we saw how to use the nat_ind function to complete the
proof without using the induction tactic, but we still used tactics to finish the
proof. Here, we'll try to write out the entire proof term, with no Rocq tactics.

The third argument to nat_ind needs to have type `P 0`.
Recall that P is fun a : nat => forall b c : nat, a + (b + c) = a + b + c : nat -> Prop
so we need something with type `forall y z : nat, 0 + (y + z) = (0 + y) + z`.
We can construct this as an anonymous function with two arguments, whose body
is just eq_refl (which has type `forall {A : Type} {x : A}, x = x`).

The fourth argument needs to have type `(forall n : nat, P n -> P (S n))`
Notice that the premise `P n` in the type is what allows us to use the
induction hypothesis in proving the goal.
We end up with a function of four arguments:
1. x0 : nat, which comes from the `forall n` in the type
2. IHx : forall y z : nat, x0 + (y + z) = x0 + y + z, which comes from `P n`
3-4. y z : nat, which come from `forall b c` in the type of P

The body then must have type `S n + (b + c) = S n + b + c`
eq_ind_r has type `forall (A : Type) (x : A) (P : A -> Prop),
                     P x -> forall y : A, y = x -> P y`
intuitively, it says if you know P x and x = y, then you can conclude P y.
There are 6 arguments:
1. A = nat                  This is the type of the input to P, which is nat in our case
2. x = (x0 + y + z)         This is the value for which we know P holds
3. P                        This is the property we want to carry across the equality x = y
                            Note that this is different than the P we have at the top level
                            Here P is `fun n => S n = S (x0 + y + z)`
4. P x = eq_refl            We need to supply a proof that S (x0 + y + z) = S (x0 + y + z)
5. y = (x0 + (y + z))       This is the value we want to conclude that P holds for
6. y = x                    Finally, we need to supply a proof that y = x.
                            We do this by applying our induction hypothesis (IHx y z)
                            Remember, IHx has type `forall y z : nat, x0 + (y + z) = x0 + y + z`
                            so supplying y and z gives us `x0 + (y + z) = x0 + y + z`, as desired.
Phew! So with all 6 arguments, we now conclude P y,
  which says S (x0 + (y + z)) = S (x0 + y + z),
  which is what we needed to prove!
Rocq can infer some of these arguments for us, so we could equivalently write this as
eq_ind_r (fun n => S n = S (x0 + y + z)) eq_refl (IHx y z),
supplying only arguments 3, 4, and 6, leaving the others implicit
(Rocq notation note: the @ tells Rocq not to use implicit arguments)

So to summarize:
`nat_ind` is the induction principle for natural numbers
It takes 3 arguments: 
1. The property we want to prove, P
2. A proof of P 0
3. A proof of the inductive case, (forall n : nat, P n -> P (S n))

We supply 3 arguments:
1. P = fun a => forall b c, a + (b + c) = (a + b) + c
2. fun y z => eq_refl, which proves 0 + (y + z) = (0 + y) + z
3. fun x0 IHx y z => eq_ind_r (fun n => S n = S (x0 + y + z)) eq_refl (IHx y z),
    which uses the induction hypothesis `x0 + (y + z) = x0 + y + z` and
    `eq_ind_r` to transport that equality under S,
    giving `S(x0 + (y + z)) = S(x0 + y + z)`.
*)
Goal forall x y z : nat, x + (y + z) = (x + y) + z.
  pose eq_ind_r.
  exact (nat_ind (fun a => forall b c, a + (b + c) = (a + b) + c)
    (fun y z => eq_refl)
    (fun x0 (IHx : forall y z : nat, x0 + (y + z) = x0 + y + z) y z => 
      @eq_ind_r nat (x0 + y + z) (fun n => S n = S (x0 + y + z)) eq_refl (x0 + (y + z)) (IHx y z))).
Qed.
