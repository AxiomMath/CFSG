module

public section

namespace CFSG.KC.ListGroup

@[expose] noncomputable def grpR {α : Type} (n : Nat) (L : List α) :
    Nat → (List α → List α) → List (List α) :=
  L.rec (motive := fun _ => Nat → (List α → List α) → List (List α)) (fun _ _ => [])
    fun x _ r k acc =>
      Bool.rec (r (Nat.sub k 1) fun t => acc (x :: t)) (acc [x] :: r n fun t => t) (Nat.beq k 1)

@[expose] noncomputable def grp {α : Type} (n : Nat) (L : List α) : List (List α) :=
  grpR n L n fun t => t

end CFSG.KC.ListGroup
