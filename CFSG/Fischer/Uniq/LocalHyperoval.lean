module

public import CFSG.Fischer.Uniq.Model

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X]

@[expose] def lineIn (A : Set X) (x y : X) : Set X :=
  {z | z ∈ A ∧ ∀ w ∈ A, w * x = x * w → w * y = y * w → w * z = z * w}

@[expose] def IsLineIn (A L : Set X) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ x * y = y * x ∧ L = lineIn A x y

structure IsHyperovalIn (A U : Set X) : Prop where
  subset : U ⊆ A
  inter : ∀ L, IsLineIn A L → (L ∩ U).ncard = 0 ∨ (L ∩ U).ncard = 2
  closed : ∀ x ∈ U, (fun y => x * y * x) '' U = U

structure IsLocallyHyperoval (D T : Set X) : Prop where
  subset : T ⊆ D
  closed : ∀ s ∈ T, ∀ t ∈ T, s * t * s ∈ T
  nonempty : ∀ s ∈ T, (T ∩ LocalClass D s).Nonempty
  hyperoval : ∀ s ∈ T, IsHyperovalIn (LocalClass D s) (T ∩ LocalClass D s)

@[expose] def pairModel {E : Set X} (hP : Pair X E) : LocalModel E where
  perp x y := (x : X) * y = y * x
  tv x := (Pair.tauE_involutive hP x).toPerm _
  tv_tv x y := Pair.tauE_tauE hP x y
  tv_self x := Pair.tauE_self hP x

theorem pairModel_perp {E : Set X} (hP : Pair X E) (x y : E) :
    (pairModel hP).perp x y ↔ (x : X) * y = y * x :=
  Iff.rfl

theorem pairModel_tv {E : Set X} (hP : Pair X E) (x y : E) :
    ((pairModel hP).tv x y : X) = x * y * x :=
  rfl

end CFSG.Fischer
