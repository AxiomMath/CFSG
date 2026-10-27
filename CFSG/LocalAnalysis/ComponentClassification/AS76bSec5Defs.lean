module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.GroupWithZero.Action.Defs

public section

namespace CFSG.ComponentClassification.AS76b.Sec5

variable {V : Type} [AddCommGroup V]

structure Decomp (R U W : AddSubgroup V) : Prop where
  sup_eq : R ⊔ U ⊔ W = ⊤
  inf_R : R ⊓ (U ⊔ W) = ⊥
  inf_U : U ⊓ W = ⊥

variable {X : Type} [Group X] [DistribMulAction X V]

@[expose] def img (x : X) (T : AddSubgroup V) : AddSubgroup V :=
  T.map (DistribSMul.toAddMonoidHom V x)

variable (X)

@[expose] def members (R : AddSubgroup V) : Set (AddSubgroup V) :=
  {T | ∃ x : X, img x R = T}

@[expose] def fused (R : AddSubgroup V) : Set V :=
  {v | ∃ x : X, ∃ r ∈ R, r ≠ 0 ∧ x • r = v}

structure Hyp51 (A B : Subgroup X) (R U W : AddSubgroup V) : Prop where
  two : ∀ v : V, v + v = 0
  decomp : Decomp R U W
  two_lt : 2 < Nat.card R
  card_eq : Nat.card U = Nat.card W
  A_fix : ∀ a ∈ A, ∀ v ∈ R ⊔ U, a • v = v
  B_fix : ∀ b ∈ B, ∀ v ∈ R ⊔ W, b • v = v
  A_W : ∀ a ∈ A, ∀ w ∈ W, a • w ∈ W
  B_U : ∀ b ∈ B, ∀ u ∈ U, b • u ∈ U
  A_trans : ∀ w ∈ W, ∀ w' ∈ W, w ≠ 0 → w' ≠ 0 → ∃ a ∈ A, a • w = w'
  B_trans : ∀ u ∈ U, ∀ u' ∈ U, u ≠ 0 → u' ≠ 0 → ∃ b ∈ B, b • u = u'
  A_free : ∀ a ∈ A, ∀ w ∈ W, w ≠ 0 → a • w = w → ∀ w' ∈ W, a • w' = w'
  B_free : ∀ b ∈ B, ∀ u ∈ U, u ≠ 0 → b • u = u → ∀ u' ∈ U, b • u' = u'
  normal : ∀ n : X, img n R = R → ∀ a ∈ A, ∀ b ∈ B,
    ∃ a' ∈ A, ∃ b' ∈ B, ∀ v : V, (n⁻¹ * (a * b) * n) • v = (a' * b') • v
  one : ∀ T ∈ members X R, T ≠ R → T ⊓ R = ⊥ ∧
    (T ≤ R ⊔ U ∨ T ≤ R ⊔ W ∨ (T ⊓ (R ⊔ U) = ⊥ ∧ T ⊓ (R ⊔ W) = ⊥))
  twoU : ∀ T ∈ members X R, T ≤ R ⊔ U →
    (T = U ∧ ∀ T' ∈ members X R, T' ≤ R ⊔ U → T' = R ∨ T' = U) ∨ T ⊓ U = ⊥
  twoW : ∀ T ∈ members X R, T ≤ R ⊔ W →
    (T = W ∧ ∀ T' ∈ members X R, T' ≤ R ⊔ W → T' = R ∨ T' = W) ∨ T ⊓ W = ⊥
  three : ∃ T ∈ members X R, T ≠ R ∧ T ⊓ (R ⊔ U) = ⊥ ∧ T ⊓ (R ⊔ W) = ⊥

end CFSG.ComponentClassification.AS76b.Sec5
