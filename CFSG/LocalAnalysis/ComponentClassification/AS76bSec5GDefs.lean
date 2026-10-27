module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.AS76b.Sec5

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G]

@[expose] def gMembers (X R : Subgroup G) : Set (Subgroup G) :=
  {T | ∃ x ∈ X, rightConjugate R x = T}

@[expose] def gFused (X R : Subgroup G) : Set G :=
  {v | ∃ x ∈ X, ∃ r ∈ R, r ≠ 1 ∧ x⁻¹ * r * x = v}

structure GHyp51 (V R U W X A B : Subgroup G) : Prop where
  two : ∀ v ∈ V, v * v = 1
  R_le : R ≤ V
  U_le : U ≤ V
  W_le : W ≤ V
  sup_eq : R ⊔ U ⊔ W = V
  inf_R : R ⊓ (U ⊔ W) = ⊥
  inf_U : U ⊓ W = ⊥
  two_lt : 2 < Nat.card R
  card_eq : Nat.card U = Nat.card W
  X_le : X ≤ normalizer (V : Set G)
  A_le : A ≤ X
  B_le : B ≤ X
  A_centR : A ≤ centralizer (R : Set G)
  A_centU : A ≤ centralizer (U : Set G)
  A_normW : A ≤ normalizer (W : Set G)
  B_centR : B ≤ centralizer (R : Set G)
  B_centW : B ≤ centralizer (W : Set G)
  B_normU : B ≤ normalizer (U : Set G)
  A_trans : ∀ w ∈ W, ∀ w' ∈ W, w ≠ 1 → w' ≠ 1 → ∃ a ∈ A, a⁻¹ * w * a = w'
  A_fix : ∀ a ∈ A, ∀ w ∈ W, w ≠ 1 → a⁻¹ * w * a = w → a ∈ centralizer (W : Set G)
  B_trans : ∀ u ∈ U, ∀ u' ∈ U, u ≠ 1 → u' ≠ 1 → ∃ b ∈ B, b⁻¹ * u * b = u'
  B_fix : ∀ b ∈ B, ∀ u ∈ U, u ≠ 1 → b⁻¹ * u * b = u → b ∈ centralizer (U : Set G)
  normal : ∀ n ∈ X, n ∈ normalizer (R : Set G) → ∀ a ∈ A, ∀ b ∈ B,
    ∃ a' ∈ A, ∃ b' ∈ B, ∃ c ∈ centralizer (V : Set G), n⁻¹ * (a * b) * n = a' * b' * c
  one : ∀ T ∈ gMembers X R, T ≠ R → T ⊓ R = ⊥ ∧
    (T ≤ R ⊔ U ∨ T ≤ R ⊔ W ∨ (T ⊓ (R ⊔ U) = ⊥ ∧ T ⊓ (R ⊔ W) = ⊥))
  twoU : ∀ T ∈ gMembers X R, T ≤ R ⊔ U →
    (T = U ∧ ∀ T' ∈ gMembers X R, T' ≤ R ⊔ U → T' = R ∨ T' = U) ∨ T ⊓ U = ⊥
  twoW : ∀ T ∈ gMembers X R, T ≤ R ⊔ W →
    (T = W ∧ ∀ T' ∈ gMembers X R, T' ≤ R ⊔ W → T' = R ∨ T' = W) ∨ T ⊓ W = ⊥
  three : ∃ T ∈ gMembers X R, T ≠ R ∧ T ⊓ (R ⊔ U) = ⊥ ∧ T ⊓ (R ⊔ W) = ⊥

end CFSG.ComponentClassification.AS76b.Sec5
