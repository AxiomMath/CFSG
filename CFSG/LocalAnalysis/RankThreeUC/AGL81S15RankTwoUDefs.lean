module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open

@[expose] def IsScalarTorus {G : Type} [Group G] (q : ℕ) (U E : Subgroup G) : Prop :=
  E ≤ Subgroup.normalizer (U : Set G) ∧ IsElemAbelian q E ∧ Nat.card E = q ^ 2 ∧
    ∀ α : MulAut G, U.map α.toMonoidHom = U →
      (∃ j : ℕ, ∀ x ∈ E, α x * (x ^ j)⁻¹ ∈ U) ∧ (α * α = 1 → ∀ x ∈ E, α x * x⁻¹ ∈ U)

@[expose] def HasScalarTorus (G : Type) [Group G] (q : ℕ) (U : Subgroup G) : Prop :=
  ∃ E : Subgroup G, IsScalarTorus q U E

end CFSG.LocalAnalysis.RankThreeUC.S15

end
