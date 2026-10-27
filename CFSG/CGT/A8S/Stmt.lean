module

public import CFSG.CGT.Timmesfeld75.PaperSteps

public section

namespace CFSG.CGT.A8S

open CFSG.CGT.Timmesfeld75

structure A8CtxHyp {G : Type} [Group G] (T T₁ : Subgroup G) : Prop where
  wc : IsWC T
  card8 : Nat.card T = 8
  inf_bot : T ⊓ T₁ = ⊥
  conj : ∃ s : G, T₁ = conjSubgroup s T
  norm1 : Nat.card (normIn T T₁) = 4
  norm2 : Nat.card (normIn T₁ T) = 4
  cent_le : ∀ d ∈ T, d ≠ 1 →
    Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (T : Set G)
  cent_eq : Subgroup.centralizer (T : Set G) = T
  nat : NaturalSL T (Subgroup.normalizer (T : Set G)) 3 1
  compl : ∃ L : Subgroup G, L ⊓ T = ⊥ ∧ T ⊔ L = Subgroup.normalizer (T : Set G)
  trans : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
    ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y

end CFSG.CGT.A8S
