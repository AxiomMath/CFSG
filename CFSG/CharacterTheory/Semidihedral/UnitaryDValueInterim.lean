module

public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage

public section

namespace CFSG.Semidihedral.UnitaryBranch

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

@[expose] def CentralizerCharacterTrivialStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (n : ℕ), 4 ≤ n → ∀ (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
      (t : G), t = (fS (r n) : G) ^ 2 ^ (n - 2) →
    ∀ [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))],
      (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) →
      Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ →
      (∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 7 ≤ p ^ f →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f →
    ∀ θ : C t →* ℂˣ, (∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1) →
      (∀ g ∈ Subgroup.normalizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
        ∀ c c' : C t,
          (c : G) ∈ Subgroup.centralizer
            ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
          (c' : G) = g * c * g⁻¹ → θ c' = θ c) →
      ∀ c : C t, θ c = 1

end CFSG.Semidihedral.UnitaryBranch
