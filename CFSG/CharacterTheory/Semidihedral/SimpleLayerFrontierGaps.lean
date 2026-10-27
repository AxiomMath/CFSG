module

public import CFSG.CharacterTheory.Semidihedral.EscapingLocalEigensubgroups

public section

namespace CFSG.Semidihedral.SimpleLayerFrontier

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

@[expose] def StationaryCoverageStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    PerfectLayerNormalization.OriginalSmallerSimpleRecognition G →
    ∀ (n : ℕ), 4 ≤ n → ∀ (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
      (t : G), t = (fS (r n) : G) ^ 2 ^ (n - 2) →
    ∀ [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))],
      (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) →
      Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ →
      (∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 < p ^ f →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f →
      EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G)

@[expose] def FieldFactorOneStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    PerfectLayerNormalization.OriginalSmallerSimpleRecognition G →
    ∀ (n : ℕ), 4 ≤ n → ∀ (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
      (t : G), t = (fS (r n) : G) ^ 2 ^ (n - 2) →
    ∀ [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))],
      (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) →
      Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ →
      (∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 < p ^ f →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f →
      EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G) →
      (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2

@[expose] def FixedCoreNontrivialStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    PerfectLayerNormalization.OriginalSmallerSimpleRecognition G →
    ∀ (n : ℕ), 4 ≤ n → ∀ (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
      (t : G), t = (fS (r n) : G) ^ 2 ^ (n - 2) →
    ∀ [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))],
      (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) →
      Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ →
      (∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 7 < p ^ f →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f →
      EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G) →
      (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2 →
      (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} ≠ ⊥

@[expose] def UnitaryBranchStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    PerfectLayerNormalization.OriginalSmallerSimpleRecognition G →
    ∀ (n : ℕ), 4 ≤ n → ∀ (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
      (t : G), t = (fS (r n) : G) ^ 2 ^ (n - 2) →
    ∀ [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))],
      (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) →
      Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ →
      (∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → p ^ f % 4 = 1 → 5 < p ^ f →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f →
      EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G) →
      (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2 →
      (N t).map (C t).subtype ⊓ Subgroup.centralizer {(fS (s n) : G)} ≠ ⊥ →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 p f

@[expose] def ParameterFiveRecognitionStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (n : ℕ), 4 ≤ n → ∀ (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
      (t : G), t = (fS (r n) : G) ^ 2 ^ (n - 2) →
    ∀ [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))],
      (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) →
      Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ →
      (∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U) →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1 →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 5 1

end CFSG.Semidihedral.SimpleLayerFrontier
