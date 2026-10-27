module

public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierGaps
public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierLinear
public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierStatement
public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierSetup

public section

namespace CFSG.Semidihedral.SimpleLayerFrontier

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem frontierAt_of_local_theorems
    (hB : StationaryCoverageStatement)
    (hF : FieldFactorOneStatement) (hA : FixedCoreNontrivialStatement)
    (hU : UnitaryBranchStatement) (h5 : ParameterFiveRecognitionStatement)
    (hSN : SevenNineCoreHypothesis) (hFO : FieldFactorOneHypothesis)
    (G : Type) [Group G] [Finite G]
    (hrec : ProperSubgroupRegularity.SmallerSimpleRecognition G) : FrontierAt G := by
  intro _ hGnonab n hn S0 f0 t ht _ hLnonab hcentral m hm _ U hU'
  have hrec' : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G := hrec
  obtain ⟨hG, hnc, -, -, p, f, hp, hpodd, hf, hq5, hmodel⟩ :=
    frontier_layer_setup hGnonab n hn S0 f0 t ht hLnonab m hm U hU'
  obtain ⟨S, fS, -, hcent⟩ :=
    (InvolutionFusion.involution_centered_sylow_existence n hn S0 f0 hG t ht).2
  have ht' : t = (fS (r n) : G) ^ 2 ^ (n - 2) := by
    rw [← hcent, Subgroup.coe_pow]
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hpodd) even_two
  have hqodd : Odd (p ^ f) := hpodd.pow
  rcases Nat.lt_or_ge 5 (p ^ f) with hgt | hle
  ·
    have hcov := hB G hGnonab hrec' n hn S fS t ht' hLnonab hcentral hnc p f hp hpodd hf hgt
      hmodel
    have hY := hF G hGnonab hrec' n hn S fS t ht' hLnonab hcentral hnc p f hp hpodd hf hgt
      hmodel hcov
    obtain ⟨k, hk⟩ := hqodd
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    ·
      have hq1 : p ^ f % 4 = 1 := by omega
      have hA₀ := hA G hGnonab hrec' n hn S fS t ht' hLnonab hcentral hnc p f hp hpodd hf
        (by omega) hmodel hcov hY
      exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hq1,
        hU G hGnonab hrec' n hn S fS t ht' hLnonab hcentral hnc p f hp hpodd hf hq1 hgt hmodel
          hcov hY hA₀⟩)
    ·
      have hq3 : p ^ f % 4 = 3 := by omega
      refine Or.inl ⟨p, f, hp, hp2, hf, hq3, ?_⟩
      by_cases hq7 : p ^ f = 7
      · exact linear_branch_of_stationary_covers hSN hFO G hGnonab hrec' n hn S fS t ht'
          hLnonab hcentral hnc p f hp hpodd hf hq3 hmodel hcov (Or.inl hq7)
      · have hA₀ := hA G hGnonab hrec' n hn S fS t ht' hLnonab hcentral hnc p f hp hpodd hf
          (by omega) hmodel hcov hY
        exact linear_branch_of_stationary_covers hSN hFO G hGnonab hrec' n hn S fS t ht'
          hLnonab hcentral hnc p f hp hpodd hf hq3 hmodel hcov (Or.inr ⟨hY, hA₀⟩)
  ·
    have hq : p ^ f = 5 := le_antisymm hle hq5
    obtain ⟨rfl, rfl⟩ := (Nat.prime_five.pow_eq_iff).mp hq
    exact Or.inr (Or.inl ⟨5, 1, Nat.prime_five, by decide, le_rfl, by decide,
      h5 G hGnonab n hn S fS t ht' hLnonab hcentral hnc hmodel⟩)

theorem frontier_of_local_theorems
    (hB : StationaryCoverageStatement)
    (hF : FieldFactorOneStatement) (hA : FixedCoreNontrivialStatement)
    (hU : UnitaryBranchStatement) (h5 : ParameterFiveRecognitionStatement)
    (hSN : SevenNineCoreHypothesis) (hFO : FieldFactorOneHypothesis) :
    FrontierStatement :=
  frontier_of_inductive_step fun G _ _ hrec =>
    frontierAt_of_local_theorems hB hF hA hU h5 hSN hFO G hrec

end CFSG.Semidihedral.SimpleLayerFrontier
