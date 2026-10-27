module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardComp
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.ComponentClassification.HarrisLit
open CFSG.ASVolI.ChIJK (IsComponentIn)

theorem isMTypeSchur_of_pOmegaPlus (hC4 : POmegaPlusNotLinUnit) {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.IsQuasisimple Y) {c : Y} (hc : c ∈ center Y) (hc2 : orderOf c = 2) {n : ℕ}
    (hn : n = 4 ∨ n = 6) (hm : Blueprint.LieModel (Y ⧸ center Y) .POmegaPlus n 3 1) :
    IsMTypeSchur 3 Y := by
  have hZ : Open.fusionZStar Y = center Y := fusionZStar_eq_center_of_involution hY hc2
  have hmQ : Blueprint.LieModel (Y ⧸ Open.fusionZStar Y) .POmegaPlus n 3 1 :=
    Blueprint.LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZ.symm) hm
  refine Or.inl ⟨isTwoQuasisimple_of_involution hY hc2, ⟨.POmegaPlus, n, 1, hmQ⟩, ?_, ?_⟩
  · rw [hZ]
    exact even_iff_two_dvd.mpr (by
      rw [← hc2]
      exact Subgroup.orderOf_dvd_natCard (center Y) hc)
  · intro m r _ _ h
    rcases h with h | h
    · exact absurd h (hC4 (Y ⧸ Open.fusionZStar Y) n (2 * m) r hn hmQ).1
    · exact absurd h (hC4 (Y ⧸ Open.fusionZStar Y) n (2 * m) r hn hmQ).2

theorem false_of_component (hH : Harris82Theorem1KProper) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog G) (hcat : ¬ Blueprint.Catalog G) {ν : G}
    (hν : orderOf ν = 2) {K : Subgroup G} (hKc : IsComponentIn K (centralizer {ν}))
    (hνK : ν ∈ K) (hM : IsMTypeSchur 3 ↥K) : False := by
  exact hH G hnab hK hcat ν hν K
    (isTwoComponentIn_of_isComponentIn hKc ⟨ν, hνK, hν⟩) hνK 3 Nat.prime_three (by norm_num) hM

theorem false_of_pOmegaPlus_component (hH : Harris82Theorem1KProper)
    (hC4 : POmegaPlusNotLinUnit) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog G)
    (hcat : ¬ Blueprint.Catalog G) {ν : G} (hν : orderOf ν = 2) {K : Subgroup G}
    (hKc : IsComponentIn K (centralizer {ν})) (hνK : ν ∈ K) {n : ℕ} (hn : n = 4 ∨ n = 6)
    (hm : Blueprint.LieModel (↥K ⧸ center ↥K) .POmegaPlus n 3 1) : False := by
  have hc : (⟨ν, hνK⟩ : ↥K) ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKc.1 y.2)
  have hc2 : orderOf (⟨ν, hνK⟩ : ↥K) = 2 := (Subgroup.orderOf_mk ν hνK).trans hν
  exact false_of_component hH hnab hK hcat hν hKc hνK
    (isMTypeSchur_of_pOmegaPlus hC4 hKc.2.1 hc hc2 hn hm)

end CFSG.OddStandard.HigherRank.F3
