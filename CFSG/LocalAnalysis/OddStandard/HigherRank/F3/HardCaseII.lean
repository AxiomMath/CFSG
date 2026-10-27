module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Basic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardCentral
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardComp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardF4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardKnown
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalInvolution.Q3.Step
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieHalf
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporMult
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW
public import Certificates.Certificate10025
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.ComponentClassification.HarrisLit
open CFSG.ASVolI.ChIJK (IsComponentIn)

theorem isMTypeSchur_of_caseII (hKR : T1.KnownRowThree) (hC3 : LinUnitInvolutionComponents)
    (hC4 : POmegaPlusNotLinUnit) {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    (hcat : Blueprint.Catalog (Y ⧸ center Y)) {c : Y} (hc : c ∈ center Y) (hc2 : orderOf c = 2)
    {z : Y} (hz : orderOf z = 2) (hzc : z ∉ center Y) {L : Subgroup Y}
    (hL : IsComponentIn L (centralizer {z})) (hzL : z ∈ L) {n : ℕ} (hn : n = 4 ∨ n = 6)
    (hm : Blueprint.LieModel (↥L ⧸ center ↥L) .POmegaPlus n 3 1) : IsMTypeSchur 3 Y := by
  have hY2 : IsTwoQuasisimple Y := isTwoQuasisimple_of_involution hY hc2
  have hZY : Open.fusionZStar Y = center Y :=
    fusionZStar_eq_center_of_involution hY hc2
  have hcat' : Blueprint.Catalog (Y ⧸ Open.fusionZStar Y) :=
    SectionRank.catalog_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZY) hcat
  have hL2 : IsTwoComponentIn L (centralizer {z}) :=
    isTwoComponentIn_of_isComponentIn hL ⟨z, hzL, hz⟩
  have hZL : Open.fusionZStar ↥L = center ↥L :=
    fusionZStar_eq_center_of_involution hL.2.1 ((Subgroup.orderOf_mk z hzL).trans hz)
  have hmI : Blueprint.LieModel (↥L ⧸ Open.fusionZStar ↥L) .POmegaPlus n 3 1 :=
    Blueprint.LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZL.symm) hm
  have hI : T1.InductionType 3 ↥L := Or.inr ⟨rfl, Or.inl ⟨.POmegaPlus, n, hmI⟩⟩
  have hKRY := knownRowThree_of_isTwoQuasisimple hKR hY2 hcat' hz hL2 hzL hI
  have hc' : ∃ c' ∈ center (Y ⧸ pPrimeCore 2 Y), c' ≠ 1 := by
    refine ⟨(QuotientGroup.mk' (pPrimeCore 2 Y)) c, ?_, ?_⟩
    · exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective (pPrimeCore 2 Y))
        ⟨c, hc, rfl⟩
    · intro h1
      have hcN : c ∈ pPrimeCore 2 Y := (QuotientGroup.eq_one_iff c).mp h1
      have hdvd := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 Y) hcN
      rw [hc2] at hdvd
      exact absurd hdvd (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)
  have hF : IsSimpleChevalleyOver 3 (Y ⧸ Open.fusionZStar Y) :=
    T23.lieModel_of_theorem1 hY2 hc' hKRY
  have hG : Even (Nat.card ↥(Open.fusionZStar Y)) := by
    rw [hZY]
    exact even_iff_two_dvd.mpr (by
      rw [← hc2]
      exact Subgroup.orderOf_dvd_natCard (center Y) hc)
  refine Or.inl ⟨hY2, hF, hG, ?_⟩
  intro m r _ _ hPS
  exfalso
  haveI : IsSimpleGroup (Y ⧸ center Y) := hY.2.1
  have hPS' : Blueprint.LieModel (Y ⧸ center Y) .PSL (2 * m) 3 r ∨
      Blueprint.LieModel (Y ⧸ center Y) .PSU (2 * m) 3 r := by
    rcases hPS with h | h
    · exact Or.inl (Blueprint.LieModel.of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq hZY) h)
    · exact Or.inr (Blueprint.LieModel.of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq hZY) h)
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  have hπz : orderOf ((QuotientGroup.mk' (center Y)) z) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, hz2, map_one]
    · intro h1
      exact hzc ((QuotientGroup.eq_one_iff z).mp h1)
  obtain ⟨hLbar, ⟨eL⟩⟩ := isComponentIn_map_quotient_center (v := z) hY hL
  obtain ⟨k, s, hks⟩ := hC3 (Y ⧸ center Y) 3 (2 * m) r Nat.prime_three (by norm_num)
    hPS' (QuotientGroup.mk z) hπz (L.map (QuotientGroup.mk' (center Y))) hLbar
  have hks' : Blueprint.LieModel (↥L ⧸ center ↥L) .PSL k 3 s ∨
      Blueprint.LieModel (↥L ⧸ center ↥L) .PSU k 3 s := by
    rcases hks with h | h
    · exact Or.inl (Blueprint.LieModel.of_mulEquiv eL.symm h)
    · exact Or.inr (Blueprint.LieModel.of_mulEquiv eL.symm h)
  rcases hks' with h | h
  · exact (hC4 (↥L ⧸ center ↥L) n k s hn hm).1 h
  · exact (hC4 (↥L ⧸ center ↥L) n k s hn hm).2 h

end CFSG.OddStandard.HigherRank.F3
