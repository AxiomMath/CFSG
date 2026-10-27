module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdCovRed
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.HardMathSupport.Dickson.I271.Support.AmbU4
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.PSp43Centralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem hstd_pSimple_equiv_center {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : CFSG.Open.IsQuasisimple ↥K) (hne : GLAPPrimeCore 3 ↥K ≠ ⊤) :
    Nonempty (PSimple 3 K ≃* (↥K ⧸ Subgroup.center ↥K)) := by
  have hle : GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K :=
    le_center_of_normal_of_isQuasisimple hK inferInstance hne
  have hker : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) : ↥K →* PQuot 3 K).ker ≤
      Subgroup.center ↥K := by
    rw [QuotientGroup.ker_mk']
    exact hle
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hK.1 (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) (QuotientGroup.mk'_surjective _) hker
  exact ⟨e.symm⟩

theorem hstd_ne_top_of_one_lt {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (h : 1 < Nat.card (PSimple 3 K)) : GLAPPrimeCore 3 ↥K ≠ ⊤ := by
  intro htop
  have hsub : Subsingleton (PQuot 3 K) := by
    show Subsingleton (↥K ⧸ GLAPPrimeCore 3 ↥K)
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  have hsub' : Subsingleton (PSimple 3 K) :=
    (QuotientGroup.mk_surjective (s := Subgroup.center (PQuot 3 K))).subsingleton
  have h1 : Nat.card (PSimple 3 K) = 1 := Nat.card_of_subsingleton (1 : PSimple 3 K)
  omega

theorem hstd_card_U42 {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid} (hq : q.card = 2) :
    Nat.card (CFSG.HardMathSupport.Dickson.I271.Amb.U4Group q hv) = 25920 := by
  obtain ⟨eP⟩ := CFSG.LieType.Multipliers.U42.nonempty_mulEquiv_PSp43
    (CFSG.HardMathSupport.Dickson.I271.Amb.u4_lieModel (hv := hv) hq)
  rw [Nat.card_congr eP.toEquiv]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435.card_PSp43

theorem StdCovSchurAt_holds :
    StdCovSchurAt := by
  intro X _ _ K hK hS
  rcases hS with hU | hA
  · obtain ⟨q, hv, hq, ⟨eU⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU4two hU
    have hcard : 1 < Nat.card (PSimple 3 K) := by
      rw [Nat.card_congr eU.toEquiv, hstd_card_U42 (hv := hv) hq]
      norm_num
    obtain ⟨eK⟩ := hstd_pSimple_equiv_center hK (hstd_ne_top_of_one_lt hcard)
    have e : (↥K ⧸ Subgroup.center ↥K) ≃* CFSG.HardMathSupport.Dickson.I271.Amb.U4Group q hv :=
      eK.symm.trans eU
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two
      (CFSG.HardMathSupport.Dickson.I271.Amb.U4Group q hv)
      (CFSG.HardMathSupport.Dickson.I271.Amb.u4_lieModel (hv := hv) hq)
    have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier ⟨hK.1⟩ e
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at hdvd
    exact hdvd.trans (by norm_num)
  · obtain ⟨i, hi, ⟨eA⟩⟩ := hA
    cases i with
    | alternating n h =>
      have hn : n = 6 := hi
      subst hn
      have e6 : PSimple 3 K ≃* alternatingGroup (Fin 6) := eA
      have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
        rw [show (6 : ℕ) = 4 + 2 from rfl, CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin]
        norm_num [Nat.factorial]
      have hcard : 1 < Nat.card (PSimple 3 K) := by
        rw [Nat.card_congr e6.toEquiv, h360]
        norm_num
      obtain ⟨eK⟩ := hstd_pSimple_equiv_center hK (hstd_ne_top_of_one_lt hcard)
      have e : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6) := eK.symm.trans e6
      have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier ⟨hK.1⟩ e
      rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
        (alternatingGroup (Fin 6))).toEquiv,
        (CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six).2] at hdvd
      exact hdvd
    | _ => exact False.elim hi

end CFSG.LocalAnalysis.GLTheoremA

end
