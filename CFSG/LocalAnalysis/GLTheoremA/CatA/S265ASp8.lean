module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResSchur
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ABlk
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BActS
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ARank
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp8Cen
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASpAct
import CFSG.LocalAnalysis.GLTheoremA.CatB.KFactsSp
import CFSG.LocalAnalysis.GLTheoremA.PComp
import CFSG.Open.StatedAPI
public import CFSG.LargeExtraspecial.S4CEA6Basic
public import CFSG.LargeExtraspecial.S4CESmallThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015U6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnAPI
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutQuot
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpRank
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.Milestones.ASVolI.F48.Core
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
import Certificates.Certificate8007
import Certificates.Certificate8008

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open CFSG.RankThree.Classical (spEnd spLin spLin_injective)

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem catalogIs_isSp8two_of_tySp8 {G : Type} [Group G] (h : catalogIs G tySp8) :
    catalogIs G S9.isSp8two := by
  obtain ⟨i, hi, he⟩ := h
  exact ⟨i, hi, he⟩

private theorem isSimpleGroup_of_tySp8 {G : Type} [Group G] (h : catalogIs G tySp8) :
    IsSimpleGroup G := by
  obtain ⟨e⟩ := HSubT.sp8_model (catalogIs_isSp8two_of_tySp8 h)
  haveI : IsSimpleGroup (StatedProj (StatedSp 4 (ZMod 2))) :=
    CFSG.LieType.SeitzGeneration.isSimpleGroup_statedProj_statedSp_of_two_le (by norm_num)
      fun h4 => absurd h4.1 (by norm_num)
  have hsc : (StatedScalars (Fin 4 ⊕ Fin 4) (ZMod 2)).subgroupOf (StatedSp 4 (ZMod 2)) = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot, Subgroup.bot_subgroupOf]
  exact (e.trans ((QuotientGroup.quotientMulEquivOfEq hsc).trans
    QuotientGroup.quotientBot).symm).isSimpleGroup

theorem false_of_sp8_big {X J B D : Subgroup Ω} (hN : NLAct 3 X J B D) (hB : IsElemAbelian 3 B)
    (hcat : catalogIs (PSimple 3 J) tySp8) (h27 : 27 * Nat.card D ≤ Nat.card B) : False := by
  obtain ⟨e⟩ := HSubT.sp8_model (catalogIs_isSp8two_of_tySp8 hcat)
  obtain ⟨Ab, hAb, hcard, hL⟩ := exists_spImage (by norm_num) e hN hB
  have hle : 27 ≤ Nat.card Ab :=
    Nat.le_of_mul_le_mul_right (by rw [hcard]; exact h27) Nat.card_pos
  have hAb27 : 27 ∣ Nat.card Ab := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := hAb.isPGroup.exists_card_eq
    rw [hk] at hle ⊢
    have hk3 : 3 ≤ k := by
      by_contra hk3
      have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 27 = 3 ^ 3 := by norm_num
      _ ∣ 3 ^ k := pow_dvd_pow 3 hk3
  let φ : StatedSp 4 (ZMod 2) →* ((Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).toMonoidHom.comp
      (spLin 4 (ZMod 2))
  have hφ : Function.Injective φ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).injective.comp spLin_injective
  haveI : Finite ↥(Ab.map φ) := Finite.of_equiv _ (Subgroup.equivMapOfInjective Ab φ hφ).toEquiv
  letI : Fintype ↥(Ab.map φ) := Fintype.ofFinite _
  have hV : Module.finrank (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  refine false_of_nOut_const (fun D : Hyperplane (Ab.map φ) 3 => D.1)
    (fun D => Module.finrank (ZMod 2) ↥(blockSpace (Ab.map φ) D.1)) (fun D => D.2) (c := 2)
    (by norm_num) (fun a ha => ?_) ?_
  · obtain ⟨s, hs, hsa⟩ := Subgroup.mem_map.1 a.2
    have hs1 : s ≠ 1 := by
      rintro rfl
      exact ha (Subtype.ext (by rw [← hsa, map_one]; rfl))
    have hfix : fixedByEnd (a : (Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) =
        LinearMap.ker (spEnd s - 1) := by
      ext v
      rw [mem_fixedByEnd, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
        sub_eq_zero, ← hsa]
      exact Iff.rfl
    have h := finrank_eq_fixedByEnd_add_nOut (Ab.map φ) Nat.prime_three (by decide)
      (hAb.map φ) a
    rw [hfix, finrank_ker_eq_two_of_layer_eq_bot (hAb.2 s hs) hs1 (hL s hs hs1), hV] at h
    omega
  · rw [← Nat.card_eq_fintype_card, Subgroup.card_map_of_injective hφ]
    exact hAb27

section Schur


private theorem false_of_nlAct_sp8 {X J B D : Subgroup Ω} (hN : NLAct 3 X J B D)
    (hB : IsElemAbelian 3 B) (hDJ : D ≤ Subgroup.centralizer (J : Set Ω))
    (hcat : catalogIs (PSimple 3 J) tySp8) (hrank : 3 ^ GLATwoLocalRank 3 Ω ≤ Nat.card B) :
    False := by
  have hcat' := catalogIs_isSp8two_of_tySp8 hcat
  have hZ : Subgroup.center (PQuot 3 J) = ⊥ := HSubT.schurSp8_holds (PQuot 3 J)
    (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hN.comp) hcat'
  obtain ⟨e⟩ := HSubT.sp8_model hcat'
  obtain ⟨E, U, hE, hEc, hU2, hU1, hEU⟩ := CatB.KFacts.kProfile_sp82.e27
  have h := card_mul_card_le_rank hZ (hB.mono hN.le) hDJ (hE.map e.symm.toMonoidHom)
    (hU2.map e.symm.toMonoidHom)
    ((Subgroup.map_eq_bot_iff_of_injective U e.symm.injective).not.2 hU1)
    ((Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map _))
  rw [Subgroup.card_map_of_injective e.symm.injective, hEc] at h
  exact false_of_sp8_big hN hB hcat (calc 27 * Nat.card D = 3 ^ 3 * Nat.card D := by norm_num
    _ ≤ Nat.card B := h.trans hrank)

theorem qsConcl_of_sp8 {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K)
    (hcat : catalogIs (PSimple 3 K) tySp8) : QSConcl 3 S B D K := by
  exfalso
  obtain ⟨-, -, -, -, -, -, hDK⟩ := h.cfg.std
  have hpK : 3 ∣ Nat.card ↥K := by
    obtain ⟨e⟩ := HSubT.sp8_model (catalogIs_isSp8two_of_tySp8 hcat)
    have h3 : 3 ∣ Nat.card (PSimple 3 K) := by
      rw [Nat.card_congr e.toEquiv]
      exact Nat.dvd_of_factorization_pos (by rw [CatB.KFacts.kProfile_sp82.card3]; norm_num)
    exact h3.trans ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _))
  exact false_of_nlAct_sp8 (h.nlAct hpK) h.cfg.elem (fun d hd => (hDK.le hd).2) hcat h.cfg.rank

theorem quConcl_of_sp8 {S B T : Subgroup Ω} {x b : Ω} (h : QUNL 3 S B T x b)
    (hcat : catalogIs (PSimple 3 (Ipart 3 S b)) tySp8) : QUConcl 3 S B x b := by
  exfalso
  have hN := h.nlAct_of_simple (isSimpleGroup_of_tySp8 hcat)
  have hDJ : Dgrp b x ≤ Subgroup.centralizer ((Ipart 3 S b : Subgroup Ω) : Set Ω) := by
    refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨?_,
      Set.singleton_subset_iff.2 (Subgroup.mem_centralizer_iff.2 fun y _ => h.cfg.xcen y)⟩)
    exact Subgroup.mem_centralizer_iff.2 fun y hy =>
      (Subgroup.mem_centralizer_iff.1 (hN.comp.1 hy).2 b (Set.mem_singleton b)).symm
  exact false_of_nlAct_sp8 hN h.cfg.elem hDJ hcat h.cfg.rank

end Schur

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
