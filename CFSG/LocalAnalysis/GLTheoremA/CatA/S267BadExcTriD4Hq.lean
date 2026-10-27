module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcG2Hq
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTriD4Rank
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3TriD4Short

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley (graphFixedRootGroup orbitField)


variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem false_of_badExcLie_trialityD4_hq {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hS : S.Normal)
    (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B) (hB4 : p ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {Q : TauCeti.PrimePower} (hQ2 : Q.p ≠ 2)
    (hQp : Q.p ≠ p) (hv : (TauCeti.LieTypeIndex.trialityD4 Q).Valid)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 Q, hv⟩).Group)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank Q.p K' ≤ CFSG.Open.pRank p B) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, σ, hK, hσ, ⟨Θ, hΘ⟩, ⟨ec⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 Q hv
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    have : Finite (Module.End K (RootModule TwistTag.D4.tag K)) := Module.finite_of_finite K
    infer_instance
  have hK3 : Nat.card K = Q.p ^ (3 * Q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  have hf3 : 1 ≤ 3 * Q.exponent := by have := Q.exponent_pos; omega
  haveI : CharP K Q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Q.prime_p hf3 hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K Q.p]; exact hQ2
  have hσ3 : σ ^ 3 = 1 := CFSG.LocalAnalysis.GLTheoremA.S267.P3.triD4_sigma_cube hK hσ
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective
  have hX : ∀ F : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      IsElemAbelian p F → Nat.card F ≤ p ^ 2 :=
    CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv ec
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_cat_trialityD4 Q hv hp hp5 (Ne.symm hQp))
  haveI : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hrk := pRank_mulAut_le_of_cyclic hZ hp hX Θ hΘ
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr (e.trans ec).symm)] at hrk
  have hBle := card_le_pow_succ_of_pRank_mulAut_le hp hS hperf hB hBC hrk
  have hBr : CFSG.Open.pRank p B ≤ 4 :=
    CFSG.SectionRank.pRank_le hp.one_lt fun _ hEB _ => (Subgroup.card_le_of_le hEB).trans hBle
  obtain ⟨A, hA, hAc⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.exists_elemAbelian_aut_cube hp hS hperf hB hB4 hBC
  have hA' : IsElemAbelian p (A.map (MulAut.congr (e.trans ec)).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hA _
  have hA'c : p ^ (2 + 1) ≤ Nat.card (A.map (MulAut.congr (e.trans ec)).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.congr (e.trans ec)).injective]
    exact hAc
  have hdvd := dvd_card_of_elemAbelian_mulAut hZ hp hX Θ hΘ hA' hA'c
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality Q.prime_p
      hf3 hK3
  rw [hcard] at hdvd
  have hm : 5 ≤ 3 * Q.exponent := hp5.trans (Nat.le_of_dvd (by omega) hdvd)
  have hinj := CFSG.LieType.Chevalley.orbitRankOneHom_injective_D4 hσ3
    CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4Outer
  have hle := CFSG.LieType.Chevalley.range_orbitRankOneHom_le (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom) CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4Outer
  have eJ : Matrix.SpecialLinearGroup (Fin 2) (orbitField TwistTag.D4 K σ.toRingHom
      CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4Outer) ≃*
      CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :=
    (MonoidHom.ofInjective hinj).trans (Subgroup.subgroupOfEquivOfLe hle).symm
  have hL : Nat.card (orbitField TwistTag.D4 K σ.toRingHom
      CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4Outer) = Q.p ^ (3 * Q.exponent) := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv
      (CFSG.LocalAnalysis.GLTheoremA.S267.P3.triD4_mem_orbitField hσ3)), hK3]
  obtain ⟨t, -, ht1, ht2, htc, -⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.P3.triD4_exists_short_involution hK2 hσ3
  refine false_of_hq_of_section Q.prime_p hBr hHq (e.trans ec)
    (CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.isPGroup_two_zpowers_of_sq ht2)
    (CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.zpowers_ne_bot_of_ne_one ht1) (fun m hm => ?_)
    (five_le_pRank_of_mulEquiv_sl2 Q.prime_p hQ2 hm hL eJ)
  refine CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.mem_normalizer_of_forall_comm fun k hk => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  exact (Commute.zpow_right (htc m hm) n).eq

theorem false_of_badExcCore_trialityD4 {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hqp : q ≠ p) (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B)
    (hB4 : p ^ 4 ≤ Nat.card B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    (hp3B : ¬ (p = 3 ∧ Nat.card B = 3 ^ 4)) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.trialityD4 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 Q, hv⟩).Group)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) : False := by
  rw [TauCeti.LieTypeIndex.characteristic_trialityD4] at hchar
  subst hchar
  rcases eq_or_ne p 3 with rfl | hp3
  · exact false_of_badExcLie_trialityD4_three hS hperf hB hB4 hBC (fun h => hp3B ⟨rfl, h⟩) hq2
      hqp hv e
  · exact false_of_badExcLie_trialityD4_hq hp (hp.five_le_of_ne_two_of_ne_three hp2 hp3) hS hperf
      hB hB4 hBC hq2 hqp hv e hHq

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
