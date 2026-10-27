module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248FactsM
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Glue3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Glue4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Glue5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Glue6
public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs6364

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement Pointwise

private theorem center_eq_bot_of_perfect {S : Type} [Group S] [IsSimpleGroup S]
    (hperf : commutator S = ⊤) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    have hc : commutator S = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top,
        Subgroup.centralizer_univ, h]
    exact absurd (hc.symm.trans hperf) bot_ne_top

theorem i248_of_factsM (hI : GL83.I_7_13_1) (hR1 : RankOneFact) (hC : CoreFact) (hL : L227FactM)
    (G : Type) [Group G] [Finite G] (p : ℕ) : CFSG.LocalAnalysis.GLTheoremA.I248At G p := by
  intro hp hp2 q hq hq2 hqp X K Q hX hK hchev hA hQK hQ hcardQ
  have hp2' : 2 ≤ p := hp.two_le
  by_cases hU : IsU3Case p q K
  · exact Or.inr hU
  refine Or.inl ?_
  haveI : Fact q.Prime := ⟨hq⟩
  have hKX : K ≤ X := hK.1
  have hKbar : CFSG.Open.IsQuasisimple (PQuot p K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hK
  have hKperf : commutator ↥K = ⊤ :=
    commutator_eq_top_of_commutator_eq K (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hK)
  have hKlayer : GLAPLayer p K = K := glaPLayer_eq_self_of_component hp hK
  have hKG : CFSG.Open.IsKGroup ↥K := isKGroup_subgroup X K hKX hX
  haveI : IsSimpleGroup (PSimple p K) := hKbar.2
  obtain ⟨A, hAab, hAcard⟩ := hA
  obtain ⟨AS, hASab, hAScard⟩ :=
    exists_elemAbelian_mulAut_of_perfect hKbar.1 (MulEquiv.refl (PSimple p K)) A hAab
  have hAS3 : p ^ 3 ≤ Nat.card AS := by rw [hAScard]; exact hAcard
  have hnotR1 : ¬ CatRankOneGroup q (PSimple p K) := by
    intro h1
    exact hU (hR1 p q hp hp2 hq hq2 hqp (PSimple p K) hchev h1 ⟨AS, hASab, hAS3⟩)
  set W : Subgroup ↥K := W227 p K with hWdef
  set N : Subgroup ↥K := CFSG.Open.GLAPPrimeCore p ↥K with hNdef
  have hWN : W ≤ N := Subgroup.commutator_le_left N ⊤
  have hcommNW : ∀ n ∈ N, ∀ k : ↥K, ⁅n, k⁆ ∈ W := fun n hn k =>
    Subgroup.commutator_mem_commutator hn (Subgroup.mem_top k)
  set N' : Subgroup (↥K ⧸ W) := N.map (QuotientGroup.mk' W) with hN'def
  have hN'central : N' ≤ Subgroup.center (↥K ⧸ W) := map_mk_le_center W N hcommNW
  obtain ⟨eQ⟩ := quotient_quotient_map_equiv W N hWN
  have hHperf : commutator (↥K ⧸ W) = ⊤ :=
    commutator_eq_top_of_surjective _ (QuotientGroup.mk'_surjective W) hKperf
  obtain ⟨hHQS, ⟨eH⟩⟩ := isQuasisimple_of_central_quotient N' hN'central hHperf eQ hKbar
  have hHchev : IsChevSimple q ((↥K ⧸ W) ⧸ Subgroup.center (↥K ⧸ W)) :=
    isChevSimple_of_mulEquiv eH q hchev
  have hHnotR1 : ¬ CatRankOneGroup q ((↥K ⧸ W) ⧸ Subgroup.center (↥K ⧸ W)) := fun h =>
    hnotR1 (catRankOneGroup_of_mulEquiv eH.symm q h)
  have hHnotU3 : ¬ IsU3Shape p q ((↥K ⧸ W) ⧸ Subgroup.center (↥K ⧸ W)) := fun h =>
    hU (isU3Shape_of_mulEquiv eH.symm p q h)
  obtain ⟨AH, hAHab, hAHcard⟩ := exists_elemAbelian_mulAut_of_mulEquiv eH.symm AS hASab
  set Q' : Subgroup ↥K := Q.subgroupOf K with hQ'def
  have hQ'card : Nat.card Q' = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv
  have hQ'pg : IsPGroup q Q' := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
    exact IsPGroup.iff_card.mpr ⟨n, by rw [hQ'card, hn]⟩
  have hQ'card' : Nat.card Q' = q ^ (Nat.card ↥K).factorization q := by
    rw [hQ'card, hcardQ]
  obtain ⟨hQHpg, hQHcard⟩ := sylow_map_quotient hq W Q' hQ'pg hQ'card'
  obtain ⟨hrankH, hgenH⟩ := hC p q hp hp2 hq hq2 hqp (↥K ⧸ W) hHQS hHchev hHnotR1
    ⟨AH, hAHab, by rw [hAHcard]; exact hAS3⟩ hHnotU3 (Q'.map (QuotientGroup.mk' W)) hQHpg hQHcard
  obtain ⟨eM⟩ := quotient_comap_center_equiv (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore p ↥K))
    (QuotientGroup.mk'_surjective _) (Subgroup.center (PQuot p K))
  have hSimpleM : IsSimpleGroup (↥K ⧸ M227 p K) := eM.isSimpleGroup
  have hpS2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (PSimple p K)) := by
    by_contra hlt
    have hle1 : CFSG.Open.pRank p (⊤ : Subgroup (PSimple p K)) ≤ 1 := by omega
    have hperfS : commutator (PSimple p K) = ⊤ :=
      commutator_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _) hKbar.1
    have hnoncomm := exists_noncomm_of_perfect hperfS
    have hcat : CFSG.Open.IsCatalogGroup (PSimple p K) := by
      rcases hchev with h | h
      · obtain ⟨i, -, hi⟩ := h
        exact ⟨i, hi⟩
      · obtain ⟨i, -, hi⟩ := h
        exact ⟨i, hi⟩
    have hmul := (hI p hp hp2 (PSimple p K) hKbar.2 hnoncomm hcat hle1).2
    have h3 := three_le_pRank_of_card hp hASab hAS3
    omega
  have hpM : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥K ⧸ M227 p K)) :=
    hpS2.trans_eq (pRank_eq_of_mulEquiv eM p hp2').symm
  have hMperf : commutator (↥K ⧸ M227 p K) = ⊤ :=
    commutator_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _) hKperf
  have hZM : Subgroup.center (↥K ⧸ M227 p K) = ⊥ := center_eq_bot_of_perfect hMperf
  let eZ : (↥K ⧸ M227 p K) ⧸ Subgroup.center (↥K ⧸ M227 p K) ≃* (↥K ⧸ M227 p K) :=
    (QuotientGroup.quotientMulEquivOfEq hZM).trans QuotientGroup.quotientBot
  have hMQS : CFSG.Open.IsQuasisimple (↥K ⧸ M227 p K) := ⟨hMperf, eZ.isSimpleGroup⟩
  let eMZ : (↥K ⧸ M227 p K) ⧸ Subgroup.center (↥K ⧸ M227 p K) ≃* PSimple p K := eZ.trans eM
  have hMchev : IsChevSimple q ((↥K ⧸ M227 p K) ⧸ Subgroup.center (↥K ⧸ M227 p K)) :=
    isChevSimple_of_mulEquiv eMZ q hchev
  have hMnotR1 : ¬ CatRankOneGroup q ((↥K ⧸ M227 p K) ⧸ Subgroup.center (↥K ⧸ M227 p K)) :=
    fun h => hnotR1 (catRankOneGroup_of_mulEquiv eMZ.symm q h)
  have hMnotU3 : ¬ IsU3Shape p q ((↥K ⧸ M227 p K) ⧸ Subgroup.center (↥K ⧸ M227 p K)) :=
    fun h => hU (isU3Shape_of_mulEquiv eMZ.symm p q h)
  obtain ⟨AM, hAMab, hAMcard⟩ := exists_elemAbelian_mulAut_of_mulEquiv eMZ.symm AS hASab
  obtain ⟨hQMpg, hQMcard⟩ := sylow_map_quotient hq (M227 p K) Q' hQ'pg hQ'card'
  obtain ⟨hrankM, -⟩ := hC p q hp hp2 hq hq2 hqp (↥K ⧸ M227 p K) hMQS hMchev hMnotR1
    ⟨AM, hAMab, by rw [hAMcard]; exact hAS3⟩ hMnotU3 (Q'.map (QuotientGroup.mk' (M227 p K)))
    hQMpg hQMcard
  have hQHgen : 4 ≤ CFSG.Open.pRank q ((Q.subgroupOf K).map (QuotientGroup.mk' (W227 p K))) :=
    hrankH
  have hcoreK := hL p q hp hp2 hq hq2 hqp G K Q hKG hKlayer hKbar hSimpleM hpM hQK hQ hcardQ hQHgen
    hrankM hgenH
  refine ⟨?_, hcoreK.symm⟩
  by_contra hlt
  rw [not_le] at hlt
  have hbot : CFSG.HardMathSupport.Solomon.Coordinator.coreIn q 3 Q K ≤ ⊥ := by
    unfold CFSG.HardMathSupport.Solomon.Coordinator.coreIn
    refine iSup_le fun Q'' => iSup_le fun hQ'' => ?_
    exact absurd hQ''.2 (not_le.mpr (lt_of_le_of_lt (pRank_mono hq.two_le hQ''.1) hlt))
  rw [hcoreK] at hbot
  have hsubK : Subsingleton ↥K :=
    ⟨fun a b => Subtype.ext
      (by rw [Subgroup.mem_bot.mp (hbot a.2), Subgroup.mem_bot.mp (hbot b.2)])⟩
  have hφ : Function.Surjective
      ((QuotientGroup.mk' (Subgroup.center (PQuot p K))).comp
        (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore p ↥K))) := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨x, rfl⟩
  exact not_subsingleton (PSimple p K) (Function.Surjective.subsingleton hφ)

end CFSG.LocalAnalysis.GLTheoremA.H248
