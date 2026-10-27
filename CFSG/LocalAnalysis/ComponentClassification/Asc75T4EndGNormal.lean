module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Main
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4EndGLocal

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix

variable {G : Type} [Group G] [Finite G]

theorem thm4Case1_of_normalIn_chain {Q A B : Subgroup G} (htight : TightlyEmbedded Q)
    (h4 : HasFourGroup (twoPrimeLayerIn Q)) (hKA : NormalIn (twoPrimeLayerIn Q) A)
    (hAB : NormalIn A B) (hB : B.Normal) : Thm4Case1 Q := by
  set K := twoPrimeLayerIn Q
  have hBtop : NormalIn B ⊤ :=
    normalIn_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.mpr hB])
  have hinf : K ⊓ oddCoreIn (⊤ : Subgroup G) = oddCoreIn K := by
    refine le_antisymm (le_oddCoreIn (normalIn_of_le_normalizer inf_le_left ?_)
      ((odd_card_oddCoreIn _).of_dvd_nat (card_dvd_of_le inf_le_right))) ?_
    · exact (le_inf le_normalizer (le_top.trans
        (normalIn_le_normalizer (oddCoreIn_normalIn ⊤)))).trans
        (inf_normalizer_le_normalizer_inf _ _)
    · exact le_inf (oddCoreIn_le K) (((oddCoreIn_le_of_normalIn hKA).trans
        (oddCoreIn_le_of_normalIn hAB)).trans (oddCoreIn_le_of_normalIn hBtop))
  have hKsub' : (K.subgroupOf (⊤ : Subgroup G)).IsSubnormal := by
    have hKG : K ≤ (⊤ : Subgroup G) := le_top
    refine IsSubnormal.step _ (A.subgroupOf ⊤) (subgroupOf_mono ⊤ hKA.1)
      (isSubnormal_subgroupOf_of_normalIn hAB hBtop) ?_
    rw [normal_subgroupOf_iff_le_normalizer (subgroupOf_mono ⊤ hKA.1),
      ← subgroupOf_normalizer_eq hKG]
    exact subgroupOf_mono ⊤ (normalIn_le_normalizer hKA)
  have hKsub : (quotImage ⊤ K).IsSubnormal := isSubnormal_quotImage_of_subgroupOf hKsub'
  have hKlay : CFSG.layer (quotImage ⊤ K) = ⊤ :=
    layer_map_mk_eq_top le_top hinf (isSemisimpleQ_twoPrimeLayerIn Q)
  have hKle : K ≤ twoPrimeLayerIn (⊤ : Subgroup G) := by
    have h := map_subtype_layer_le_layer_of_isSubnormal hKsub
    rw [hKlay, ← MonoidHom.range_eq_map, range_subtype] at h
    intro k hk
    exact mem_twoPrimeLayerIn_iff.mpr ⟨mem_top k, h ⟨⟨k, mem_top k⟩, hk, rfl⟩⟩
  have hEN : CFSG.layer (↥(⊤ : Subgroup G) ⧸ CFSG.Assembly.oddCore ↥(⊤ : Subgroup G)) ≤
      normalizer (quotImage ⊤ K :
        Set (↥(⊤ : Subgroup G) ⧸ CFSG.Assembly.oddCore ↥(⊤ : Subgroup G))) := by
    refine sSup_le fun C hC => ?_
    rcases CFSG.LocalCores.component_subnormal_subgroup hC hKsub with h | h
    · exact h.trans le_normalizer
    · exact (commutator_eq_bot_iff_le_centralizer.mp h).trans (centralizer_le_normalizer _)
  have hOQ : oddCoreIn (⊤ : Subgroup G) ≤ normalizer (Q : Set G) :=
    oddCoreIn_le_normalizer htight (twoPrimeLayerIn_le Q) le_top h4
  have hON : (⊤ : Subgroup G) ≤ normalizer (oddCoreIn (⊤ : Subgroup G) : Set G) :=
    normalIn_le_normalizer (oddCoreIn_normalIn ⊤)
  obtain ⟨E, hEK, hE, hE4⟩ := h4
  have hEne : E ≠ ⊥ := fun h => by rw [h, card_bot] at hE4; norm_num at hE4
  obtain ⟨⟨u, huE⟩, hu1⟩ := ne_bot_iff_exists_ne_one.mp hEne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huK := hEK huE
  have hLQ : twoPrimeLayerIn (⊤ : Subgroup G) ≤ normalizer (Q : Set G) := by
    intro x hx
    obtain ⟨hxt, hxE⟩ := mem_twoPrimeLayerIn_iff.mp hx
    have hxN := hEN hxE
    have hm : QuotientGroup.mk' (CFSG.Assembly.oddCore (⊤ : Subgroup G))
        (⟨x, hxt⟩ * ⟨u, mem_top u⟩ * ⟨x, hxt⟩⁻¹) ∈ quotImage ⊤ K := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hxN _).mp ⟨⟨u, mem_top u⟩, huK, rfl⟩
    have hv : x * u * x⁻¹ ∈ K ⊔ oddCoreIn (⊤ : Subgroup G) := mem_sup_oddCoreIn_of_mk_mem hm
    have hv2 : (x * u * x⁻¹) ^ 2 ^ 1 = 1 := by
      rw [pow_one, conj_pow, hE u huE, mul_one, mul_inv_cancel]
    have hvQ : x * u * x⁻¹ ∈ Q := mem_of_two_element_of_le_sup (twoPrimeLayerIn_le Q)
      (odd_card_oddCoreIn _) (le_top.trans hON) hOQ hv hv2
    have hvQx : x * u * x⁻¹ ∈ rightConjugate Q x⁻¹ := by
      rw [mem_rightConjugate_iff, show x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u by group]
      exact twoPrimeLayerIn_le Q huK
    have hv1 : x * u * x⁻¹ ≠ 1 := by
      intro h
      apply hu1'
      rw [show u = x⁻¹ * (x * u * x⁻¹) * x by group, h]
      group
    have heven : Even (Nat.card (Q ⊓ rightConjugate Q x⁻¹ : Subgroup G)) := by
      have hz : Nat.card (zpowers (x * u * x⁻¹)) = 2 := by
        rw [Nat.card_zpowers, orderOf_eq_prime (by simpa using hv2) hv1]
      exact even_iff_two_dvd.mpr (hz ▸ card_dvd_of_le ((zpowers_le).mpr ⟨hvQ, hvQx⟩))
    exact inv_mem_iff.mp (mem_normalizer_of_even_inf htight heven)
  exact normalIn_of_le_normalizer hKle (hLQ.trans (normalizer_le_normalizer_twoPrimeLayerIn Q))

namespace MainCounterexample

variable {Q : Subgroup G} (hM : MainCounterexample G Q)
include hM

theorem false_of_normal {N : Subgroup G} (hN : N.Normal) (hNt : N ≠ ⊤) (hQN : Q ≤ N) : False := by
  have hcard : Nat.card N < Nat.card G := by
    rw [← card_top (G := G)]
    exact card_lt_of_lt (lt_top_iff_ne_top.mpr hNt)
  have ht : TightlyEmbedded (Q.subgroupOf N) :=
    tightlyEmbedded_subgroupOf hM.tight le_rfl hQN hM.tight.1 inf_le_right
  have hne : twoPrimeLayerIn (Q.subgroupOf N) ≠ oddCoreIn (Q.subgroupOf N) := by
    intro h
    have h1 := congrArg (Subgroup.map N.subtype) h
    rw [twoPrimeLayerIn_subgroupOf_map hQN, oddCoreIn_subgroupOf_map hQN] at h1
    have h2 := odd_card_oddCoreIn Q
    rw [← h1] at h2
    exact Nat.not_even_iff_odd.mpr h2 hM.four.even_card
  rcases hM.ih N hcard (Q.subgroupOf N) ht hne with h1 | h2 | h3
  · apply hM.not_case1
    have h := (normalIn_map_iff N.subtype_injective).mpr h1
    rw [twoPrimeLayerIn_subgroupOf_map hQN, twoPrimeLayerIn_top_map] at h
    exact thm4Case1_of_normalIn_chain hM.tight hM.four h (twoPrimeLayerIn_normalIn N) hN
  · have h : CFSG.Open.pRank 2 (twoPrimeLayerIn (Q.subgroupOf N)) = 1 := h2
    rw [← pRank_map_subtype, twoPrimeLayerIn_subgroupOf_map hQN] at h
    have := hM.four.two_le_pRank
    omega
  · apply hM.not_case3
    obtain ⟨g, -, hg, T, -, hT, hTN, n, hn, φ, hφ, hker⟩ := thm4Case3_subgroupOf hQN h3
    exact ⟨g, hg, T, hT, hTN, n, hn, φ, hφ, hker⟩

omit [Finite G] hM in
theorem le_of_odd_of_index_eq_two {N Y : Subgroup G} (hN : N.Normal) (hidx : N.index = 2)
    (hY : Odd (Nat.card Y)) : Y ≤ N := by
  intro y hy
  have hodd : Odd (orderOf y) := by
    have h := orderOf_dvd_natCard (⟨y, hy⟩ : Y)
    rw [Subgroup.orderOf_mk] at h
    exact hY.of_dvd_nat h
  have h1 : orderOf (QuotientGroup.mk' N y) ∣ orderOf y := orderOf_map_dvd _ _
  have h2 : orderOf (QuotientGroup.mk' N y) ∣ 2 := by
    rw [← hidx, index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk' N y) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · exfalso
      rw [h] at h1
      exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h1)
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem false_of_index_eq_two
    (hE : EndSetting Q) {N : Subgroup G} (hN : N.Normal)
    (hidx : N.index = 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := twoPrimeLayerIn Q with hKdef
  have hNt : N ≠ ⊤ := fun h => by rw [h, index_top] at hidx; norm_num at hidx
  have hON : oddCoreIn Q ≤ N := le_of_odd_of_index_eq_two hN hidx (odd_card_oddCoreIn Q)
  have hKN' : K ≤ normalizer (Q : Set G) := (twoPrimeLayerIn_le Q).trans le_normalizer
  have hKN : K ≤ N := by
    obtain ⟨u, huK, w, hwK, hu, hw, hu1, hw1, huw, huwc⟩ := hM.four.exists_commute
    obtain ⟨e, heK, heN, he, he1⟩ : ∃ e ∈ K, e ∈ N ∧ e ^ 2 = 1 ∧ e ≠ 1 := by
      by_cases huN : u ∈ N
      · exact ⟨u, huK, huN, hu, hu1⟩
      by_cases hwN : w ∈ N
      · exact ⟨w, hwK, hwN, hw, hw1⟩
      refine ⟨u * w, mul_mem huK hwK, (mul_mem_iff_of_index_two hidx).mpr
        ⟨fun h => absurd h huN, fun h => absurd h hwN⟩, ?_, ?_⟩
      · rw [(show Commute u w from huwc).mul_pow, hu, hw, one_mul]
      · intro h
        apply huw
        have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hu)
        rw [← hu', eq_inv_of_mul_eq_one_left h, inv_inv]
    have hsimple := hE.isSimpleGroup_bar
    set L := bar Q K
    set M := bar Q (K ⊓ N)
    have hML : M ≤ L := bar_mono Q inf_le_left
    have hMn : (M.subgroupOf L).Normal := by
      refine (normal_subgroupOf_iff_le_normalizer hML).mpr ?_
      refine bar_le_normalizer ?_ (inf_le_left.trans hKN')
      intro k hk
      exact inf_normalizer_le_normalizer_inf _ _ (mem_inf.mpr ⟨le_normalizer hk,
        by rw [normalizer_eq_top_iff.mpr hN]; exact mem_top k⟩)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf L) with hbot | htop
    · exfalso
      have heM : toBar Q ⟨e, hKN' heK⟩ ∈ M := toBar_mem_bar Q (mem_inf.mpr ⟨heK, heN⟩)
      have : (⟨toBar Q ⟨e, hKN' heK⟩, hML heM⟩ : L) ∈ M.subgroupOf L := heM
      rw [hbot, mem_bot] at this
      have h1 : toBar Q ⟨e, hKN' heK⟩ = 1 := congrArg Subtype.val this
      rw [toBar_eq_one_iff] at h1
      have h1' : e ∈ oddCoreIn Q := h1
      have h2 : orderOf e ∣ Nat.card (oddCoreIn Q) := by
        have := orderOf_dvd_natCard (⟨e, h1'⟩ : oddCoreIn Q)
        rwa [Subgroup.orderOf_mk] at this
      rw [orderOf_eq_prime he he1] at h2
      exact Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn Q) (even_iff_two_dvd.mpr h2)
    · intro k hk
      have hkL : toBar Q ⟨k, hKN' hk⟩ ∈ M := by
        have : (⟨toBar Q ⟨k, hKN' hk⟩, toBar_mem_bar Q hk⟩ : L) ∈ M.subgroupOf L := by
          rw [htop]
          exact mem_top _
        exact this
      obtain ⟨k', hk', hkk'⟩ := (mem_bar_iff Q _ _).mp hkL
      have hO : (k' : G)⁻¹ * k ∈ oddCoreIn Q := by
        have h1 : k'⁻¹ * ⟨k, hKN' hk⟩ ∈ coreIn Q := QuotientGroup.eq.mp hkk'
        exact h1
      have : k = (k' : G) * ((k' : G)⁻¹ * k) := by group
      rw [this]
      exact mul_mem (mem_inf.mp hk').2 (hON hO)
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 Q
  have hRK : R ≤ K := by
    intro r hr
    have hrN : r ∈ normalizer (Q : Set G) := le_normalizer (hR.le hr)
    have hbar : toBar Q ⟨r, hrN⟩ ∈ bar Q K :=
      hE.le_layer_of_isPGroup (bar_mono Q hR.le) (isPGroup_bar hR.isPGroup)
        (toBar_mem_bar Q (h := ⟨r, hrN⟩) hr)
    obtain ⟨k, hk, hkr⟩ := (mem_bar_iff Q _ _).mp hbar
    have hO : (k : G)⁻¹ * r ∈ oddCoreIn Q := by
      have h1 : k⁻¹ * ⟨r, hrN⟩ ∈ coreIn Q := QuotientGroup.eq.mp hkr
      exact h1
    have : r = (k : G) * ((k : G)⁻¹ * r) := by group
    rw [this]
    exact mul_mem hk (oddCoreIn_le_twoPrimeLayerIn Q hO)
  have hQN : Q ≤ N := by
    have hRQN : R ≤ N ⊓ Q := le_inf (hRK.trans hKN) hR.le
    have hdvd : N.relIndex Q ∣ 2 := hidx ▸ N.relIndex_dvd_index_of_normal Q
    have hodd : ¬ 2 ∣ N.relIndex Q := by
      intro h2
      apply (isSylowOf_iff.mp hR).2.2
      rw [← relIndex_mul_relIndex R (N ⊓ Q) Q hRQN inf_le_right, inf_relIndex_right]
      exact h2.mul_left _
    have h1 : N.relIndex Q = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · exact absurd (show 2 ∣ N.relIndex Q by simp [h]) hodd
    exact relIndex_eq_one.mp h1
  exact hM.false_of_normal hN hNt hQN

end MainCounterexample

end CFSG.ComponentClassification.Asc75T4
