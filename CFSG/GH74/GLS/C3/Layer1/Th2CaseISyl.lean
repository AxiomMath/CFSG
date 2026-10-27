module

public import CFSG.GH74.GLS.C3.Layer1.Th2ConnRows
public import CFSG.GH74.GLS.C3.Layer1.Th2Tstar
public import CFSG.GH74.GLS.C3.Layer1.BkIv81Aux
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

@[expose] def B_thm2_terminal_standard : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → IsTerminalPair 2 x K → IsStandardSubgroup K

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_self_of_perfect' {X : Type} [Group X] (C : Subgroup X) (hC : Group.IsPerfect C) :
    ⁅C, C⁆ = C := by
  have h1 : ⁅(⊤ : Subgroup C), (⊤ : Subgroup C)⁆ = ⊤ := by
    rw [← commutator_def]
    exact hC.commutator_eq_top
  have h2 := Subgroup.map_commutator (⊤ : Subgroup C) ⊤ C.subtype
  have h3 : (⊤ : Subgroup C).map C.subtype = C := by
    rw [← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype C
  rw [h1, h3] at h2
  exact h2.symm

theorem commute_of_mem_pPrimeCoreOf [Finite G] {K : Subgroup G} (hK : CFSG.IsQuasisimple ↥K) {o : G}
    (ho : o ∈ pPrimeCoreOf 2 K) {k : G} (hk : k ∈ K) : o * k = k * o := by
  obtain ⟨-, hsimple, a, b, hab⟩ := hK
  obtain ⟨hoK, hoO⟩ := C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.1 ho
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥K)) := by
    have := CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥K)
    exact Nat.coprime_two_left.1 this
  have hsolv : Group.IsSolvable ↥(pPrimeCore 2 ↥K) := CFSG.Milestones.odd_order_solvable hodd
  have hnorm : ((pPrimeCore 2 ↥K).map (QuotientGroup.mk' (center ↥K))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective (center ↥K))
  have hle : pPrimeCore 2 ↥K ≤ center ↥K := by
    have := hnorm
    rcases hsimple.eq_bot_or_eq_top_of_normal ((pPrimeCore 2 ↥K).map (QuotientGroup.mk' (center ↥K))) with h0 | h0
    · intro o' ho'
      have : QuotientGroup.mk' (center ↥K) o' ∈ (pPrimeCore 2 ↥K).map (QuotientGroup.mk' (center ↥K)) := ⟨o', ho', rfl⟩
      rw [h0] at this
      exact (QuotientGroup.eq_one_iff o').1 this
    · exfalso
      have hsur : Function.Surjective ((QuotientGroup.mk' (center ↥K)).comp (pPrimeCore 2 ↥K).subtype) := by
        intro g
        have : g ∈ (pPrimeCore 2 ↥K).map (QuotientGroup.mk' (center ↥K)) := by rw [h0]; trivial
        obtain ⟨o', ho', rfl⟩ := this
        exact ⟨⟨o', ho'⟩, rfl⟩
      have hsolv' : Group.IsSolvable (↥K ⧸ center ↥K) := Group.isSolvable_of_surjective hsur
      have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hsolv'
      exact hab (hcomm a b)
  have := Subgroup.mem_center_iff.1 (hle hoO) ⟨k, hk⟩
  exact congrArg Subtype.val this.symm

theorem commute_of_mem_cSec [Finite G] {K : Subgroup G} (hK : CFSG.IsQuasisimple ↥K) {q : G}
    (hq : q ∈ centralizerSection K (pPrimeCoreOf 2 K)) : ∀ k ∈ K, q * k = k * q := by
  have hperf : ⁅K, K⁆ = K := commutator_self_of_perfect' K hK.1
  set H : Subgroup G := zpowers q with hH
  have hHcs : H ≤ centralizerSection K (pPrimeCoreOf 2 K) := zpowers_le.2 hq
  have h1 : ⁅K, H⁆ ≤ pPrimeCoreOf 2 K := by
    rw [Subgroup.commutator_le]
    intro k hk h hh
    exact (hHcs hh).2.2 k hk
  have hOK : ⁅pPrimeCoreOf 2 K, K⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro o ho k hk
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (commute_of_mem_pPrimeCoreOf hK ho hk)
  have h2 : ⁅⁅K, H⁆, K⁆ = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_mono h1 le_rfl).trans hOK.le)
  have h3 : ⁅⁅H, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm H K]; exact h2
  have h4 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K) (H₂ := K) (H₃ := H) h2 h3
  rw [hperf] at h4
  intro k hk
  have : ⁅k, q⁆ ∈ (⊥ : Subgroup G) :=
    h4 ▸ Subgroup.commutator_mem_commutator hk (Subgroup.mem_zpowers q)
  rw [Subgroup.mem_bot] at this
  exact (commutatorElement_eq_one_iff_mul_comm.1 this).symm

theorem pumpUp_eq_self [Finite G] {u : G} {K : Subgroup G}
    (hKC : K ≤ centralizer ({u} : Set G)) (hK : IsPCompIn 2 (centralizer ({u} : Set G)) K) :
    pumpUp 2 K u = K ∧ IsPCompIn 2 K K := by
  have hKK : IsPCompIn 2 K K := C3.Layer1.Bk.isPCompIn_of_le hK le_rfl hKC
  have hlayerK : pLayerOf 2 (K ⊓ centralizer ({u} : Set G)) = K := by
    rw [inf_eq_left.2 hKC]
    refine le_antisymm (sSup_le fun L hL => hL.1) (le_sSup hKK)
  have hnorm : pLayerOf 2 (centralizer ({u} : Set G)) ≤ normalizer (K : Set G) := by
    refine sSup_le fun L hL => ?_
    by_cases hLK : L = K
    · rw [hLK]; exact Subgroup.le_normalizer
    · exact (Stage1.Thm2.Recip.le_cSec_of_ne hL hK hLK).trans fun c hc => hc.1
  refine ⟨?_, hKK⟩
  unfold pumpUp
  rw [hlayerK]
  refine le_antisymm (iSup₂_le fun g hg => ?_) ?_
  · exact (Th2Tstar.map_conj_eq_of_mem_normalizer (hnorm hg)).le
  · exact le_iSup₂_of_le 1 (one_mem _) (by
      intro k hk
      exact ⟨k, hk, by simp⟩)

end CFSG.GH74.GLS.Th2

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Th2
open scoped commutatorElement

section CaseISyl

variable {G : Type} [Group G] {x y : G} {K T S : Subgroup G}

theorem Th2Std.centerless_and_shape [Finite G] (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem)
    (h102 : B_ivk_10_2) (h : Th2Std x y K T S) :
    CenterlessBar K ∧ RankTwoShape (T ⊓ K) := by
  obtain ⟨hq, hshape⟩ := h102 G hG x y K h.v2ss.isV2Triple.1
  rcases hshape with hL2 | h7 | ⟨hL34', hel, hcard⟩
  · have hPr : ∀ q : ℕ, Odd q → Odd q := fun q hq => hq
    exact ⟨centerlessBar_of_hasL2Model hPr hL2,
      rankTwoShape_sylow_L2 h.sylow_P (TwoThin.isQuasisimple_hat h.comp) hPr hL2⟩
  · exact ⟨centerlessBar_of_A7 h7, rankTwoShape_sylow_A7 h.sylow_P h7⟩
  · exact (hL34 G hG.gen4 x K h.orderOf_x h.comp ⟨hL34', hel, hcard⟩).elim

theorem sylow_Q_centralizer_of_terminal [Finite G] (hG : C3Hyp G) (hL34 : B_gen4_noL34_elem)
    (h102 : B_ivk_10_2) (h : Th2Std x y K T S) (hterm : IsTerminalPair 2 x K)
    (hS : IsStandardSubgroup K) :
    IsSylowOf 2 (T ⊓ CxK x K) (centralizer (K : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcen, hP⟩ := h.centerless_and_shape hG hL34 h102
  have hPQ := h.commDisj hcen
  have hQsyl := h.sylow_Q
  have hQT : T ⊓ CxK x K ≤ T := inf_le_left
  have hCxK : CxK x K ≤ centralizer (K : Set G) := fun c hc =>
    Subgroup.mem_centralizer_iff.2 fun k hk => (commute_of_mem_cSec hS.1 hc.2 k hk).symm
  have hQC : T ⊓ CxK x K ≤ centralizer (K : Set G) := inf_le_right.trans hCxK
  obtain ⟨Qs, hQs, hQQs⟩ : ∃ Qs : Subgroup G, IsSylowOf 2 Qs (centralizer (K : Set G)) ∧
      T ⊓ CxK x K ≤ Qs := by
    have hp : IsPGroup 2 ↥((T ⊓ CxK x K).subgroupOf (centralizer (K : Set G))) :=
      (h.T_pGroup.to_le hQT).comap_subtype
    obtain ⟨S₀, hS₀⟩ := hp.exists_le_sylow
    refine ⟨(S₀ : Subgroup ↥(centralizer (K : Set G))).map (centralizer (K : Set G)).subtype,
      ⟨S₀, rfl⟩, fun q hq => ⟨⟨q, hQC hq⟩, hS₀ ?_, rfl⟩⟩
    rw [Subgroup.mem_subgroupOf]; exact hq
  have hQs2 : IsPGroup 2 ↥Qs := hQs.isPGroup
  have hCK_cs : centralizer (K : Set G) ≤ centralizerSection K (pPrimeCoreOf 2 K) := fun c hc =>
    C3.Layer1.Back.mem_centralizerSection_of_centralizes
      (fun k hk => (Subgroup.mem_centralizer_iff.1 hc k hk).symm) (TwoThin.pPrimeCoreOf_le K)
  have hxQ : x ∈ T ⊓ CxK x K := ⟨h.x_mem_T, h.x_mem_CxK⟩
  have hxQs : x ∈ Qs := hQQs hxQ
  have hW : Qs ⊓ centralizer ({x} : Set G) = T ⊓ CxK x K :=
    hQsyl.eq_of_le (fun q hq => ⟨hQQs hq, h.T_le_C hq.1⟩)
      (fun c hc => ⟨hc.2, hCK_cs (hQs.le hc.1)⟩) hQs2.to_inf_left
  have hQsne : Qs ≠ ⊥ := by
    intro h0
    have : x ∈ (⊥ : Subgroup G) := h0 ▸ hxQs
    rw [Subgroup.mem_bot] at this
    have := h.orderOf_x
    simp_all
  obtain ⟨u, huQs, hu2, huc⟩ := exists_central_involution hQs2 hQsne
  have hux : u ∈ T ⊓ CxK x K := by
    rw [← hW]
    exact ⟨huQs, mem_centralizer_singleton_iff.2 (huc x hxQs)⟩
  have huK : u ∈ centralizer (K : Set G) := hQs.le huQs
  have hKcomp := hterm.2.2.2 u hu2 huK
  have hKC : K ≤ centralizer ({u} : Set G) := hKcomp.1
  have hK2 : IsPCompIn 2 (centralizer ({u} : Set G)) K := by
    refine ⟨hKC, CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2
      hKcomp.2 fun hle => ?_⟩
    have h1 : Nat.card ↥(K.subgroupOf (centralizer ({u} : Set G))) ∣
        Nat.card ↥(pPrimeCore 2 ↥(centralizer ({u} : Set G))) := Subgroup.card_dvd_of_le hle
    have h2 : Nat.card ↥(K.subgroupOf (centralizer ({u} : Set G))) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv
    rw [h2] at h1
    have h3 := Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
    have h4 := Nat.Coprime.eq_one_of_dvd h3 hterm.2.2.1
    omega
  obtain ⟨hpumpK, hKK⟩ := pumpUp_eq_self hKC hK2
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  have huQ : u ∈ T ⊓ CxK x K := hux
  have hrank : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) := by
    have hzel : CFSG.IsElementaryAbelian 2 ↥(zpowers u) := by
      have : u ^ 2 = 1 := by rw [pow_two]; exact mul_self_eq_one_of_orderOf_eq_two hu2
      exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one this
    have hzQ : zpowers u ≤ T ⊓ CxK x K := zpowers_le.2 huQ
    have hr1 : pRank 2 ↥(zpowers u) = 1 := by
      have hc : Nat.card ↥(zpowers u) = 2 := by rw [Nat.card_zpowers]; exact hu2
      have h2 := C3.Layer1.Back.card_eq_two_pow_pRank hzel
      rw [hc] at h2
      have : (2 : ℕ) ^ 1 = 2 ^ pRank 2 ↥(zpowers u) := by simpa using h2
      exact (Nat.pow_right_injective le_rfl this).symm
    have hsup := hPQ.pRank_sup hU.2.1 hzel hU.1 hzQ
    have hle : U ⊔ zpowers u ≤ centralizer ({u} : Set G) := by
      refine sup_le (fun g hg => ?_) (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
      exact mem_centralizer_singleton_iff.2 (hPQ.comm g (hU.1 hg) u huQ)
    have := C3.Layer1.Back.pRank_mono' hle
    rw [hsup, pRank_of_isFourSub hU, hr1] at this
    omega
  have hILo_u : IsILo 2 u K := ⟨hu2, by simpa [oBound] using hrank, hK2⟩
  have hterm' : IsPTerminal 2 x K := h.v2ss.isV2Triple.2.1
  have hpump : PumpUpLT 2 x K u K :=
    ⟨hterm'.1, hILo_u, h.T_le_C huQ.1, huQ.2.2, by rw [hpumpK]; exact hKK⟩
  have hsyl_u := hterm'.2.2 (T ⊓ CxK x K) hQsyl u K hpump huQ
    (fun q hq => huc q (hQQs hq))
  have hQsle : Qs ≤ centralizer ({u} : Set G) ⊓ centralizerSection K (pPrimeCoreOf 2 K) :=
    le_inf (fun c hc => mem_centralizer_singleton_iff.2 (huc c hc).symm) (fun c hc => hCK_cs (hQs.le hc))
  have hEq : Qs = T ⊓ CxK x K := hsyl_u.eq_of_le hQQs hQsle hQs2
  rw [hEq] at hQs
  exact hQs

end CaseISyl

theorem b_thm2_caseI_of (hstd : B_thm2_terminal_standard) (h102 : B_ivk_10_2)
    (hL34 : B_gen4_noL34_elem) : B_thm2_caseI := by
  intro G _ _ hG x y K T S h hterm
  have hS := hstd G hG x y K T S h hterm
  exact ⟨hS, sylow_Q_centralizer_of_terminal hG hL34 h102 h hterm hS⟩

end CFSG.GH74.GLS
