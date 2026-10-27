module

public import CFSG.GH74.GLS.C3.Layer1.St1PumpupEq
public import CFSG.GH74.AS16.Standard
public import CFSG.GH74.GLS.C3.Layer1.Th2CaseISyl
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5

public section

namespace CFSG.GH74.GLS.Th2.P72c

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pPrimeCore_eq_bot_of_pPrimeCoreOf_eq_bot {H : Subgroup G} (h : pPrimeCoreOf 2 H = ⊥) :
    pPrimeCore 2 ↥H = ⊥ := by
  unfold pPrimeCoreOf at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp h

theorem isQuasisimple_of_isPCompIn {X K : Subgroup G} (hK : IsPCompIn 2 X K)
    (hO : pPrimeCore 2 ↥X = ⊥) : CFSG.IsQuasisimple ↥K := by
  have hsub : (K.subgroupOf X).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (isPCompIn_two_iff.mp hK).2.1 Subgroup.IsSubnormal.top
  have hOK : pPrimeCore 2 ↥K = ⊥ := pPrimeCore_eq_bot_of_subnormal hK.1 hsub hO
  have e : ↥K ⧸ pPrimeCore 2 ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hOK).trans QuotientGroup.quotientBot
  exact (isQuasisimple_congr e).1 (isQuasisimple_hat hK)

theorem isCompIn_of_isPCompIn {X K : Subgroup G} (hK : IsPCompIn 2 X K)
    (hO : pPrimeCore 2 ↥X = ⊥) : IsCompIn X K := by
  have hsub : (K.subgroupOf X).IsSubnormal :=
    Components.mathlib_subnormal_of_chain (isPCompIn_two_iff.mp hK).2.1 Subgroup.IsSubnormal.top
  exact ⟨hK.1, CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hK.1).symm (isQuasisimple_of_isPCompIn hK hO), hsub⟩

end CFSG.GH74.GLS.Th2.P72c

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P72c

section Std

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem Th2Std.three_le_pRank_centralizer (h : Th2Std x y K T S) (hcen : CenterlessBar K)
    (hP : RankTwoShape (T ⊓ K)) {u : G} (hu : u ∈ T ⊓ CxK x K) (hu2 : orderOf u = 2) :
    3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) := by
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hP
  have hPQ := h.commDisj hcen
  have hzel := Th2.isElementaryAbelian_zpowers_of_orderOf_two hu2
  have hzQ : zpowers u ≤ T ⊓ CxK x K := zpowers_le.2 hu
  have hsup := hPQ.pRank_sup hU.2.1 hzel hU.1 hzQ
  have hle : U ⊔ zpowers u ≤ centralizer ({u} : Set G) := by
    refine sup_le (fun g hg => ?_) (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
    exact mem_centralizer_singleton_iff.2 (hPQ.comm g (hU.1 hg) u hu)
  have := C3.Layer1.Back.pRank_mono' hle
  rw [hsup, pRank_of_isFourSub hU, Th2.pRank_zpowers_of_orderOf_two hu2] at this
  omega

theorem sylow_Q_centralizer_of_comp
    (hR : ∀ u ∈ T ⊓ CxK x K, orderOf u = 2 →
      3 ≤ pRank 2 ↥(centralizer ({u} : Set G)))
    (h : Th2Std x y K T S) (hKq : CFSG.IsQuasisimple ↥K)
    (hev : 2 ∣ Nat.card ↥K)
    (hcomp : ∀ u ∈ T ⊓ CxK x K, orderOf u = 2 → IsCompIn (centralizer ({u} : Set G)) K) :
    IsSylowOf 2 (T ⊓ CxK x K) (centralizer (K : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQsyl := h.sylow_Q
  have hQT : T ⊓ CxK x K ≤ T := inf_le_left
  have hCxK : CxK x K ≤ centralizer (K : Set G) := fun c hc =>
    Subgroup.mem_centralizer_iff.2 fun k hk => (commute_of_mem_cSec hKq hc.2 k hk).symm
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
  obtain ⟨u, huQs, hu2, huc⟩ := Th2.exists_central_involution hQs2 hQsne
  have hux : u ∈ T ⊓ CxK x K := by
    rw [← hW]
    exact ⟨huQs, mem_centralizer_singleton_iff.2 (huc x hxQs)⟩
  have huQ : u ∈ T ⊓ CxK x K := hux
  have huK : u ∈ centralizer (K : Set G) := hQs.le huQs
  have hKcomp := hcomp u hux hu2
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
    have h4 := Nat.Coprime.eq_one_of_dvd h3 hev
    omega
  obtain ⟨hpumpK, hKK⟩ := pumpUp_eq_self hKC hK2
  have hrank : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) := hR u huQ hu2
  have hILo_u : IsILo 2 u K := ⟨hu2, by simpa [oBound] using hrank, hK2⟩
  have hterm' : IsPTerminal 2 x K := h.v2ss.isV2Triple.2.1
  have hpump : PumpUpLT 2 x K u K :=
    ⟨hterm'.1, hILo_u, h.T_le_C huQ.1, huQ.2.2, by rw [hpumpK]; exact hKK⟩
  have hsyl_u := hterm'.2.2 (T ⊓ CxK x K) hQsyl u K hpump huQ
    (fun q hq => huc q (hQQs hq))
  have hQsle : Qs ≤ centralizer ({u} : Set G) ⊓ centralizerSection K (pPrimeCoreOf 2 K) :=
    le_inf (fun c hc => mem_centralizer_singleton_iff.2 (huc c hc).symm)
      (fun c hc => hCK_cs (hQs.le hc))
  have hEq : Qs = T ⊓ CxK x K := hsyl_u.eq_of_le hQQs hQsle hQs2
  rw [hEq] at hQs
  exact hQs

theorem isTerminalPair_of_comp_Q (h : Th2Std x y K T S) (hev : 2 ∣ Nat.card ↥K)
    (hQ : IsSylowOf 2 (T ⊓ CxK x K) (centralizer (K : Set G)))
    (hcomp : ∀ u ∈ T ⊓ CxK x K, orderOf u = 2 → IsCompIn (centralizer ({u} : Set G)) K) :
    IsTerminalPair 2 x K := by
  refine ⟨h.orderOf_x, hcomp x ⟨h.x_mem_T, h.x_mem_CxK⟩ h.orderOf_x, hev, ?_⟩
  intro y' hy2 hyK
  have hyel := Th2.isElementaryAbelian_zpowers_of_orderOf_two hy2
  have hyp : IsPGroup 2 ↥(zpowers y') := CFSG.IsElementaryAbelian.isPGroup 2 _
  obtain ⟨g, hgC, hgW⟩ := Th2.exists_cj_le_of_isSylowOf hQ (zpowers_le.2 hyK) hyp
  have hv : g * y' * g⁻¹ ∈ T ⊓ CxK x K := by
    apply hgW
    rw [Th2.mem_cj_iff]
    have : g⁻¹ * (g * y' * g⁻¹) * g = y' := by group
    rw [this]
    exact mem_zpowers y'
  have hv2 : orderOf (g * y' * g⁻¹) = 2 := by
    rw [CFSG.BenderGlauberman.orderOf_conj_eq]; exact hy2
  have h1 := AS16.isCompIn_conj (hcomp _ hv hv2) g
  have hK : conjugate K g = K := by
    ext k
    rw [AS16.mem_conjugate_iff']
    constructor
    · intro hk
      have hc := Subgroup.mem_centralizer_iff.1 hgC _ hk
      have : g * k * g⁻¹ = k := by
        have h2 : g * (g * k * g⁻¹) = g * k := by
          calc g * (g * k * g⁻¹) = (g * k * g⁻¹) * g := hc.symm
            _ = g * k := by group
        have h3 := mul_left_cancel h2
        exact h3
      rw [this] at hk
      exact hk
    · intro hk
      have hc := Subgroup.mem_centralizer_iff.1 hgC _ hk
      have : g * k * g⁻¹ = k := by rw [← hc]; group
      rw [this]
      exact hk
  have hC : conjugate (centralizer ({g * y' * g⁻¹} : Set G)) g = centralizer ({y'} : Set G) := by
    rw [AS16.conjugate_centralizer_singleton]
    have : g⁻¹ * (g * y' * g⁻¹) * g = y' := by group
    rw [this]
  rwa [hK, hC] at h1

end Std

end CFSG.GH74.GLS
