module

public import CFSG.GH74.GLS.C3.Layer1.BkL114A5
public import CFSG.GH74.GLS.C3.Layer1.Th2Pump

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_CxK_conj {u : G} {M : Subgroup G} {z : G} (hz : z ∈ CxK u M) (g : G) :
    g * z * g⁻¹ ∈ CxK (g * u * g⁻¹) (Th2.cj g M) := by
  refine ⟨mem_centralizer_singleton_iff.2 ?_, Stage1.Thm2.Recip.mem_cSec_cj hz.2 g⟩
  have := mem_centralizer_singleton_iff.1 hz.1
  calc g * z * g⁻¹ * (g * u * g⁻¹) = g * (z * u) * g⁻¹ := by group
    _ = g * (u * z) * g⁻¹ := by rw [this]
    _ = g * u * g⁻¹ * (g * z * g⁻¹) := by group

theorem no_central_involution_of_centerless [Finite G] {M : Subgroup G} (hcen : CenterlessBar M)
    {v : G} (hv2 : orderOf v = 2) (hvM : v ∈ M) (hc : ∀ k ∈ M, k * v = v * k) : False := by
  have huO : v ∈ pPrimeCoreOf 2 M := by
    refine mem_pPrimeCoreOf_of_commutators hcen hvM (fun k' hk' => ?_)
    rw [commutatorElement_def, hc k' hk']
    simp
  have hodd2 : Odd (orderOf v) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd M) (Subgroup.orderOf_dvd_natCard _ huO)
  rw [hv2] at hodd2
  exact absurd hodd2 (by decide)

theorem pump_comp_unique [Finite G] {u : G} (hu2 : orderOf u = 2) {M M' Q : Subgroup G}
    (hM : IsPCompIn 2 (centralizer ({u} : Set G)) M) (hM' : IsPCompIn 2 (centralizer ({u} : Set G)) M')
    (huM' : u ∉ M') (hr' : 2 ≤ pRank 2 ↥M') (hQ : IsSylowOf 2 Q (CxK u M))
    (hQrk : pRank 2 ↥Q ≤ 2) : M' = M := by
  by_contra hne
  have hle : M' ≤ CxK u M := le_inf hM'.1 (Stage1.Thm2.Recip.le_cSec_of_ne hM' hM hne)
  obtain ⟨E, hEM, hEel, hErk⟩ := exists_elemAbelian_pRank M'
  have hE2 : 2 ≤ pRank 2 ↥E := hErk ▸ hr'
  have hxel : CFSG.IsElementaryAbelian 2 ↥(zpowers u) := isElementaryAbelian_zpowers_of_orderOf_two hu2
  have hcd : CommDisj E (zpowers u) := by
    refine ⟨fun e he t ht => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ht
      have : e ∈ centralizer ({u} : Set G) := hM'.1 (hEM he)
      exact (Commute.zpow_right (mem_centralizer_singleton_iff.1 this) m).symm.eq.symm
    · refine eq_bot_iff.2 fun z hz => ?_
      rcases mem_zpowers_two hu2 hz.2 with h0 | h0
      · simp [h0]
      · exact absurd (hEM (h0 ▸ hz.1)) huM'
  have hFel := hcd.isElementaryAbelian_sup' hEel hxel le_rfl le_rfl
  have hFrk : pRank 2 ↥(E ⊔ zpowers u) = pRank 2 ↥E + 1 := by
    rw [hcd.pRank_sup hEel hxel le_rfl le_rfl, pRank_zpowers_of_orderOf_two hu2]
  have huCxKuM : u ∈ CxK u M := by
    refine ⟨mem_centralizer_singleton_iff.2 rfl,
      C3.Layer1.Back.mem_centralizerSection_of_centralizes ?_ ?_⟩
    · intro k' hk'
      exact (mem_centralizer_singleton_iff.1 (hM.1 hk')).symm
    · unfold pPrimeCoreOf
      intro z hz
      obtain ⟨z', -, rfl⟩ := hz
      exact z'.2
  have hFC : E ⊔ zpowers u ≤ CxK u M := sup_le (hEM.trans hle) (zpowers_le.2 huCxKuM)
  have hFp : IsPGroup 2 ↥(E ⊔ zpowers u) := CFSG.IsElementaryAbelian.isPGroup 2 _
  obtain ⟨g, hgC, hgF⟩ := Th2.exists_cj_le_of_isSylowOf hQ hFC hFp
  have h1 := C3.Layer1.Back.pRank_mono' hgF
  rw [pRank_cj, hFrk] at h1
  omega


theorem aconfigW_five_pumpup [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {u : G} (huQ : u ∈ Q) (hu1 : u ≠ 1) :
    ∃ M : Subgroup G, IsPCompIn 2 (centralizer ({u} : Set G)) M ∧ CenterlessBar M ∧
      2 ≤ pRank 2 ↥M ∧ IsSylowOf 2 Q (CxK u M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRel, hRcard⟩ := aconfigW_five_R h
  obtain ⟨hRc, hRs⟩ := forall_of_isElementaryAbelian hRel
  obtain ⟨hQc, hQs⟩ := forall_of_isElementaryAbelian h.elemQ
  have huR : u ∈ (T ⊓ K) ⊔ Q := Subgroup.mem_sup_right huQ
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hQs u huQ) hu1
  have hux : u ∈ centralizer ({x} : Set G) := h.T_le_C (h.Q_le_T huQ)
  have hucs : u ∈ centralizerSection K (pPrimeCoreOf 2 K) := (h.Q_le_CxK huQ).2
  have hRC : (T ⊓ K) ⊔ Q ≤ centralizer ({u} : Set G) := fun r hr =>
    mem_centralizer_singleton_iff.2 (hRc r hr u huR)
  have hR : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) := by
    have h1 := card_eq_two_pow_pRank hRel
    rw [hRcard] at h1
    have h2 : pRank 2 ↥((T ⊓ K) ⊔ Q) = 4 := by
      have : (2 : ℕ) ^ 4 = 2 ^ pRank 2 ↥((T ⊓ K) ⊔ Q) := by rw [← h1]; norm_num
      exact (Nat.pow_right_injective (le_refl 2) this).symm
    have h3 := C3.Layer1.Back.pRank_mono' hRC
    omega
  have hKil : IsILo 2 x K := h.twoTerminal.1
  obtain ⟨M, hlt⟩ := TwoThin.exists_pumpup_of_involution h.x_order hu2 hKil.2.2 hux hucs hKil hR
  obtain ⟨hxM, ⟨e⟩⟩ := h.twoTerminal.2.1 u M hlt
  have hQM : IsSylowOf 2 Q (CxK u M) :=
    h.twoTerminal.2.2 Q h.sylowQ u M hlt huQ (fun q hq => (hQc u huQ q hq))
  have hcen : CenterlessBar K := centerlessBar_of_A5 h.kbar
  have hcenM : CenterlessBar M := Th2.centerlessBar_of_equiv hcen e
  have hrM : 2 ≤ pRank 2 ↥M := by
    have h1 : pRank 2 (kBar M) = pRank 2 ↥M := by
      have hN : ¬ 2 ∣ Nat.card ↥(pPrimeCore 2 ↥M) := fun h2 =>
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1
          (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥M)) h2
      exact CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hN
    have h2 : pRank 2 (kBar K) = pRank 2 ↥K := by
      have hN : ¬ 2 ∣ Nat.card ↥(pPrimeCore 2 ↥K) := fun h2 =>
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1
          (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥K)) h2
      exact CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hN
    have h3 : pRank 2 (kBar M) = pRank 2 (kBar K) :=
      CFSG.RankThree.PartOne.Quotient36.pRank_congr_mulEquiv one_lt_two e
    have h4 : pRank 2 ↥(T ⊓ K) ≤ pRank 2 ↥K := C3.Layer1.Back.pRank_mono' inf_le_right
    have h5 : 2 ≤ pRank 2 ↥(T ⊓ K) := by
      obtain ⟨hPcard, hPel⟩ := aconfigW_five_P h
      have h6 := card_eq_two_pow_pRank hPel
      rw [hPcard] at h6
      have : (2 : ℕ) ^ 2 = 2 ^ pRank 2 ↥(T ⊓ K) := by rw [← h6]; norm_num
      exact (Nat.pow_right_injective (le_refl 2) this).symm.ge
    omega
  exact ⟨M, hlt.2.1.2.2, hcenM, hrM, hQM⟩


theorem aconfigW_five_TI [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {g : G}
    (hg : g ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G))
    (hne : Q ⊓ conjugate Q g ≠ ⊥) : conjugate Q g = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRel, hRcard⟩ := aconfigW_five_R h
  obtain ⟨hQc, hQs⟩ := forall_of_isElementaryAbelian h.elemQ
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have huQ : u ∈ Q := hu.1
  have hu1' : u ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
  have hu'Q : g * u * g⁻¹ ∈ Q := mem_conjugate_iff'.1 hu.2
  have hu'1 : g * u * g⁻¹ ≠ 1 := by
    intro h1
    apply hu1'
    have : u = g⁻¹ * (g * u * g⁻¹) * g := by group
    rw [this, h1]
    group
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hQs u huQ) hu1'
  have hu'2 : orderOf (g * u * g⁻¹) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hQs _ hu'Q) hu'1
  obtain ⟨M, hM, hcenM, hrM, hQM⟩ := aconfigW_five_pumpup h huQ hu1'
  obtain ⟨M₂, hM₂, hcenM₂, hrM₂, hQM₂⟩ := aconfigW_five_pumpup h hu'Q hu'1
  have hM' : IsPCompIn 2 (centralizer ({g * u * g⁻¹} : Set G)) (Th2.cj g M) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hM g
    rwa [Stage1.Thm2.Recip.map_centralizer_singleton_conj] at this
  have hu'M' : g * u * g⁻¹ ∉ Th2.cj g M := by
    intro hmem
    have hm : g⁻¹ * (g * u * g⁻¹) * g ∈ M := (Th2.mem_cj_iff g M _).1 hmem
    rw [show g⁻¹ * (g * u * g⁻¹) * g = u by group] at hm
    exact no_central_involution_of_centerless hcenM hu2 hm
      (fun k hk => mem_centralizer_singleton_iff.1 (hM.1 hk))
  have hr' : 2 ≤ pRank 2 ↥(Th2.cj g M) := by rw [pRank_cj]; exact hrM
  have hQrk : pRank 2 ↥Q ≤ 2 := by
    have h1 := card_eq_two_pow_pRank h.elemQ
    rw [h.card_Q] at h1
    have : (2 : ℕ) ^ 2 = 2 ^ pRank 2 ↥Q := by rw [← h1]; norm_num
    exact (Nat.pow_right_injective (le_refl 2) this).symm.le
  have heq : Th2.cj g M = M₂ := pump_comp_unique hu'2 hM₂ hM' hu'M' hr' hQM₂ hQrk
  have hR2 : IsPGroup 2 ↥((T ⊓ K) ⊔ Q) := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hQle : Q ≤ ((T ⊓ K) ⊔ Q) ⊓ CxK (g * u * g⁻¹) M₂ := le_inf le_sup_right hQM₂.le
  have hQeq : ((T ⊓ K) ⊔ Q) ⊓ CxK (g * u * g⁻¹) M₂ = Q :=
    hQM₂.eq_of_le hQle inf_le_right (hR2.to_le inf_le_left)
  have hsub : ∀ z ∈ Q, g * z * g⁻¹ ∈ Q := by
    intro z hz
    have hz1 : g * z * g⁻¹ ∈ (T ⊓ K) ⊔ Q :=
      (Subgroup.mem_normalizer_iff.1 hg z).1 (Subgroup.mem_sup_right hz)
    have hz2 : g * z * g⁻¹ ∈ CxK (g * u * g⁻¹) M₂ := by
      have := mem_CxK_conj (hQM.le hz) g
      rwa [heq] at this
    rw [← hQeq]
    exact ⟨hz1, hz2⟩
  have hle : Q ≤ conjugate Q g := fun z hz => mem_conjugate_iff'.2 (hsub z hz)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjugate'])).symm

end CFSG.GH74.GLS.C3.Layer1.Bk
