module

public import CFSG.GH74.Uniqueness.SU.KI6BFrat

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG CFSG.Blueprint CFSG.ProperTwoGeneratedCore CFSG.GH74.Uniqueness.SU.K.R3
open scoped Pointwise commutatorElement
open CFSG.LocalCores

variable {H : Type} [Group H] [Finite H] {T : Sylow 2 H} {H₀ : Subgroup H}

omit [Finite H] in
theorem layer_eq_of_unique {K : Subgroup H} (hK : IsComponent K)
    (huniq : ∀ K' : Subgroup H, IsComponent K' → K' = K) : layer H = K :=
  le_antisymm (sSup_le fun L hL => (huniq L hL).le) (component_le_layer hK)

theorem exists_noncentral_cent (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K : Subgroup H} (hK : IsComponent K) :
    ∃ x ∈ (T : Subgroup H), x ∈ centralizer (K : Set H) ∧ x ∈ generalizedFitting H ∧
      x ∉ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hlayerF : layer H ≤ generalizedFitting H := le_sup_right
  have hfit : fittingSubgroup H = pCore 2 H := Fitting_eq_pcore H 2 h.odd
  have hdata := component_data F h htc ht2 hK (hr K hK)
  have hQ : pCore 2 H ≤ zpowers t := by
    intro q hq
    apply hcon q (Cfg.pCore_le_T T hq)
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (h.pCore_comm_layer hq (component_le_layer hK hx)).symm
    · exact (le_sup_left : fittingSubgroup H ≤ generalizedFitting H) (by rw [hfit]; exact hq)
  have huniq : ∀ K' : Subgroup H, IsComponent K' → K' = K := by
    intro K' hK'
    by_contra hne
    obtain ⟨y', hy'K', hy'T, hy'4⟩ := exists_orderFour_mem F h htc ht2 hK' (hr K' hK')
    have hcomm := components_commute hK hK' (fun h' => hne h'.symm)
    apply not_mem_zpowers_of_orderOf_four ht2 hy'4
    apply hcon y' hy'T
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact hcomm x hx y' hy'K'
    · exact hlayerF (component_le_layer hK' hy'K')
  have hlayer : layer H = K := layer_eq_of_unique hK huniq
  have htK : t ∈ K := hdata.1
  have hFK : generalizedFitting H ≤ K := by
    refine sup_le ?_ hlayer.le
    rw [hfit]
    intro q hq
    exact Subgroup.zpowers_le.mpr htK (hQ hq)
  have := (SU1.pRank_mono (by norm_num) hFK).trans (hr K hK)
  have h2 := two_le_pRank_generalizedFitting F h hr htc ht2
  omega

theorem exists_orderOf_four_of_card {W : Subgroup H} (hW : IsPGroup 2 W)
    (hcard : 4 ≤ Nat.card W)
    (huniq : ∀ a ∈ W, ∀ b ∈ W, orderOf a = 2 → orderOf b = 2 → a = b) :
    ∃ y ∈ W, orderOf y = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  by_contra hcon
  push Not at hcon
  have hinv : ∀ a ∈ W, a ≠ 1 → orderOf a = 2 := by
    intro a ha ha1
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hW) ⟨a, ha⟩
    have hord : orderOf a = 2 ^ n := (Subgroup.orderOf_coe (⟨a, ha⟩ : ↥W)).trans hn
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · interval_cases n
      · rw [pow_zero, orderOf_eq_one_iff] at hord; exact absurd hord ha1
      · simpa using hord
    · exfalso
      have hdvd : 2 ^ (n - 2) ∣ orderOf a := by
        rw [hord]; exact pow_dvd_pow 2 (by omega)
      have h4 : orderOf (a ^ (2 ^ (n - 2))) = 4 := by
        rw [orderOf_pow_of_dvd (by positivity) hdvd, hord]
        have : 2 ^ n = 2 ^ (n - 2) * 4 := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
        rw [this, Nat.mul_div_cancel_left _ (by positivity)]
      exact hcon (a ^ (2 ^ (n - 2))) (W.pow_mem ha _) h4
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ W, a ≠ 1 := by
    by_contra hall
    push Not at hall
    have : W = ⊥ := eq_bot_iff.mpr fun x hx => hall x hx
    rw [this, Subgroup.card_bot] at hcard
    omega
  have hW2 : W ≤ zpowers a := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    · rw [huniq x hx a ha (hinv x hx hx1) (hinv a ha ha1)]; exact Subgroup.mem_zpowers a
  have := Subgroup.card_le_of_le hW2
  rw [Nat.card_zpowers, hinv a ha ha1] at this
  omega


omit [Finite H] in
theorem mem_normalizer_sup_of_centralizes {A B : Subgroup H}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {k : H} (hkA : k ∈ normalizer (A : Set H))
    (hkB : ∀ b ∈ B, k * b = b * k) : k ∈ normalizer ((A ⊔ B : Subgroup H) : Set H) := by
  have key : ∀ k : H, k ∈ normalizer (A : Set H) → (∀ b ∈ B, k * b = b * k) →
      ∀ g ∈ A ⊔ B, k * g * k⁻¹ ∈ A ⊔ B := by
    intro k hkA hkB g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := SU1.mem_sup_of_commute hAB hg
    have h1 : k * a * k⁻¹ ∈ A := ((Subgroup.mem_normalizer_iff.mp hkA) a).mp ha
    have h2 : k * b * k⁻¹ = b := by rw [hkB b hb]; group
    have : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
    rw [this, h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hb)
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact key k hkA hkB g
  · intro hg
    have hkA' : k⁻¹ ∈ normalizer (A : Set H) := (normalizer (A : Set H)).inv_mem hkA
    have hkB' : ∀ b ∈ B, k⁻¹ * b = b * k⁻¹ := by
      intro b hb
      have := hkB b hb
      calc k⁻¹ * b = k⁻¹ * (b * k) * k⁻¹ := by group
        _ = k⁻¹ * (k * b) * k⁻¹ := by rw [this]
        _ = b * k⁻¹ := by group
    have h5 := key k⁻¹ hkA' hkB' _ hg
    have h6 : k⁻¹ * (k * g * k⁻¹) * k⁻¹⁻¹ = g := by group
    rwa [h6] at h5

theorem normalizer_le_H₀ (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K : Subgroup H} (hK : IsComponent K) {W : Subgroup H}
    (hWT : W ≤ (T : Subgroup H)) (hWK : W ≤ K) (hy : ∃ y ∈ W, orderOf y = 4) {k : H}
    (hkK : k ∈ K) (hk : k ∈ normalizer (W : Set H)) : k ∈ H₀ := by
  obtain ⟨y, hyW, hy4⟩ := hy
  obtain ⟨x, hxT, hxC, -, hxt⟩ := exists_noncentral_cent F h hr htc ht2 hK
  have hdata := component_data F h htc ht2 hK (hr K hK)
  have hx2 : ∃ n : ℕ, x ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp T.isPGroup') ⟨x, hxT⟩
    refine ⟨n, ?_⟩
    have : x ^ (2 ^ n) = 1 := by
      have h1 := (Subgroup.orderOf_coe (⟨x, hxT⟩ : ↥(T : Subgroup H))).trans hn
      rw [← h1]; exact pow_orderOf_eq_one x
    exact this
  have hxcomm : ∀ g ∈ K, x * g = g * x := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp hxC g hg).symm
  have hrank0 := two_le_pRank_of_order_four F h htc ht2 hK (hr K hK) (hWK hyW) hy4
    (hxcomm y (hWK hyW)).symm hxt hx2
    (fun g hg1 hg2 => hdata.2.2.1 g (Subgroup.zpowers_le.mpr (hWK hyW) hg1) (fun k' hk' => by
      have hgc : g ∈ centralizer (K : Set H) := (Subgroup.zpowers_le.mpr hxC) hg2
      exact (Subgroup.mem_centralizer_iff.mp hgc k' hk').symm))
  have hrank : 2 ≤ Open.pRank 2 (W ⊔ zpowers x) :=
    hrank0.trans (SU1.pRank_mono (by norm_num)
      (sup_le_sup (Subgroup.zpowers_le.mpr hyW) le_rfl))
  have hDT : W ⊔ zpowers x ≤ H₀ :=
    sup_le (hWT.trans h.sylow_le) (Subgroup.zpowers_le.mpr (h.sylow_le hxT))
  apply two_generated_core_subgroup_normalizer_le T H₀ h.sylow_le h.gamma _ hDT hrank
  apply mem_normalizer_sup_of_centralizes ?_ hk
  · intro b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have := Subgroup.mem_centralizer_iff.mp hxC k hkK
    exact ((Commute.zpow_right (show Commute k x from this) n)).eq
  · intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have := Subgroup.mem_centralizer_iff.mp hxC a (hWK ha)
    exact ((Commute.zpow_right (show Commute a x from this) n)).eq


omit [Finite H] in
theorem coe_mem_normalizer_map {K : Subgroup H} (W' : Subgroup ↥K) {k : ↥K}
    (hk : k ∈ normalizer (W' : Set ↥K)) :
    (k : H) ∈ normalizer ((W'.map K.subtype : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨k * w * k⁻¹, ((Subgroup.mem_normalizer_iff.mp hk) w).mp hw, ?_⟩
    simp
  · rintro ⟨w, hw, hwx⟩
    have hwx' : (w : H) = (k : H) * x * (k : H)⁻¹ := hwx
    have hxeq : x = (k : H)⁻¹ * (w : H) * (k : H) := by rw [hwx']; group
    have hxK : x ∈ K := by
      rw [hxeq]
      exact K.mul_mem (K.mul_mem (K.inv_mem k.2) w.2) k.2
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    have h1 : (⟨x, hxK⟩ : ↥K) = k⁻¹ * w * k := by
      apply Subtype.ext
      simpa using hxeq
    show (⟨x, hxK⟩ : ↥K) ∈ W'
    rw [h1]
    have h3 := (Subgroup.mem_normalizer_iff.mp hk) (k⁻¹ * w * k)
    have h2 : k * (k⁻¹ * w * k) * k⁻¹ = w := by group
    rw [h3, h2]
    exact hw

theorem component_sl25 (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K : Subgroup H} (hK : IsComponent K) (hKH : ¬ K ≤ H₀) :
    Nonempty ((↥K ⧸ center ↥K) ≃* alternatingGroup (Fin 5)) ∧ IsSL25 ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_component T hK
  have hdata := component_data F h htc ht2 hK (hr K hK)
  have hrk : CFSG.pRank 2 ↥K ≤ 1 := (pRank_coe_eq K).trans_le (hr K hK)
  have hZ := h.isPGroup_center_component hK
  have h5 : Nonempty ((↥K ⧸ center ↥K) ≃* alternatingGroup (Fin 5)) := by
    refine F.stronglyEmbedded ↥K hK.1 hrk hZ S (H₀.subgroupOf K) ?_ ?_ ?_
    · intro x hx
      exact Subgroup.mem_subgroupOf.mpr (h.sylow_le ((hS x).mp hx))
    · intro htop
      apply hKH
      intro x hx
      have : (⟨x, hx⟩ : ↥K) ∈ H₀.subgroupOf K := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.mp this
    · intro W' hW'S hW'4 k hk
      apply Subgroup.mem_subgroupOf.mpr
      let W : Subgroup H := W'.map K.subtype
      have hWT : W ≤ (T : Subgroup H) := by
        rintro _ ⟨w, hw, rfl⟩
        exact (hS w).mp (hW'S hw)
      have hWK : W ≤ K := by
        rintro _ ⟨w, hw, rfl⟩
        exact w.2
      have hWp : IsPGroup 2 W := IsPGroup.to_le T.isPGroup' hWT
      have hWcard : 4 ≤ Nat.card W := by
        rw [Subgroup.card_map_of_injective K.subtype_injective]; exact hW'4
      obtain ⟨y, hyW, hy4⟩ := exists_orderOf_four_of_card hWp hWcard (fun a ha b hb ha2 hb2 =>
        (hdata.2.1 a (hWK ha) ha2).trans (hdata.2.1 b (hWK hb) hb2).symm)
      exact normalizer_le_H₀ F h hr htc ht2 hK hWT hWK ⟨y, hyW, hy4⟩ k.2
        (coe_mem_normalizer_map W' hk)
  exact ⟨h5, F.sl25 ↥K hK.1 hrk hZ h5⟩

end CFSG.GH74.Uniqueness.SU.K.R6
