module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemCls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL47A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE16L

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma ht_mul_self (h : Ctx t L S x₁ x₂ lam rho tau) : t * t = 1 := t_mul_self h.hyp

private lemma conj_mem_L (h : Ctx t L S x₁ x₂ lam rho tau) {k x : G}
    (hk : k ∈ invCent t) (hx : x ∈ L) : k * x * k⁻¹ ∈ L := by
  have hxH : x ∈ invCent t := L_le_invCent h.hyp hx
  have hmem : (⟨k, hk⟩ : ↥(invCent t)) * (⟨x, hxH⟩ : ↥(invCent t)) *
      (⟨k, hk⟩ : ↥(invCent t))⁻¹ ∈ L.subgroupOf (invCent t) :=
    h.hyp.normal.conj_mem ⟨x, hxH⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨k, hk⟩
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

private lemma htau2_of (h44 : tau ^ 2 = 1) : tau * tau = 1 := by
  simpa [pow_two] using h44

private lemma tau_inv_eq (h44 : tau ^ 2 = 1) : tau⁻¹ = tau :=
  inv_eq_of_mul_eq_one_right (htau2_of h44)

private lemma twoCore_eq_one_or_eq_t (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) {a : G} (ha : a ∈ twoCore t) : a = 1 ∨ a = t := by
  have ha' : a ∈ zpowers t := h43 ▸ ha
  have hdvd : orderOf a ∣ orderOf t := orderOf_dvd_of_mem_zpowers ha'
  have ha2 : a ^ 2 = 1 := by
    have h2 : orderOf a ∣ 2 := by rw [← h.hyp.ord_t]; exact hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  exact h.hyp.eq_one_or_eq a ha ha2

private lemma conj_eq_of_mem_twoCore (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) {a x : G} (ha : a ∈ twoCore t)
    (hx : x ∈ invCent t) : a * x * a⁻¹ = x := by
  have ha' : a ∈ zpowers t := h43 ▸ ha
  have hdvd : orderOf a ∣ orderOf t := orderOf_dvd_of_mem_zpowers ha'
  have ha2 : a ^ 2 = 1 := by
    have h2 : orderOf a ∣ 2 := by rw [← h.hyp.ord_t]; exact hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  rcases h.hyp.eq_one_or_eq a ha ha2 with ha1 | ha1
  · rw [ha1, one_mul, inv_one, mul_one]
  · rw [ha1, (mem_invCent_iff.mp hx).symm, mul_assoc, mul_inv_cancel, mul_one]

private lemma mem_PL_or_mul_tau_mem (h : Ctx t L S x₁ x₂ lam rho tau) {g : G}
    (hg : g ∈ invCent t) : g ∈ twoCore t ⊔ L ∨ g * tau ∈ twoCore t ⊔ L := by
  have hPLH : twoCore t ⊔ L ≤ invCent t :=
    sup_le (twoCore_le_invCent t) (L_le_invCent h.hyp)
  have htauH : tau ∈ invCent t := h.le_invCent h.tau_mem
  rcases mem_or_mem_or_mul_mem_of_relIndex_two (S := invCent t) (K := twoCore t ⊔ L)
      hPLH h.relIndex_two hg htauH with h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd h1 h.tau_not_mem
  · exact Or.inr h1

private lemma mem_sup_iff_mem_L_or (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) {x : G} :
    x ∈ twoCore t ⊔ L ↔ x ∈ L ∨ t * x ∈ L := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hx
    rcases twoCore_eq_one_or_eq_t h h43 ha with ha1 | ha1
    · rw [ha1, one_mul]; exact Or.inl hb
    · rw [ha1]
      exact Or.inr (by rw [← mul_assoc, ht_mul_self h, one_mul]; exact hb)
  · rintro (hx | hx)
    · exact Subgroup.mem_sup_right hx
    · have hx' : x = t * (t * x) := by rw [← mul_assoc, ht_mul_self h, one_mul]
      rw [hx']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h.hyp.mem_twoCore)
        (Subgroup.mem_sup_right hx)

private lemma conj_t_mul (h : Ctx t L S x₁ x₂ lam rho tau) {k : G}
    (hk : k ∈ invCent t) (x : G) : t * (k * x * k⁻¹) = k * (t * x) * k⁻¹ := by
  have hcomm : t * k = k * t := (mem_invCent_iff.mp hk).symm
  calc t * (k * x * k⁻¹) = (t * k) * x * k⁻¹ := by group
    _ = (k * t) * x * k⁻¹ := by rw [hcomm]
    _ = k * (t * x) * k⁻¹ := by group

private lemma conj_tau_mem_coset (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) {k : G} (hk : k ∈ invCent t) :
    tau⁻¹ * (k * tau * k⁻¹) ∈ L := by
  have htauH : tau ∈ invCent t := h.le_invCent h.tau_mem
  have hPLH : twoCore t ⊔ L ≤ invCent t :=
    sup_le (twoCore_le_invCent t) (L_le_invCent h.hyp)
  rcases mem_or_mem_or_mul_mem_of_relIndex_two (S := invCent t) (K := twoCore t ⊔ L)
      hPLH h.relIndex_two htauH hk with hK | hK | hK
  · exact absurd hK h.tau_not_mem
  · obtain ⟨p, hp, l, hl, hk_eq⟩ :=
      (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hK
    have hmH : l * tau * l⁻¹ ∈ invCent t :=
      (invCent t).mul_mem ((invCent t).mul_mem (L_le_invCent h.hyp hl) htauH)
        ((invCent t).inv_mem (L_le_invCent h.hyp hl))
    have hconj : (p * l) * tau * (p * l)⁻¹ = l * tau * l⁻¹ := by
      rw [show (p * l) * tau * (p * l)⁻¹ = p * (l * tau * l⁻¹) * p⁻¹ from by group,
        conj_eq_of_mem_twoCore h h43 hp hmH]
    rw [hk_eq, hconj, tau_inv_eq h44]
    have hL : tau * l * tau ∈ L := by
      have hc := conj_mem_L h htauH hl
      rwa [tau_inv_eq h44] at hc
    have hgoal : tau * (l * tau * l⁻¹) = (tau * l * tau) * l⁻¹ := by group
    rw [hgoal]
    exact Subgroup.mul_mem _ hL (Subgroup.inv_mem _ hl)
  · obtain ⟨p, hp, l, hl, hk_eq⟩ :=
      (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hK
    have hk_eq' : k = tau⁻¹ * (p * l) := by rw [← hk_eq, inv_mul_cancel_left]
    have hmL : l * tau * l⁻¹ ∈ invCent t :=
      (invCent t).mul_mem ((invCent t).mul_mem (L_le_invCent h.hyp hl) htauH)
        ((invCent t).inv_mem (L_le_invCent h.hyp hl))
    have hpcenter : p * (l * tau * l⁻¹) * p⁻¹ = l * tau * l⁻¹ :=
      conj_eq_of_mem_twoCore h h43 hp hmL
    have hconj : k * tau * k⁻¹ = tau⁻¹ * (l * tau * l⁻¹) * tau := by
      rw [hk_eq']
      calc (tau⁻¹ * (p * l)) * tau * (tau⁻¹ * (p * l))⁻¹
          = tau⁻¹ * (p * (l * tau * l⁻¹) * p⁻¹) * tau := by group
        _ = tau⁻¹ * (l * tau * l⁻¹) * tau := by rw [hpcenter]
    rw [hconj]
    have htauinv2 : tau⁻¹ * tau⁻¹ = 1 := by
      rw [tau_inv_eq h44, ← pow_two]
      exact h44
    have hgoal : tau⁻¹ * (tau⁻¹ * (l * tau * l⁻¹) * tau) =
        l * (tau * l⁻¹ * tau) := by
      calc tau⁻¹ * (tau⁻¹ * (l * tau * l⁻¹) * tau)
          = (tau⁻¹ * tau⁻¹) * (l * tau * l⁻¹) * tau := by group
        _ = l * tau * l⁻¹ * tau := by rw [htauinv2, one_mul]
        _ = l * (tau * l⁻¹ * tau) := by group
    rw [hgoal]
    refine Subgroup.mul_mem _ hl ?_
    have hc := conj_mem_L h htauH (Subgroup.inv_mem _ hl)
    rwa [tau_inv_eq h44] at hc

theorem lemma4_7e_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) : Lemma4_7eConcl t S x₁ x₂ tau := by
  unfold Lemma4_7eConcl
  intro Y hY
  have hYIs : IsE16In S Y := hY
  unfold IsE16In at hY
  obtain ⟨hYS, hYea, hYcard⟩ := hY
  have htY : t ∈ Y := t_mem_of_isE16 h h43 h44 hYIs
  have hY2 : ∀ u ∈ Y, u * u = 1 := by
    intro u hu
    have h1 := hYea.2 u hu
    rwa [pow_two] at h1
  have hzL : (x₁ * x₂) ^ 2 ∈ L := (y_z_mem_L h.toCtx0).2
  have hz_ne : (x₁ * x₂) ^ 2 ≠ 1 := (z_mul_self_ne_one h.toCtx0).2
  have hYL : (((Y ⊓ L : Subgroup G) : Set G)).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact card_inf_L_of_E16 h h43 hYIs
  have hset1 : conjIn (invCent t) ((x₁ * x₂) ^ 2) ∩ (Y : Set G) =
      ((Y ⊓ L : Subgroup G) : Set G) \ {1} := by
    ext u
    constructor
    · rintro ⟨⟨k, hkH, hkeq⟩, huY⟩
      have huL : u ∈ L := by
        rw [← hkeq]
        exact conj_mem_L h hkH hzL
      refine ⟨⟨huY, huL⟩, ?_⟩
      intro hu1
      exact hz_ne (by
        calc (x₁ * x₂) ^ 2 = k⁻¹ * (k * (x₁ * x₂) ^ 2 * k⁻¹) * k := by group
          _ = k⁻¹ * u * k := by rw [hkeq]
          _ = 1 := by rw [Set.mem_singleton_iff.mp hu1]; group)
    · rintro ⟨⟨huY, huL⟩, hu_ne⟩
      have hne : u ≠ 1 := fun h1 => hu_ne (Set.mem_singleton_iff.mpr h1)
      obtain ⟨c, hcL, hc⟩ := h.toCtx0.invol_L u huL (hY2 u huY) hne
      exact ⟨⟨c, L_le_invCent h.hyp hcL, hc⟩, huY⟩
  have hcard1 : (conjIn (invCent t) ((x₁ * x₂) ^ 2) ∩ (Y : Set G)).ncard = 3 := by
    rw [hset1, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem (Y ⊓ L))]
    rw [show (((Y ⊓ L : Subgroup G) : Set G)).ncard = 4 from hYL]
  have hset2 : conjIn (invCent t) (t * (x₁ * x₂) ^ 2) ∩ (Y : Set G) =
      (fun u => t * u) '' (conjIn (invCent t) ((x₁ * x₂) ^ 2) ∩ (Y : Set G)) := by
    ext u
    constructor
    · rintro ⟨⟨k, hkH, hkeq⟩, huY⟩
      have htw : t * (k * (x₁ * x₂) ^ 2 * k⁻¹) = u := by
        rw [conj_t_mul h hkH ((x₁ * x₂) ^ 2)]
        exact hkeq
      have hwY : k * (x₁ * x₂) ^ 2 * k⁻¹ ∈ Y := by
        have htuY : t * u ∈ Y := Y.mul_mem htY huY
        have htu : t * u = k * (x₁ * x₂) ^ 2 * k⁻¹ := by
          rw [← htw, ← mul_assoc, ht_mul_self h, one_mul]
        rwa [htu] at htuY
      exact ⟨k * (x₁ * x₂) ^ 2 * k⁻¹, ⟨⟨k, hkH, rfl⟩, hwY⟩, htw⟩
    · rintro ⟨w, ⟨⟨k, hkH, hkeq⟩, hwY⟩, htw⟩
      refine ⟨⟨k, hkH, ?_⟩, ?_⟩
      · rw [← htw, ← conj_t_mul h hkH ((x₁ * x₂) ^ 2), hkeq]
      · rw [← htw]
        exact Y.mul_mem htY hwY
  have hcard2 : (conjIn (invCent t) (t * (x₁ * x₂) ^ 2) ∩ (Y : Set G)).ncard = 3 := by
    rw [hset2, Set.ncard_image_of_injective _ (mul_right_injective t)]
    exact hcard1
  have hset4 : conjIn (invCent t) tau ∩ (Y : Set G) =
      {u : G | u ∈ Y ∧ tau⁻¹ * u ∈ L} := by
    ext u
    constructor
    · rintro ⟨⟨k, hkH, hkeq⟩, huY⟩
      refine ⟨huY, ?_⟩
      rw [← hkeq]
      exact conj_tau_mem_coset h h43 h44 hkH
    · rintro ⟨huY, hlu⟩
      have h2 : (tau * (tau⁻¹ * u)) * (tau * (tau⁻¹ * u)) = 1 := by
        simpa [mul_inv_cancel_left] using hY2 u huY
      obtain ⟨c, hcL, hc⟩ := (involutions_tau_coset_of h h43 h44).1 (tau⁻¹ * u) hlu h2
      refine ⟨⟨c, L_le_invCent h.hyp hcL, ?_⟩, huY⟩
      rw [hc, mul_inv_cancel_left]
  have hcard4 : (conjIn (invCent t) tau ∩ (Y : Set G)).ncard = 4 := by
    rw [hset4, ncard_coset_inter (Y := Y) (L := L) (g := tau)
      (exists_mem_E16_coset h h43 hYIs tau (h.le_invCent h.tau_mem))]
    exact card_inf_L_of_E16 h h43 hYIs
  have httauH : t * tau ∈ invCent t :=
    (invCent t).mul_mem (mem_invCent_iff.mpr rfl) (h.le_invCent h.tau_mem)
  have hset5 : conjIn (invCent t) (t * tau) ∩ (Y : Set G) =
      {u : G | u ∈ Y ∧ (t * tau)⁻¹ * u ∈ L} := by
    ext u
    constructor
    · rintro ⟨⟨k, hkH, hkeq⟩, huY⟩
      refine ⟨huY, ?_⟩
      rw [← hkeq]
      have hstep : (t * tau)⁻¹ * (k * (t * tau) * k⁻¹) =
          tau⁻¹ * (k * tau * k⁻¹) := by
        rw [← conj_t_mul h hkH tau, mul_inv_rev]
        group
      rw [hstep]
      exact conj_tau_mem_coset h h43 h44 hkH
    · rintro ⟨huY, hlu⟩
      have h2 : ((t * tau) * ((t * tau)⁻¹ * u)) * ((t * tau) * ((t * tau)⁻¹ * u)) = 1 := by
        rw [mul_inv_cancel_left]
        exact hY2 u huY
      obtain ⟨c, hcL, hc⟩ :=
        (involutions_tau_coset_of h h43 h44).2 ((t * tau)⁻¹ * u) hlu h2
      refine ⟨⟨c, L_le_invCent h.hyp hcL, ?_⟩, huY⟩
      rw [hc, mul_inv_cancel_left]
  have hcard5 : (conjIn (invCent t) (t * tau) ∩ (Y : Set G)).ncard = 4 := by
    rw [hset5, ncard_coset_inter (Y := Y) (L := L) (g := t * tau)
      (exists_mem_E16_coset h h43 hYIs (t * tau) httauH)]
    exact card_inf_L_of_E16 h h43 hYIs
  exact ⟨hcard1, hcard2, hcard4, hcard5⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
