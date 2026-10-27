module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S7b

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

omit [Finite H] in
theorem commutator_self_le (X : Subgroup H) : ⁅X, X⁆ ≤ X :=
  commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

section Seven

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts)
  (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma)
include I F h3

theorem DSig_comm_P : ∀ x ∈ h.D ⊔ zpowers d.sigma, ∀ π ∈ h.P, x * π = π * x := by
  intro x hx π hπ
  obtain ⟨e, he, w, hw, rfl⟩ := Eight.exists_mul_of_mem_sup₂ (D_comm_sigma F) hx
  have heπ : e * π = π * e := H₁.D_comm_P he hπ
  have hwπ : w * π = π * w := by
    rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hw with rfl | rfl
    · rw [one_mul, mul_one]
    · exact sigma_comm_P I F h3 hπ
  rw [mul_assoc, hwπ, ← mul_assoc, heπ, mul_assoc]

omit h3 in
theorem DSig_inf_P : (h.D ⊔ zpowers d.sigma) ⊓ h.P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxB, hxP⟩ := mem_inf.mp hx
  obtain ⟨e, he, w, hw, rfl⟩ := Eight.exists_mul_of_mem_sup₂ (D_comm_sigma F) hxB
  rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hw with rfl | rfl
  · rw [mul_one] at hxP ⊢
    exact (h.toHyp52.D_inf_P_eq_bot H₁.center_J) ▸ mem_inf.mpr ⟨he, hxP⟩
  · exfalso
    apply d.sigma_not_mem_DP I.cf1 I.cf2 F
    have := mul_mem_sup (inv_mem he) hxP
    rwa [inv_mul_cancel_left] at this

theorem F_le_DSig_sup_P : h.F32 ≤ (h.D ⊔ zpowers d.sigma) ⊔ h.P := by
  intro x hx
  obtain ⟨e, he, r, hr, rfl⟩ := Eight.exists_mul_of_mem_sup₂ (d.D_comm_R0 F)
    (F32_le_D_sup_R0 I F hx)
  obtain ⟨π, hπ, hr' | hr'⟩ := d.mem_R0_cases hr
  · subst hr'
    exact mul_mem (mem_sup_left (mem_sup_left he)) (mem_sup_right hπ)
  · subst hr'
    rw [← sigma_comm_P I F h3 hπ, ← mul_assoc]
    exact mul_mem (mem_sup_left (mul_mem (mem_sup_left he) (mem_sup_right (mem_zpowers _))))
      (mem_sup_right hπ)

omit h3 in
theorem F_le_normalizer_DSig :
    h.F32 ≤ normalizer ((h.D ⊔ zpowers d.sigma : Subgroup H) : Set H) := by
  intro f hf
  have hfS := h.F32_le_S hf
  have hσF := d.F32_le_centralizer_sigma I.rk I.j I.c I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F
  refine Eight.mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨e, he, w, hw, rfl⟩ := Eight.exists_mul_of_mem_sup₂ (D_comm_sigma F) hx
  have hfe : f⁻¹ * e * f ∈ h.D := by
    refine mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hfS) (mem_inf.mp he).1) hfS, ?_⟩
    have := (mem_normalizer_iff.mp (h.toHyp52.S_le_normalizer (inv_mem hfS)) e).mp
      (mem_inf.mp he).2
    rwa [inv_inv] at this
  have hfσ : f * d.sigma = d.sigma * f := mem_centralizer_singleton_iff.mp (hσF hf)
  rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hw with rfl | rfl
  · rw [mul_one]; exact mem_sup_left hfe
  · have h1 : f⁻¹ * (e * d.sigma) * f = f⁻¹ * e * f * d.sigma := by
      have hσf : d.sigma * f = f * d.sigma := hfσ.symm
      calc f⁻¹ * (e * d.sigma) * f = f⁻¹ * e * (d.sigma * f) := Eight.mul4_assoc f⁻¹ e d.sigma f
        _ = f⁻¹ * e * (f * d.sigma) := by rw [hσf]
        _ = f⁻¹ * e * f * d.sigma := (mul_assoc _ _ _).symm
    rw [h1]
    exact mul_mem (mem_sup_left hfe) (mem_sup_right (mem_zpowers _))

include hv

theorem DSig_sup_Dv_eq_F (hFO : CF81FieldOrd) :
    (h.D ⊔ zpowers d.sigma) ⊔ conjugate h.D v = h.F32 := by
  have hDF := d.D_le_F I.sy I.cf1 I.cf2 F
  have hDvF := conjugate_D_le_F hv hDF
  have hBF : h.D ⊔ zpowers d.sigma ≤ h.F32 := sup_le hDF (zpowers_le.mpr (sigma_mem_F I F))
  have hle : (h.D ⊔ zpowers d.sigma) ⊔ conjugate h.D v ≤ h.F32 := sup_le hBF hDvF
  have hcard1 : Nat.card ↥((h.D ⊔ zpowers d.sigma) ⊔ conjugate h.D v) =
      Nat.card ↥(h.D ⊔ zpowers d.sigma) * Nat.card h.D := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (hDvF.trans (F_le_normalizer_DSig I F))
      (disjoint_iff.mpr (by rw [inf_comm]; exact conjugate_D_inf_eq_bot hv I F)),
      Eight.card_conjugate']
  have hcard2 : Nat.card ↥((h.D ⊔ zpowers d.sigma) ⊔ h.P) =
      Nat.card ↥(h.D ⊔ zpowers d.sigma) * Nat.card h.P :=
    Seven.card_sup_of_commute (DSig_comm_P I F h3) (DSig_inf_P I F)
  have hFc := Subgroup.card_le_of_le (F_le_DSig_sup_P I F h3)
  rw [hcard2, card_P_eq_card_D hv I F h3 hFO, ← hcard1] at hFc
  exact eq_of_le_of_card_ge hle hFc

theorem P_mem_DSig_mul (hFO : CF81FieldOrd) {π : H} (hπ : π ∈ h.P) :
    ∃ β ∈ h.D ⊔ zpowers d.sigma, ∃ δ ∈ conjugate h.D v, β * δ = π := by
  have hπF : π ∈ h.F32 := P_le_F hv I F h3 hFO hπ
  rw [← DSig_sup_Dv_eq_F hv I F h3 hFO] at hπF
  have hπ' : π ∈ (((h.D ⊔ zpowers d.sigma) ⊔ conjugate h.D v : Subgroup H) : Set H) := hπF
  rw [coe_mul_of_right_le_normalizer_left _ _
    ((conjugate_D_le_F hv (d.D_le_F I.sy I.cf1 I.cf2 F)).trans (F_le_normalizer_DSig I F))] at hπ'
  obtain ⟨β, hβ, δ, hδ, hβδ⟩ := hπ'
  exact ⟨β, hβ, δ, hδ, hβδ⟩

variable {y : H} (hyS : y ∈ h.S) (hya : y⁻¹ * h.a * y = h.a) (hyz : y⁻¹ * d.z * y = d.z)
  (hyσ : y⁻¹ * d.sigma * y = h.a * d.z * d.sigma)
include hyS hya hyz hyσ

theorem y_nontrivial_P (hFO : CF81FieldOrd) (hDg : CF81Diag) :
    ∃ π ∈ h.P, y * π * y⁻¹ * π⁻¹ ∉ zpowers (d.p ^ 2) := by
  by_contra hall
  push Not at hall
  obtain ⟨δ, hδ, hnot⟩ := y_nontrivial_Dv hv I F h3 hyS hya hyz hyσ hDg
  apply hnot
  set X := ⁅conjugate h.D v, conjugate h.D v⁆ with hX
  set B := h.D ⊔ zpowers d.sigma with hB
  have hDF := d.D_le_F I.sy I.cf1 I.cf2 F
  have hDvF := conjugate_D_le_F hv hDF
  have hXDv : X ≤ conjugate h.D v := commutator_self_le _
  have hXN : X ≤ normalizer (B : Set H) := hXDv.trans (hDvF.trans (F_le_normalizer_DSig I F))
  have hdisj : conjugate h.D v ⊓ B = ⊥ := conjugate_D_inf_eq_bot hv I F
  have hsqX : ∀ e ∈ conjugate h.D v, e * e ∈ X := by
    intro e he
    rw [hX, commutator_conjugate, mem_conjugate_iff]
    have he' := mem_conjugate_iff.mp he
    rw [show v * (e * e) * v⁻¹ = v * e * v⁻¹ * (v * e * v⁻¹) by group]
    exact sq_mem_commutator_D I.sy F he'
  have haX : h.a ∈ X := by
    rw [hX, commutator_conjugate, mem_conjugate_iff, ← hv.conj_z,
      show v * (v⁻¹ * d.z * v) * v⁻¹ = d.z by group]
    exact z_mem_commutator_D I.sy F
  have hp2 : zpowers (d.p ^ 2) ≤ X ⊔ B := by
    rw [zpowers_le]
    obtain ⟨β₀, hβ₀, δ₀, hδ₀, hβδ₀⟩ := P_mem_DSig_mul hv I F h3 hFO d.p_mem
    have hcomm := DSig_comm_P I F h3 β₀ hβ₀ d.p d.p_mem
    have h1 : β₀ * β₀ * (δ₀ * δ₀) = d.p ^ 2 := by
      have hδ : δ₀ = β₀⁻¹ * d.p := by rw [← hβδ₀]; group
      have hc' : β₀⁻¹ * d.p = d.p * β₀⁻¹ := by
        calc β₀⁻¹ * d.p = β₀⁻¹ * (d.p * β₀) * β₀⁻¹ := by group
          _ = β₀⁻¹ * (β₀ * d.p) * β₀⁻¹ := by rw [hcomm]
          _ = d.p * β₀⁻¹ := by group
      rw [hδ, pow_two]
      calc β₀ * β₀ * (β₀⁻¹ * d.p * (β₀⁻¹ * d.p)) =
          β₀ * β₀ * (β₀⁻¹ * (d.p * β₀⁻¹) * d.p) := by group
        _ = β₀ * β₀ * (β₀⁻¹ * (β₀⁻¹ * d.p) * d.p) := by rw [← hc']
        _ = d.p * d.p := by group
    rw [← h1]
    exact mul_mem (mem_sup_right (mul_mem hβ₀ hβ₀)) (mem_sup_left (hsqX δ₀ hδ₀))
  have hδF := hDvF hδ
  obtain ⟨β, hβ, π, hπ, rfl⟩ :=
    Eight.exists_mul_of_mem_sup₂ (DSig_comm_P I F h3) (F_le_DSig_sup_P I F h3 hδF)
  have hyπ : y * π * y⁻¹ ∈ h.P := h.toHyp52.conj_mem_P' hyS hπ
  have hc : y * π * y⁻¹ * π⁻¹ ∈ h.P := mul_mem hyπ (inv_mem hπ)
  have hcβ : y * π * y⁻¹ * π⁻¹ * β⁻¹ = β⁻¹ * (y * π * y⁻¹ * π⁻¹) :=
    (DSig_comm_P I F h3 β⁻¹ (inv_mem hβ) _ hc).symm
  have hu : y * (β * π) * y⁻¹ * (β * π)⁻¹ =
      y * β * y⁻¹ * β⁻¹ * (y * π * y⁻¹ * π⁻¹) := by
    calc y * (β * π) * y⁻¹ * (β * π)⁻¹ = y * β * y⁻¹ * (y * π * y⁻¹ * π⁻¹ * β⁻¹) := by group
      _ = y * β * y⁻¹ * (β⁻¹ * (y * π * y⁻¹ * π⁻¹)) := by rw [hcβ]
      _ = y * β * y⁻¹ * β⁻¹ * (y * π * y⁻¹ * π⁻¹) := by group
  have hyσ' : y * d.sigma * y⁻¹ = h.a * d.z * d.sigma := by
    have hya' : y * h.a * y⁻¹ = h.a := by
      calc y * h.a * y⁻¹ = y * (y⁻¹ * h.a * y) * y⁻¹ := by rw [hya]
        _ = h.a := by group
    have hyz' : y * d.z * y⁻¹ = d.z := by
      calc y * d.z * y⁻¹ = y * (y⁻¹ * d.z * y) * y⁻¹ := by rw [hyz]
        _ = d.z := by group
    have hza' : h.a * d.z * (h.a * d.z) = 1 := by
      calc h.a * d.z * (h.a * d.z) = h.a * (d.z * h.a) * d.z := by group
        _ = h.a * (h.a * d.z) * d.z := by rw [d.z_comm_a]
        _ = (h.a * h.a) * (d.z * d.z) := by group
        _ = 1 := by rw [Six.a_mul_a_self h.toHyp52, d.z_mul_self, one_mul]
    have h2 : d.sigma = h.a * d.z * (y * d.sigma * y⁻¹) := by
      calc d.sigma = y * (y⁻¹ * d.sigma * y) * y⁻¹ := (Eight.mul_conj_inv_cancel y d.sigma).symm
        _ = y * (h.a * d.z * d.sigma) * y⁻¹ := by rw [hyσ]
        _ = h.a * d.z * (y * d.sigma * y⁻¹) := by rw [Eight.conj3_distrib', hya', hyz']
    calc y * d.sigma * y⁻¹ = h.a * d.z * (h.a * d.z * (y * d.sigma * y⁻¹)) := by
          rw [← mul_assoc (h.a * d.z) (h.a * d.z), hza', one_mul]
      _ = h.a * d.z * d.sigma := by rw [← h2]
  have hyβ : y * β * y⁻¹ ∈ X ⊔ B := by
    obtain ⟨e, he, w, hw, rfl⟩ := Eight.exists_mul_of_mem_sup₂ (D_comm_sigma F) hβ
    have hye : y * e * y⁻¹ ∈ h.D := by
      refine mem_inf.mpr ⟨mul_mem (mul_mem hyS (mem_inf.mp he).1) (inv_mem hyS), ?_⟩
      exact (mem_normalizer_iff.mp (h.toHyp52.S_le_normalizer hyS) e).mp (mem_inf.mp he).2
    rw [show y * (e * w) * y⁻¹ = y * e * y⁻¹ * (y * w * y⁻¹) by group]
    refine mul_mem (mem_sup_right (mem_sup_left hye)) ?_
    rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hw with rfl | rfl
    · rw [mul_one, mul_inv_cancel]; exact one_mem _
    · rw [hyσ']
      exact mul_mem (mul_mem (mem_sup_left haX) (mem_sup_right (mem_sup_left d.z_D)))
        (mem_sup_right (mem_sup_right (mem_zpowers _)))
  have huXB : y * (β * π) * y⁻¹ * (β * π)⁻¹ ∈ X ⊔ B := by
    rw [hu]
    exact mul_mem (mul_mem hyβ (mem_sup_right (inv_mem hβ))) (hp2 (hall π hπ))
  have hy'S : v * y * v⁻¹ ∈ h.S := (mem_normalizer_iff.mp hv.mem_N y).mp hyS
  have huDv : y * (β * π) * y⁻¹ * (β * π)⁻¹ ∈ conjugate h.D v := by
    refine mul_mem ?_ (inv_mem hδ)
    rw [mem_conjugate_iff]
    have he := mem_conjugate_iff.mp hδ
    rw [show v * (y * (β * π) * y⁻¹) * v⁻¹ =
      (v * y * v⁻¹) * (v * (β * π) * v⁻¹) * (v * y * v⁻¹)⁻¹ by group]
    refine mem_inf.mpr ⟨mul_mem (mul_mem hy'S (mem_inf.mp he).1) (inv_mem hy'S), ?_⟩
    exact (mem_normalizer_iff.mp (h.toHyp52.S_le_normalizer hy'S) _).mp (mem_inf.mp he).2
  have huXB' : y * (β * π) * y⁻¹ * (β * π)⁻¹ ∈ ((X ⊔ B : Subgroup H) : Set H) := huXB
  rw [coe_mul_of_left_le_normalizer_right X B hXN] at huXB'
  obtain ⟨ξ, hξ, β', hβ', hξβ⟩ := huXB'
  beta_reduce at hξβ
  have hβ'1 : β' = 1 := by
    have hmem : β' ∈ conjugate h.D v ⊓ B := by
      refine mem_inf.mpr ⟨?_, hβ'⟩
      have := mul_mem (inv_mem (hXDv hξ)) huDv
      rwa [← hξβ, inv_mul_cancel_left] at this
    rw [hdisj] at hmem
    exact mem_bot.mp hmem
  rw [← hξβ, hβ'1, mul_one]
  exact hξ

end Seven

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
