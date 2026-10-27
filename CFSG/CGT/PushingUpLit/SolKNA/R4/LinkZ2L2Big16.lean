module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big9
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big12

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section Squares

variable {F : Type} [Field F] [Finite F]

theorem not_isSquare_y_diag (h2 : (2 : F) ≠ 0) {σ₀ : F ≃+* F} {q : ℕ}
    (hq : ∀ x : F, σ₀ x = x ^ q) (hcard : Nat.card Fˣ = q * q - 1) {r : ℕ} (hr : 4 ≤ r)
    {x₀ y : Fˣ} (hx₀ : orderOf x₀ = 2 ^ (r - 1)) (hx : autU σ₀ x₀ = x₀⁻¹)
    (hy : y * autU σ₀ y = -1) : ¬ IsSquare y := by
  have hxq : x₀ ^ q = x₀⁻¹ := (autU_eq_pow hq x₀).symm.trans hx
  have hxq1 : x₀ ^ (q + 1) = 1 := by rw [pow_succ, hxq, inv_mul_cancel]
  have hdvd : 2 ^ (r - 1) ∣ q + 1 := by
    rw [← hx₀]
    exact orderOf_dvd_of_pow_eq_one hxq1
  have hq8 : q % 8 = 7 := q_mod_eight_of_dvd_add_one hr hdvd
  have hq1 : 1 ≤ q := by omega
  obtain ⟨m, hm⟩ : ∃ m, q = 8 * m + 7 := by
    refine ⟨q / 8, ?_⟩
    have := Nat.div_add_mod q 8
    omega
  have hdy : (q - 1) / 2 = 4 * m + 3 := by rw [hm]; omega
  have hcard2 : Nat.card Fˣ / 2 = 32 * m * m + 56 * m + 24 := by
    rw [hcard, hm]
    have hsq : (8 * m + 7) * (8 * m + 7) = 2 * (32 * m * m + 56 * m + 24) + 1 := by ring
    have h : (8 * m + 7) * (8 * m + 7) - 1 = 2 * (32 * m * m + 56 * m + 24) := by omega
    rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hcd_y : (q + 1) * ((q - 1) / 2) = Nat.card Fˣ / 2 := by
    rw [hdy, hcard2, hm]
    ring
  have hy_pow : y ^ (q + 1) = -1 := by
    rw [pow_succ, mul_comm (y ^ q) y, ← hy, autU_eq_pow hq y]
  have hodd : ¬ Even ((q - 1) / 2) := by
    rw [hdy]
    intro h
    obtain ⟨j, hj⟩ := h
    omega
  exact fun h => hodd ((isSquare_iff_even_of_pow_eq_neg_one h2 hcd_y hy_pow).mp h)

theorem not_isSquare_y_anti (h2 : (2 : F) ≠ 0) {σ₀ : F ≃+* F} {q : ℕ}
    (hq : ∀ x : F, σ₀ x = x ^ q) (hcard : Nat.card Fˣ = q * q - 1) {r : ℕ} (hr : 4 ≤ r)
    {x₀ y : Fˣ} (hx₀ : orderOf x₀ = 2 ^ (r - 1)) (hx : autU σ₀ x₀ = x₀)
    (hy : y * (autU σ₀ y)⁻¹ = -1) : ¬ IsSquare y := by
  have hq1 : 1 ≤ q := by
    by_contra hq1'
    have hq0 : q = 0 := by omega
    have hx1 : x₀ = 1 := by
      rw [← hx, autU_eq_pow hq x₀, hq0, pow_zero]
    have h8 : 8 ≤ 2 ^ (r - 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : orderOf x₀ = 1 := by rw [hx1, orderOf_one]
    omega
  have hxq : x₀ ^ q = x₀ := (autU_eq_pow hq x₀).symm.trans hx
  have hxqm1 : x₀ ^ (q - 1) = 1 := by
    have h : x₀ ^ (q - 1) * x₀ = 1 * x₀ := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel hq1, hxq]
    exact mul_right_cancel h
  have hdvd : 2 ^ (r - 1) ∣ q - 1 := by
    rw [← hx₀]
    exact orderOf_dvd_of_pow_eq_one hxqm1
  have hq8 : q % 8 = 1 := q_mod_eight_of_dvd_sub_one hr hq1 hdvd
  obtain ⟨m, hm⟩ : ∃ m, q = 8 * m + 1 := by
    refine ⟨q / 8, ?_⟩
    have := Nat.div_add_mod q 8
    omega
  have hdy : (q + 1) / 2 = 4 * m + 1 := by rw [hm]; omega
  have hcard2 : Nat.card Fˣ / 2 = 32 * m * m + 8 * m := by
    rw [hcard, hm]
    have hsq : (8 * m + 1) * (8 * m + 1) = 2 * (32 * m * m + 8 * m) + 1 := by ring
    have h : (8 * m + 1) * (8 * m + 1) - 1 = 2 * (32 * m * m + 8 * m) := by omega
    rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hcd_y : (q - 1) * ((q + 1) / 2) = Nat.card Fˣ / 2 := by
    have hqm1 : q - 1 = 8 * m := by omega
    rw [hdy, hcard2, hqm1]
    ring
  have hy1 : y * (y ^ q)⁻¹ = -1 := by simpa only [autU_eq_pow hq y] using hy
  have hqeq : y ^ q = y ^ (q - 1) * y := by rw [← pow_succ, Nat.sub_add_cancel hq1]
  have hypow : y ^ (q - 1) = -1 := by
    rw [hqeq, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul] at hy1
    have := congrArg Inv.inv hy1
    simpa [inv_neg_one] using this
  have hodd : ¬ Even ((q + 1) / 2) := by
    rw [hdy]
    intro h
    obtain ⟨j, hj⟩ := h
    omega
  exact fun h => hodd ((isSquare_iff_even_of_pow_eq_neg_one h2 hcd_y hypow).mp h)

theorem isSquare_of_mul_autU (h2 : (2 : F) ≠ 0) {σ₀ : F ≃+* F} {q : ℕ}
    (hq : ∀ x : F, σ₀ x = x ^ q) (hcard : Nat.card Fˣ = q * q - 1) (hqodd : Odd q) {w : Fˣ}
    (hw : w * autU σ₀ w = 1) : IsSquare w := by
  have hwq : w ^ q = w⁻¹ := by
    rw [autU_eq_pow hq w] at hw
    have h : w ^ q * w = 1 := by rw [mul_comm]; exact hw
    exact mul_eq_one_iff_eq_inv.mp h
  have hwq1 : w ^ (q + 1) = 1 := by rw [pow_succ, hwq, inv_mul_cancel]
  obtain ⟨k, hk⟩ := hqodd
  have hcard2 : Nat.card Fˣ / 2 = 2 * k * (k + 1) := by
    rw [hcard, hk]
    have hsq : (2 * k + 1) * (2 * k + 1) = 2 * (2 * k * (k + 1)) + 1 := by ring
    have h : (2 * k + 1) * (2 * k + 1) - 1 = 2 * (2 * k * (k + 1)) := by omega
    rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hcd : (q + 1) * ((q - 1) / 2) = Nat.card Fˣ / 2 := by
    rw [hcard2, hk]
    have h1 : (2 * k + 1 - 1) / 2 = k := by omega
    rw [h1]
    ring
  have hmain : w ^ (Nat.card Fˣ / 2) = 1 := by
    rw [← hcd, pow_mul, hwq1, one_pow]
  exact (isSquare_iff_pow_eq_one h2 w).mpr hmain

theorem isSquare_of_autU_eq (h2 : (2 : F) ≠ 0) {σ₀ : F ≃+* F} {q : ℕ}
    (hq : ∀ x : F, σ₀ x = x ^ q) (hcard : Nat.card Fˣ = q * q - 1) (hqodd : Odd q) {w : Fˣ}
    (hw : autU σ₀ w = w) : IsSquare w := by
  have hwq : w ^ q = w := (autU_eq_pow hq w).symm.trans hw
  obtain ⟨k, hk⟩ := hqodd
  have hq1 : 1 ≤ q := by rw [hk]; omega
  have hwqm1 : w ^ (q - 1) = 1 := by
    have h : w ^ (q - 1) * w = 1 * w := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel hq1, hwq]
    exact mul_right_cancel h
  have hcard2 : Nat.card Fˣ / 2 = 2 * k * (k + 1) := by
    rw [hcard, hk]
    have hsq : (2 * k + 1) * (2 * k + 1) = 2 * (2 * k * (k + 1)) + 1 := by ring
    have h : (2 * k + 1) * (2 * k + 1) - 1 = 2 * (2 * k * (k + 1)) := by omega
    rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hcd : (q - 1) * ((q + 1) / 2) = Nat.card Fˣ / 2 := by
    rw [hcard2, hk]
    have h1 : 2 * k + 1 - 1 = 2 * k := by omega
    have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    rw [h1, h2]
  have hmain : w ^ (Nat.card Fˣ / 2) = 1 := by
    rw [← hcd, pow_mul, hwqm1, one_pow]
  exact (isSquare_iff_pow_eq_one h2 w).mpr hmain

theorem gD_quot_gD {σ₀ : F ≃+* F} (hσ₀2 : σ₀ * σ₀ = 1) (w y : Fˣ) :
    gD w σ₀ * (gD y σ₀)⁻¹ = gD (w * y⁻¹) 1 := by
  have hσinv : σ₀⁻¹ = σ₀ := inv_eq_of_mul_eq_one_right hσ₀2
  rw [gD_inv, hσinv, gD_mul_gD, hσ₀2, gD_eq_iff]
  refine ⟨?_, rfl⟩
  rw [autU_inv, ← autU_comp, hσ₀2, autU_one_aut]

theorem gA_quot_gA {σ₀ : F ≃+* F} (hσ₀2 : σ₀ * σ₀ = 1) (w y : Fˣ) :
    gA w σ₀ * (gA y σ₀)⁻¹ = gD (w * y⁻¹) 1 := by
  have hσinv : σ₀⁻¹ = σ₀ := inv_eq_of_mul_eq_one_right hσ₀2
  rw [gA_inv, hσinv, gA_mul_gA, hσ₀2, gD_eq_iff]
  refine ⟨?_, rfl⟩
  rw [← autU_comp, hσ₀2, autU_one_aut]

end Squares

section Pi4

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Q : Subgroup X} {r : ℕ}
  {p f : ℕ}

theorem not_inner_involution [Fact p.Prime] (E : PGamEmb X F)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h4 : 4 ≤ p ^ f) (hf : Even f) (hidx : (genFittingFStar X).index ≤ 2) (hr : 4 ≤ r)
    (hz : E.ρ (MulAut.conj (quatInvolution r e)) = SemidirectProduct.inl (pD (-1)))
    {σ₀ : F ≃+* F} (hσ₀1 : σ₀ ≠ 1) (hσ₀2 : σ₀ * σ₀ = 1)
    (hq : ∀ x : F, σ₀ x = x ^ (p ^ (f / 2))) {ι : PGammaL2 F} (hι : IsMon ι)
    (hι2 : ι * ι = 1) (hιr : ι.right = σ₀) : ∀ x : X, E.ρ (MulAut.conj x) ≠ ι := by
  intro x hx_eq
  have h2 : (2 : F) ≠ 0 := (field_facts (Fact.out : p.Prime) hp2 hF h4).2
  have hqodd : Odd (p ^ (f / 2)) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hcard : Nat.card Fˣ = p ^ (f / 2) * p ^ (f / 2) - 1 := card_units_eq_sq_sub_one hF hf
  have hcard4 : 4 ∣ Nat.card Fˣ := by
    rw [hcard]
    obtain ⟨k, hk⟩ := hqodd
    rw [hk]
    have hsq : (2 * k + 1) * (2 * k + 1) = 4 * (k * (k + 1)) + 1 := by ring
    exact ⟨k * (k + 1), by omega⟩
  obtain ⟨x₀, y, hx₀ord, _, hB⟩ :=
    quat_structure E e hF hp2 h4 hidx hr hz hσ₀1 hσ₀2
  let b : X := ((e.symm (QuaternionGroup.xa 0) : ↥Q) : X)
  have hbq : E.ρ (MulAut.conj b) = qEmb E e (QuaternionGroup.xa 0) := by rw [qEmb_apply]
  have hx_ne : (E.ρ (MulAut.conj x)).right ≠ 1 := by rw [hx_eq, hιr]; exact hσ₀1
  rcases hB with ⟨hBd, hxd, hyd⟩ | ⟨hBa, hxa, hya⟩
  · have hny : ¬ IsSquare y := not_isSquare_y_diag h2 hq hcard hr hx₀ord hxd hyd
    have hb_ne : (E.ρ (MulAut.conj b)).right ≠ 1 := by
      rw [hbq, hBd, gD_right]; exact hσ₀1
    have hql : (ι * (E.ρ (MulAut.conj b))⁻¹).left ∈ pslRange F := by
      have := (inner_quot_mem E hidx hb_ne hx_ne).2
      rwa [hx_eq] at this
    rcases hι with ⟨w, hw⟩ | ⟨w, hw⟩
    · rw [hιr] at hw
      have hww : w * autU σ₀ w = 1 := by
        have h := hι2
        rw [hw, gD_mul_self w σ₀ hσ₀2, ← gD_one_one, gD_eq_iff] at h
        exact h.1
      have hwsq : IsSquare w := isSquare_of_mul_autU h2 hq hcard hqodd hww
      have heq : ι * (E.ρ (MulAut.conj b))⁻¹ = gD (w * y⁻¹) 1 := by
        rw [hw, hbq, hBd, gD_quot_gD hσ₀2 w y]
      have hleft : (gD (w * y⁻¹) (1 : F ≃+* F)).left ∈ pslRange F := by rwa [← heq]
      have hwy : IsSquare (w * y⁻¹) :=
        (pD_mem_pslRange_iff (w * y⁻¹)).mp (by simpa using hleft)
      have hy_sq : IsSquare y := by
        have h1 : IsSquare ((w * y⁻¹)⁻¹ * w) := (isSquare_inv.mpr hwy).mul hwsq
        rwa [show (w * y⁻¹)⁻¹ * w = y by group] at h1
      exact hny hy_sq
    · rw [hιr] at hw
      have hww : w * (autU σ₀ w)⁻¹ = 1 := by
        have h := hι2
        rw [hw, gA_mul_self w σ₀ hσ₀2, ← gD_one_one, gD_eq_iff] at h
        exact h.1
      have hwfix : autU σ₀ w = w := (mul_inv_eq_one.mp hww).symm
      have hwsq : IsSquare w := isSquare_of_autU_eq h2 hq hcard hqodd hwfix
      have heq : ι * (E.ρ (MulAut.conj b))⁻¹ = gA (w * y) 1 := by
        rw [hw, hbq, hBd, third_diag_quot hσ₀2 w y]
      have hleft : (gA (w * y) (1 : F ≃+* F)).left ∈ pslRange F := by rwa [← heq]
      have hwy : IsSquare (w * y) :=
        (pA_mem_pslRange_iff_of_four_dvd hcard4 (w * y)).mp (by simpa using hleft)
      have hy_sq : IsSquare y := by
        have h1 : IsSquare (w⁻¹ * (w * y)) := (isSquare_inv.mpr hwsq).mul hwy
        rwa [show w⁻¹ * (w * y) = y by group] at h1
      exact hny hy_sq
  · have hny : ¬ IsSquare y := not_isSquare_y_anti h2 hq hcard hr hx₀ord hxa hya
    have hb_ne : (E.ρ (MulAut.conj b)).right ≠ 1 := by
      rw [hbq, hBa, gA_right]; exact hσ₀1
    have hql : (ι * (E.ρ (MulAut.conj b))⁻¹).left ∈ pslRange F := by
      have := (inner_quot_mem E hidx hb_ne hx_ne).2
      rwa [hx_eq] at this
    rcases hι with ⟨w, hw⟩ | ⟨w, hw⟩
    · rw [hιr] at hw
      have hww : w * autU σ₀ w = 1 := by
        have h := hι2
        rw [hw, gD_mul_self w σ₀ hσ₀2, ← gD_one_one, gD_eq_iff] at h
        exact h.1
      have hwsq : IsSquare w := isSquare_of_mul_autU h2 hq hcard hqodd hww
      have heq : ι * (E.ρ (MulAut.conj b))⁻¹ = gA (w * y) 1 := by
        rw [hw, hbq, hBa, third_anti_quot hσ₀2 w y]
      have hleft : (gA (w * y) (1 : F ≃+* F)).left ∈ pslRange F := by rwa [← heq]
      have hwy : IsSquare (w * y) :=
        (pA_mem_pslRange_iff_of_four_dvd hcard4 (w * y)).mp (by simpa using hleft)
      have hy_sq : IsSquare y := by
        have h1 : IsSquare (w⁻¹ * (w * y)) := (isSquare_inv.mpr hwsq).mul hwy
        rwa [show w⁻¹ * (w * y) = y by group] at h1
      exact hny hy_sq
    · rw [hιr] at hw
      have hww : w * (autU σ₀ w)⁻¹ = 1 := by
        have h := hι2
        rw [hw, gA_mul_self w σ₀ hσ₀2, ← gD_one_one, gD_eq_iff] at h
        exact h.1
      have hwfix : autU σ₀ w = w := (mul_inv_eq_one.mp hww).symm
      have hwsq : IsSquare w := isSquare_of_autU_eq h2 hq hcard hqodd hwfix
      have heq : ι * (E.ρ (MulAut.conj b))⁻¹ = gD (w * y⁻¹) 1 := by
        rw [hw, hbq, hBa, gA_quot_gA hσ₀2 w y]
      have hleft : (gD (w * y⁻¹) (1 : F ≃+* F)).left ∈ pslRange F := by rwa [← heq]
      have hwy : IsSquare (w * y⁻¹) :=
        (pD_mem_pslRange_iff (w * y⁻¹)).mp (by simpa using hleft)
      have hy_sq : IsSquare y := by
        have h1 : IsSquare ((w * y⁻¹)⁻¹ * w) := (isSquare_inv.mpr hwy).mul hwsq
        rwa [show (w * y⁻¹)⁻¹ * w = y by group] at h1
      exact hny hy_sq

theorem z2BigModelPi4_holds (r : ℕ) : Z2BigModelPi4 r := by
  intro hr X _ _ p f hL Q e H _ hHQ g hgH K hK hord
  obtain ⟨F, _, _, hF, h4, hp, E, hz⟩ :=
    exists_normalized_emb hL.simple hL.odd hL.even hL.model
      (quatInvolution_sq hr e) (quatInvolution_ne_one hr e)
      (quatInvolution_mem_fstar hL.index hr e)
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : F) ≠ 0 := (field_facts hp hL.odd hF h4).2
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hF h4
    omega
  obtain ⟨σ₀, hσ₀1, hσ₀2, hq⟩ := exists_frob_half hF hL.even hf0
  have hGcomm : E.ρ g * ubar F = ubar F * E.ρ g :=
    rho_comm_ubar E hr e hz (hHQ g hgH)
  have hhmon : IsMon ((E.ρ g) ^ 2 ^ (K - 2)) := by
    rw [isMon_iff_comm_ubar h2]
    exact ((show Commute (E.ρ g) (ubar F) from hGcomm).pow_left (2 ^ (K - 2))).eq
  let h : PGammaL2 F := (E.ρ g) ^ 2 ^ (K - 2)
  obtain ⟨w, hw⟩ := exists_gD_sq hhmon
  let ι : MulAut X := g ^ 2 ^ (K - 1)
  have hmul : 2 ^ (K - 2) * 2 = 2 ^ (K - 1) := by
    rw [← pow_succ]
    congr 1
    omega
  have h2K1 : 2 ^ (K - 1) * 2 = 2 ^ K := by
    rw [← pow_succ]
    congr 1
    omega
  have hpow_eq : h ^ 2 = E.ρ ι := by
    change ((E.ρ g) ^ 2 ^ (K - 2)) ^ 2 = E.ρ ι
    rw [← pow_mul, hmul, ← map_pow]
  have hEι_form : E.ρ ι = gD w (h.right ^ 2) := hpow_eq.symm.trans hw
  have hIsMon : IsMon (E.ρ ι) := by
    rw [hEι_form]
    exact isMon_gD w (h.right ^ 2)
  have hι2 : ι * ι = 1 := by
    change g ^ 2 ^ (K - 1) * g ^ 2 ^ (K - 1) = 1
    rw [← pow_two, ← pow_mul, h2K1, ← hord, pow_orderOf_eq_one]
  have hι_ne : ι ≠ 1 := by
    intro h1
    exact (pow_ne_one_of_lt_orderOf (n := 2 ^ (K - 1)) (pow_ne_zero _ (by norm_num))
      (by rw [hord]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))) h1
  have hEι2 : E.ρ ι * E.ρ ι = 1 := by rw [← map_mul, hι2, map_one]
  have hEr_sq : (E.ρ ι).right * (E.ρ ι).right = 1 := by
    have := congrArg SemidirectProduct.right hEι2
    simpa [SemidirectProduct.mul_right] using this
  have hEr_cases : (E.ρ ι).right = 1 ∨ (E.ρ ι).right = σ₀ :=
    ringAut_sq_eq_one hF hL.odd h4 hσ₀1 hσ₀2 hEr_sq
  rcases hEr_cases with hEr1 | hErσ
  · left
    have hhr : h.right ^ 2 = 1 := by rw [← right_pow h 2, hpow_eq, hEr1]
    have hEι_gD : E.ρ ι = gD w 1 := by rw [hEι_form, hhr]
    have hww : w ^ 2 = 1 := by
      have hh := hEι2
      rw [hEι_gD, gD_mul_gD, autU_one_aut, one_mul, ← gD_one_one, gD_eq_iff] at hh
      rw [pow_two]
      exact hh.1
    have hw_ne : w ≠ 1 := by
      intro hw1
      apply hι_ne
      apply E.inj
      rw [hEι_gD, hw1, gD_one_one, map_one]
    have hw_neg : w = -1 := by
      rcases (unit_sq_eq_one_iff w).mp hww with h1 | h1
      · exact absurd h1 hw_ne
      · exact h1
    have hub : ubar F = E.ρ (MulAut.conj (quatInvolution r e)) := by
      rw [ubar_eq, ← inl_pD_eq, ← hz]
    apply E.inj
    change E.ρ ι = E.ρ (MulAut.conj (quatInvolution r e))
    rw [hEι_gD, hw_neg, ← hub, ubar_eq]
  · right
    intro hmem
    obtain ⟨x, hx⟩ := hmem
    exact not_inner_involution E e hF hL.odd h4 hL.even hL.index hr hz hσ₀1 hσ₀2 hq
      hIsMon hEι2 hErσ x (by rw [hx])

end Pi4

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
