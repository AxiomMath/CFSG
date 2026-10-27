module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big10
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big11

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG.GorensteinWalter CFSG.ClassicalInvolution.Q3.TL4.Z2W

theorem mul_inv_eq_mul_inv_of_mul_inv_eq_mul {G : Type} [CommGroup G] {a b c d : G}
    (h : a * d⁻¹ = c * b) : a * b⁻¹ = c * d := by
  rw [mul_inv_eq_iff_eq_mul] at h
  rw [mul_inv_eq_iff_eq_mul, h, mul_assoc, mul_assoc, mul_comm b d]

theorem mul_eq_mul_inv_of_mul_eq_mul_inv {G : Type} [CommGroup G] {a b c d : G}
    (h : a * d = c * b⁻¹) : a * b = c * d⁻¹ := by
  have hc : c = a * d * b := by rw [h, mul_assoc, inv_mul_cancel, mul_one]
  rw [hc, mul_assoc a d b, mul_assoc a (d * b) d⁻¹, mul_comm d b, mul_assoc b d d⁻¹,
    mul_inv_cancel, mul_one]

section Classify

variable {F : Type} [Field F] [Finite F]

theorem autU_fix_of_comm_A {g : PGammaL2 F} (hg : IsMon g) {x₀ : Fˣ}
    (hA : g * gD x₀ 1 = gD x₀ 1 * g) :
    autU g.right x₀ = x₀ ∨ autU g.right x₀ = x₀⁻¹ := by
  rcases hg with ⟨u, hu⟩ | ⟨u, hu⟩
  · rw [hu] at hA
    simp only [gD_right, gD_mul_gD, mul_one, one_mul, autU_one_aut] at hA
    obtain ⟨h1, -⟩ := gD_eq_iff.mp hA
    left
    exact mul_left_cancel (h1.trans (mul_comm x₀ u))
  · rw [hu] at hA
    simp only [gD_right, gA_right, gA_mul_gD, gD_mul_gA, mul_one, one_mul, autU_one_aut] at hA
    obtain ⟨h1, -⟩ := gA_eq_iff.mp hA
    right
    have h2 : (autU g.right x₀)⁻¹ = x₀ := mul_left_cancel (h1.trans (mul_comm x₀ u))
    simpa using congrArg Inv.inv h2

theorem centralizer_diag (h2 : (2 : F) ≠ 0) {σ₀ : F ≃+* F} (hσ₀2 : σ₀ * σ₀ = 1)
    (hσ₀ : ∀ σ : F ≃+* F, σ * σ = 1 → σ = 1 ∨ σ = σ₀) {q : ℕ}
    (hq : ∀ x : F, σ₀ x = x ^ q) {r : ℕ} (hr : 4 ≤ r) {x₀ y : Fˣ}
    (hx₀ : orderOf x₀ = 2 ^ (r - 1)) (hx : autU σ₀ x₀ = x₀⁻¹) (hy : y * autU σ₀ y = -1)
    {g : PGammaL2 F} (hg : IsMon g) (hgr : g.right * g.right = 1)
    (hA : g * gD x₀ 1 = gD x₀ 1 * g) (hB : g * gD y σ₀ = gD y σ₀ * g) {k : ℕ}
    (hk : g ^ 2 ^ k = 1) :
    g = 1 ∨ g = ubar F ∨ ∃ u : Fˣ, g = gA u σ₀ ∧ u * (autU σ₀ u)⁻¹ = -1 := by
  have hx₀ne : x₀ ≠ x₀⁻¹ := by
    intro h
    have h2x : x₀ ^ 2 = 1 := by
      have := congrArg (fun z => x₀ * z) h
      rw [sq, this, mul_inv_cancel]
    have hdvd : orderOf x₀ ∣ 2 := orderOf_dvd_of_pow_eq_one h2x
    rw [hx₀] at hdvd
    have hle : 2 ^ (r - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have h8 : 8 ≤ 2 ^ (r - 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hσcases : g.right = 1 ∨ g.right = σ₀ := hσ₀ g.right hgr
  rcases hg with ⟨u, hu⟩ | ⟨u, hu⟩
  · rw [hu] at hA hB hk
    simp only [gD_right, gD_mul_gD, mul_one, one_mul, autU_one_aut] at hA
    obtain ⟨hfix, -⟩ := gD_eq_iff.mp hA
    have hfix' : autU g.right x₀ = x₀ := mul_left_cancel (hfix.trans (mul_comm x₀ u))
    rcases hσcases with hgr1 | hgrσ
    · rw [hgr1] at hB hk
      simp only [gD_mul_gD, autU_one_aut, one_mul, mul_one] at hB
      obtain ⟨hB1, -⟩ := gD_eq_iff.mp hB
      have huq : autU σ₀ u = u :=
        (mul_right_cancel (hB1.trans (mul_comm y (autU σ₀ u)))).symm
      have huqp : u ^ q = u := (autU_eq_pow hq u).symm.trans huq
      rw [gD_one_pow, ← gD_one_one] at hk
      have huk : u ^ 2 ^ k = 1 := (gD_eq_iff.mp hk).1
      have hxq : x₀ ^ q = x₀⁻¹ := (autU_eq_pow hq x₀).symm.trans hx
      have hxq1 : x₀ ^ (q + 1) = 1 := by rw [pow_succ, hxq, inv_mul_cancel]
      have hdvd : 2 ^ (r - 1) ∣ q + 1 := by
        rw [← hx₀]
        exact orderOf_dvd_of_pow_eq_one hxq1
      have hq8 : q % 8 = 7 := q_mod_eight_of_dvd_add_one hr hdvd
      have hq1 : 1 ≤ q := by omega
      have huqm1 : u ^ (q - 1) = 1 := by
        have h : u ^ (q - 1) * u = 1 * u := by
          rw [one_mul, ← pow_succ, Nat.sub_add_cancel hq1, huqp]
        exact mul_right_cancel h
      have hc4 : (q - 1) % 4 = 2 := by omega
      rcases unit_eq_neg_one_or_one_of_pow hc4 huqm1 huk with h1 | h1
      · left
        rw [hu, hgr1, h1, gD_one_one]
      · right; left
        rw [hu, hgr1, h1, ubar_eq]
    · rw [hgrσ] at hfix'
      exact absurd (hfix'.symm.trans hx) hx₀ne
  · rw [hu] at hA hB
    simp only [gA_right, gA_mul_gD, gD_mul_gA, mul_one, one_mul, autU_one_aut] at hA
    obtain ⟨h1, -⟩ := gA_eq_iff.mp hA
    have hanti : autU g.right x₀ = x₀⁻¹ := by
      have h2' : (autU g.right x₀)⁻¹ = x₀ := mul_left_cancel (h1.trans (mul_comm x₀ u))
      simpa using congrArg Inv.inv h2'
    rcases hσcases with hgr1 | hgrσ
    · rw [hgr1, autU_one_aut] at hanti
      exact absurd hanti hx₀ne
    · rw [hgrσ] at hB
      simp only [gA_mul_gD, gD_mul_gA, hσ₀2, one_mul, mul_one] at hB
      obtain ⟨hB1, -⟩ := gA_eq_iff.mp hB
      have hkey : u * (autU σ₀ u)⁻¹ = y * autU σ₀ y :=
        mul_inv_eq_mul_inv_of_mul_inv_eq_mul hB1
      refine Or.inr (Or.inr ⟨u, ?_, ?_⟩)
      · rw [hu, hgrσ]
      · rw [hkey, hy]

theorem centralizer_anti (h2 : (2 : F) ≠ 0) {σ₀ : F ≃+* F} (hσ₀2 : σ₀ * σ₀ = 1)
    (hσ₀ : ∀ σ : F ≃+* F, σ * σ = 1 → σ = 1 ∨ σ = σ₀) {q : ℕ}
    (hq : ∀ x : F, σ₀ x = x ^ q) {r : ℕ} (hr : 4 ≤ r) {x₀ y : Fˣ}
    (hx₀ : orderOf x₀ = 2 ^ (r - 1)) (hx : autU σ₀ x₀ = x₀) (hy : y * (autU σ₀ y)⁻¹ = -1)
    {g : PGammaL2 F} (hg : IsMon g) (hgr : g.right * g.right = 1)
    (hA : g * gD x₀ 1 = gD x₀ 1 * g) (hB : g * gA y σ₀ = gA y σ₀ * g) {k : ℕ}
    (hk : g ^ 2 ^ k = 1) :
    g = 1 ∨ g = ubar F ∨ ∃ u : Fˣ, g = gD u σ₀ ∧ u * autU σ₀ u = -1 := by
  have hx₀ne : x₀ ≠ x₀⁻¹ := by
    intro h
    have h2x : x₀ ^ 2 = 1 := by
      have := congrArg (fun z => x₀ * z) h
      rw [sq, this, mul_inv_cancel]
    have hdvd : orderOf x₀ ∣ 2 := orderOf_dvd_of_pow_eq_one h2x
    rw [hx₀] at hdvd
    have hle : 2 ^ (r - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have h8 : 8 ≤ 2 ^ (r - 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
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
  have hσcases : g.right = 1 ∨ g.right = σ₀ := hσ₀ g.right hgr
  rcases hg with ⟨u, hu⟩ | ⟨u, hu⟩
  · rw [hu] at hB hk
    rcases hσcases with hgr1 | hgrσ
    · rw [hgr1] at hB hk
      simp only [gD_mul_gA, gA_mul_gD, autU_one_aut, one_mul, mul_one] at hB
      obtain ⟨hB1, -⟩ := gA_eq_iff.mp hB
      have hu_eq : u = (autU σ₀ u)⁻¹ :=
        mul_right_cancel (by rw [hB1, mul_comm y (autU σ₀ u)⁻¹])
      have hu_mul : u * autU σ₀ u = 1 := by
        have := congrArg (fun z => z * autU σ₀ u) hu_eq
        rwa [inv_mul_cancel] at this
      have hu_c : u ^ (q + 1) = 1 := by
        rw [pow_succ, mul_comm (u ^ q) u, ← hu_mul, autU_eq_pow hq u]
      rw [gD_one_pow, ← gD_one_one] at hk
      have huk : u ^ 2 ^ k = 1 := (gD_eq_iff.mp hk).1
      have hc4 : (q + 1) % 4 = 2 := by omega
      rcases unit_eq_neg_one_or_one_of_pow hc4 hu_c huk with h1 | h1
      · left
        rw [hu, hgr1, h1, gD_one_one]
      · right; left
        rw [hu, hgr1, h1, ubar_eq]
    · rw [hgrσ] at hB
      simp only [gD_mul_gA, gA_mul_gD, hσ₀2, one_mul, mul_one] at hB
      obtain ⟨hB1, -⟩ := gA_eq_iff.mp hB
      have hkey : u * autU σ₀ u = y * (autU σ₀ y)⁻¹ :=
        mul_eq_mul_inv_of_mul_eq_mul_inv hB1
      refine Or.inr (Or.inr ⟨u, ?_, ?_⟩)
      · rw [hu, hgrσ]
      · rw [hkey, hy]
  · rw [hu] at hA hB
    simp only [gA_right, gA_mul_gD, gD_mul_gA, mul_one, one_mul, autU_one_aut] at hA
    obtain ⟨h1, -⟩ := gA_eq_iff.mp hA
    have hanti : autU g.right x₀ = x₀⁻¹ := by
      have h2' : (autU g.right x₀)⁻¹ = x₀ := mul_left_cancel (h1.trans (mul_comm x₀ u))
      simpa using congrArg Inv.inv h2'
    rcases hσcases with hgr1 | hgrσ
    · rw [hgr1, autU_one_aut] at hanti
      exact absurd hanti hx₀ne
    · rw [hgrσ] at hanti
      exact absurd (hx.symm.trans hanti) hx₀ne

theorem not_isSquare_third_diag (h2 : (2 : F) ≠ 0) {σ₀ : F ≃+* F} {q : ℕ}
    (hq : ∀ x : F, σ₀ x = x ^ q) (hcard : Nat.card Fˣ = q * q - 1) {r : ℕ} (hr : 4 ≤ r)
    {x₀ y u : Fˣ} (hx₀ : orderOf x₀ = 2 ^ (r - 1)) (hx : autU σ₀ x₀ = x₀⁻¹)
    (hy : y * autU σ₀ y = -1) (hu : u * (autU σ₀ u)⁻¹ = -1) : ¬ IsSquare (-(u * y)) := by
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
  have hdy : (q - 1) / 2 = 4 * m + 3 := by
    rw [hm]
    omega
  have hdu : (q + 1) / 2 = 4 * m + 4 := by
    rw [hm]
    omega
  have hcard2 : Nat.card Fˣ / 2 = 32 * m * m + 56 * m + 24 := by
    rw [hcard, hm]
    have hsq : (8 * m + 7) * (8 * m + 7) = 2 * (32 * m * m + 56 * m + 24) + 1 := by
      ring
    have h : (8 * m + 7) * (8 * m + 7) - 1 = 2 * (32 * m * m + 56 * m + 24) := by
      omega
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
  have hny : ¬ IsSquare y :=
    fun h => hodd ((isSquare_iff_even_of_pow_eq_neg_one h2 hcd_y hy_pow).mp h)
  have hu1 : u * (u ^ q)⁻¹ = -1 := by simpa only [autU_eq_pow hq u] using hu
  have hqeq : u ^ q = u ^ (q - 1) * u := by rw [← pow_succ, Nat.sub_add_cancel hq1]
  have hupow : u ^ (q - 1) = -1 := by
    rw [hqeq, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul] at hu1
    have := congrArg Inv.inv hu1
    simpa [inv_neg_one] using this
  have hcd_u : (q - 1) * ((q + 1) / 2) = Nat.card Fˣ / 2 := by
    have hqm1 : q - 1 = 8 * m + 6 := by omega
    rw [hdu, hcard2, hqm1]
    ring
  have heven : Even ((q + 1) / 2) := by
    rw [hdu]
    exact ⟨2 * m + 2, by ring⟩
  have hsu : IsSquare u := (isSquare_iff_even_of_pow_eq_neg_one h2 hcd_u hupow).mpr heven
  have hsneg : IsSquare (-1 : Fˣ) := by
    have hiff := isSquare_iff_even_of_pow_eq_neg_one (F := F) h2 (u := -1) (c := 1)
      (d := Nat.card Fˣ / 2) (by rw [one_mul]) (pow_one (-1))
    rw [hcard2] at hiff
    refine hiff.mpr ?_
    have hn : 32 * m * m + 56 * m + 24 =
        (16 * m * m + 28 * m + 12) + (16 * m * m + 28 * m + 12) := by ring
    rw [hn]
    exact ⟨16 * m * m + 28 * m + 12, rfl⟩
  have huy : ¬ IsSquare (u * y) := not_isSquare_mul_of_isSquare h2 hsu hny
  have hfinal : ¬ IsSquare ((-1 : Fˣ) * (u * y)) :=
    not_isSquare_mul_of_isSquare h2 hsneg huy
  have hneg : -(u * y) = (-1 : Fˣ) * (u * y) := by
    ext
    simp
  rwa [← hneg] at hfinal

theorem not_isSquare_third_anti (h2 : (2 : F) ≠ 0) {σ₀ : F ≃+* F} {q : ℕ}
    (hq : ∀ x : F, σ₀ x = x ^ q) (hcard : Nat.card Fˣ = q * q - 1) {r : ℕ} (hr : 4 ≤ r)
    {x₀ y u : Fˣ} (hx₀ : orderOf x₀ = 2 ^ (r - 1)) (hx : autU σ₀ x₀ = x₀)
    (hy : y * (autU σ₀ y)⁻¹ = -1) (hu : u * autU σ₀ u = -1) : ¬ IsSquare (-(u * y)) := by
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
  have hdy : (q + 1) / 2 = 4 * m + 1 := by
    rw [hm]
    omega
  have hdu : (q - 1) / 2 = 4 * m := by
    rw [hm]
    omega
  have hcard2 : Nat.card Fˣ / 2 = 32 * m * m + 8 * m := by
    rw [hcard, hm]
    have hsq : (8 * m + 1) * (8 * m + 1) = 2 * (32 * m * m + 8 * m) + 1 := by
      ring
    have h : (8 * m + 1) * (8 * m + 1) - 1 = 2 * (32 * m * m + 8 * m) := by
      omega
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
  have hny : ¬ IsSquare y :=
    fun h => hodd ((isSquare_iff_even_of_pow_eq_neg_one h2 hcd_y hypow).mp h)
  have hu_pow : u ^ (q + 1) = -1 := by
    rw [pow_succ, mul_comm (u ^ q) u, ← hu, autU_eq_pow hq u]
  have hcd_u : (q + 1) * ((q - 1) / 2) = Nat.card Fˣ / 2 := by
    rw [hdu, hcard2, hm]
    ring
  have heven : Even ((q - 1) / 2) := by
    rw [hdu]
    exact ⟨2 * m, by ring⟩
  have hsu : IsSquare u := (isSquare_iff_even_of_pow_eq_neg_one h2 hcd_u hu_pow).mpr heven
  have hsneg : IsSquare (-1 : Fˣ) := by
    have hiff := isSquare_iff_even_of_pow_eq_neg_one (F := F) h2 (u := -1) (c := 1)
      (d := Nat.card Fˣ / 2) (by rw [one_mul]) (pow_one (-1))
    rw [hcard2] at hiff
    refine hiff.mpr ?_
    have hn : 32 * m * m + 8 * m =
        (16 * m * m + 4 * m) + (16 * m * m + 4 * m) := by ring
    rw [hn]
    exact ⟨16 * m * m + 4 * m, rfl⟩
  have huy : ¬ IsSquare (u * y) := not_isSquare_mul_of_isSquare h2 hsu hny
  have hfinal : ¬ IsSquare ((-1 : Fˣ) * (u * y)) :=
    not_isSquare_mul_of_isSquare h2 hsneg huy
  have hneg : -(u * y) = (-1 : Fˣ) * (u * y) := by
    ext
    simp
  rwa [← hneg] at hfinal

theorem third_diag_quot {σ₀ : F ≃+* F} (hσ₀2 : σ₀ * σ₀ = 1) (u y : Fˣ) :
    gA u σ₀ * (gD y σ₀)⁻¹ = gA (u * y) 1 := by
  have hσinv : σ₀⁻¹ = σ₀ := inv_eq_of_mul_eq_one_right hσ₀2
  rw [gD_inv, hσinv, gA_mul_gD, hσ₀2, gA_eq_iff]
  refine ⟨?_, rfl⟩
  rw [autU_inv, inv_inv, ← autU_comp, hσ₀2, autU_one_aut]

theorem third_anti_quot {σ₀ : F ≃+* F} (hσ₀2 : σ₀ * σ₀ = 1) (u y : Fˣ) :
    gD u σ₀ * (gA y σ₀)⁻¹ = gA (u * y) 1 := by
  have hσinv : σ₀⁻¹ = σ₀ := inv_eq_of_mul_eq_one_right hσ₀2
  rw [gA_inv, hσinv, gD_mul_gA, hσ₀2, gA_eq_iff]
  refine ⟨?_, rfl⟩
  rw [← autU_comp, hσ₀2, autU_one_aut]

end Classify

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
