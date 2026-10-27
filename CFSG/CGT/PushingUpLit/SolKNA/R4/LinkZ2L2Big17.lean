module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big16

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section Twist

variable {F : Type} [Field F] [Finite F]

theorem not_isSquare_of_generator (h2 : (2 : F) ≠ 0) {γ : Fˣ}
    (hγ : ∀ x : Fˣ, x ∈ Subgroup.zpowers γ) : ¬ IsSquare γ := by
  have hord : orderOf γ = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hγ
  intro hs
  have hpow : γ ^ (Nat.card Fˣ / 2) = 1 := (isSquare_iff_pow_eq_one h2 γ).mp hs
  have hdvd : orderOf γ ∣ Nat.card Fˣ / 2 := orderOf_dvd_of_pow_eq_one hpow
  rw [hord] at hdvd
  have h2dvd : 2 ∣ Nat.card Fˣ := by
    rw [← orderOf_units_neg_one h2]
    exact orderOf_dvd_natCard (-1 : Fˣ)
  have hcardpos : 0 < Nat.card Fˣ := Nat.card_pos
  have hhalfpos : 0 < Nat.card Fˣ / 2 :=
    Nat.div_pos (Nat.le_of_dvd hcardpos h2dvd) (by norm_num)
  have hle : Nat.card Fˣ ≤ Nat.card Fˣ / 2 := Nat.le_of_dvd hhalfpos hdvd
  have hlt : Nat.card Fˣ / 2 < Nat.card Fˣ :=
    Nat.div_lt_self hcardpos (by norm_num : 1 < 2)
  omega

theorem two_mul_dvd_orderOf_gA {σ₀ : F ≃+* F} (hσ₀1 : σ₀ ≠ 1) (hσ₀2 : σ₀ * σ₀ = 1) {q : ℕ}
    (hq : ∀ x : F, σ₀ x = x ^ q) (hcard : Nat.card Fˣ = q * q - 1) (hq3 : 3 ≤ q) {γ : Fˣ}
    (hγ : ∀ x : Fˣ, x ∈ Subgroup.zpowers γ) : 2 * (q + 1) ∣ orderOf (gA γ σ₀) := by
  have hσord : orderOf σ₀ = 2 := by
    exact orderOf_eq_prime (by rw [sq]; exact hσ₀2) hσ₀1
  let g : PGammaL2 F := gA γ σ₀
  let n : ℕ := orderOf g
  have hgn : g ^ n = 1 := pow_orderOf_eq_one g
  have hright : σ₀ ^ n = 1 := by
    have h := congrArg SemidirectProduct.right hgn
    rw [right_pow] at h
    simpa [g] using h
  have h2n : 2 ∣ n := by
    rw [← hσord]
    exact orderOf_dvd_of_pow_eq_one hright
  obtain ⟨j, hj⟩ := h2n
  have hgn2 : g ^ (2 * j) = 1 := by rw [← hj]; exact hgn
  have hgj : (g ^ 2) ^ j = 1 := by rw [← pow_mul, hgn2]
  have hg2 : g ^ 2 = gD (γ * (autU σ₀ γ)⁻¹) 1 := by
    change (gA γ σ₀) ^ 2 = gD (γ * (autU σ₀ γ)⁻¹) 1
    rw [gA_sq, pow_two, hσ₀2]
  have hvj : (γ * (autU σ₀ γ)⁻¹) ^ j = 1 := by
    have h : gD ((γ * (autU σ₀ γ)⁻¹) ^ j) (1 : F ≃+* F) = gD (1 : Fˣ) 1 := by
      rw [gD_one_one, ← gD_one_pow, ← hgj, hg2]
    exact (gD_eq_iff.mp h).1
  have hq1 : 1 ≤ q := by omega
  have hordγ : orderOf γ = q * q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, hcard]
  have hfac : (q - 1) * (q + 1) = q * q - 1 := by
    have h : q * q = (q - 1) * (q + 1) + 1 := by
      have hq' : q = (q - 1) + 1 := by omega
      have h1 : q + 1 = (q - 1) + 2 := by omega
      calc q * q = ((q - 1) + 1) * ((q - 1) + 1) := by conv_lhs => rw [hq']
        _ = (q - 1) * ((q - 1) + 2) + 1 := by ring
        _ = (q - 1) * (q + 1) + 1 := by rw [← h1]
    omega
  have hposq : 0 < q - 1 := by omega
  have hne : q - 1 ≠ 0 := hposq.ne'
  have hdvd : q - 1 ∣ orderOf γ := by
    rw [hordγ]
    exact ⟨q + 1, hfac.symm⟩
  have hdiv : (q * q - 1) / (q - 1) = q + 1 := by
    rw [← hfac]
    exact Nat.mul_div_cancel_left (q + 1) hposq
  have hv_inv : (γ * (autU σ₀ γ)⁻¹)⁻¹ = γ ^ (q - 1) := by
    have hqeq : γ ^ q = γ ^ (q - 1) * γ := by
      rw [← pow_succ, Nat.sub_add_cancel hq1]
    rw [autU_eq_pow hq γ, mul_inv_rev, inv_inv, hqeq, mul_assoc, mul_inv_cancel, mul_one]
  have hordv : orderOf (γ * (autU σ₀ γ)⁻¹) = q + 1 := by
    rw [← orderOf_inv (γ * (autU σ₀ γ)⁻¹), hv_inv]
    rw [orderOf_pow_of_dvd hne hdvd, hordγ, hdiv]
  have hqv : q + 1 ∣ j := by
    rw [← hordv]
    exact orderOf_dvd_of_pow_eq_one hvj
  obtain ⟨k, hk⟩ := hqv
  have h2j : 2 * (q + 1) ∣ 2 * j := by
    rw [hk]
    exact ⟨k, by ring⟩
  show 2 * (q + 1) ∣ n
  rw [hj]
  exact h2j

theorem two_mul_dvd_orderOf_gD {σ₀ : F ≃+* F} (hσ₀1 : σ₀ ≠ 1) (hσ₀2 : σ₀ * σ₀ = 1) {q : ℕ}
    (hq : ∀ x : F, σ₀ x = x ^ q) (hcard : Nat.card Fˣ = q * q - 1) (hq3 : 3 ≤ q) {γ : Fˣ}
    (hγ : ∀ x : Fˣ, x ∈ Subgroup.zpowers γ) : 2 * (q - 1) ∣ orderOf (gD γ σ₀) := by
  have hσord : orderOf σ₀ = 2 := by
    exact orderOf_eq_prime (by rw [sq]; exact hσ₀2) hσ₀1
  let g : PGammaL2 F := gD γ σ₀
  let n : ℕ := orderOf g
  have hgn : g ^ n = 1 := pow_orderOf_eq_one g
  have hright : σ₀ ^ n = 1 := by
    have h := congrArg SemidirectProduct.right hgn
    rw [right_pow] at h
    simpa [g] using h
  have h2n : 2 ∣ n := by
    rw [← hσord]
    exact orderOf_dvd_of_pow_eq_one hright
  obtain ⟨j, hj⟩ := h2n
  have hgn2 : g ^ (2 * j) = 1 := by rw [← hj]; exact hgn
  have hgj : (g ^ 2) ^ j = 1 := by rw [← pow_mul, hgn2]
  have hg2 : g ^ 2 = gD (γ * autU σ₀ γ) 1 := by
    change (gD γ σ₀) ^ 2 = gD (γ * autU σ₀ γ) 1
    rw [sq, gD_mul_gD, hσ₀2]
  have hvj : (γ * autU σ₀ γ) ^ j = 1 := by
    have h : gD ((γ * autU σ₀ γ) ^ j) (1 : F ≃+* F) = gD (1 : Fˣ) 1 := by
      rw [gD_one_one, ← gD_one_pow, ← hgj, hg2]
    exact (gD_eq_iff.mp h).1
  have hq1 : 1 ≤ q := by omega
  have hordγ : orderOf γ = q * q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, hcard]
  have hfac : (q + 1) * (q - 1) = q * q - 1 := by
    have h : q * q = (q + 1) * (q - 1) + 1 := by
      have hq' : q = (q - 1) + 1 := by omega
      have h1 : q + 1 = (q - 1) + 2 := by omega
      calc q * q = ((q - 1) + 1) * ((q - 1) + 1) := by conv_lhs => rw [hq']
        _ = (q - 1) * ((q - 1) + 2) + 1 := by ring
        _ = (q + 1) * (q - 1) + 1 := by
              rw [← h1]
              ring
    omega
  have hposq : 0 < q + 1 := by omega
  have hne : q + 1 ≠ 0 := by omega
  have hdvd : q + 1 ∣ orderOf γ := by
    rw [hordγ]
    exact ⟨q - 1, hfac.symm⟩
  have hdiv : (q * q - 1) / (q + 1) = q - 1 := by
    rw [← hfac]
    exact Nat.mul_div_cancel_left (q - 1) hposq
  have hv_eq : γ * autU σ₀ γ = γ ^ (q + 1) := by
    rw [autU_eq_pow hq γ, mul_comm, ← pow_succ]
  have hordv : orderOf (γ * autU σ₀ γ) = q - 1 := by
    rw [hv_eq, orderOf_pow_of_dvd hne hdvd, hordγ, hdiv]
  have hqv : q - 1 ∣ j := by
    rw [← hordv]
    exact orderOf_dvd_of_pow_eq_one hvj
  obtain ⟨k, hk⟩ := hqv
  have h2j : 2 * (q - 1) ∣ 2 * j := by
    rw [hk]
    exact ⟨k, by ring⟩
  show 2 * (q - 1) ∣ n
  rw [hj]
  exact h2j

theorem two_pow_dvd_add_one_of_big {q r : ℕ} (hq8 : q % 8 = 7) (hbig : 2 ^ (r + 1) ∣ q * q - 1) :
    2 ^ r ∣ q + 1 := by
  obtain ⟨m, hm⟩ : ∃ m, q = 8 * m + 7 := by
    refine ⟨q / 8, ?_⟩
    have := Nat.div_add_mod q 8
    omega
  have hfac : q * q - 1 = 2 * ((4 * m + 3) * (q + 1)) := by
    have hq1 : 1 ≤ q := by omega
    have h : q * q = 2 * ((4 * m + 3) * (q + 1)) + 1 := by
      rw [hm]
      ring
    omega
  rw [hfac] at hbig
  rw [pow_succ, mul_comm (2 ^ r) 2] at hbig
  have hbig' : 2 ^ r ∣ (4 * m + 3) * (q + 1) :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) hbig
  have hodd : Odd (4 * m + 3) := ⟨2 * m + 1, by ring⟩
  have hcop : Nat.Coprime (2 ^ r) (4 * m + 3) :=
    Nat.Coprime.pow_left r (Nat.coprime_two_left.mpr hodd)
  exact hcop.dvd_of_dvd_mul_left hbig'

theorem two_pow_dvd_sub_one_of_big {q r : ℕ} (hq8 : q % 8 = 1) (hbig : 2 ^ (r + 1) ∣ q * q - 1) :
    2 ^ r ∣ q - 1 := by
  obtain ⟨m, hm⟩ : ∃ m, q = 8 * m + 1 := by
    refine ⟨q / 8, ?_⟩
    have := Nat.div_add_mod q 8
    omega
  have hfac : q * q - 1 = 2 * ((4 * m + 1) * (q - 1)) := by
    have hq1 : 1 ≤ q := by omega
    have h : q * q = 2 * ((4 * m + 1) * (q - 1)) + 1 := by
      rw [hm]
      have hsub : (8 * m + 1) - 1 = 8 * m := by omega
      rw [hsub]
      ring
    omega
  rw [hfac] at hbig
  rw [pow_succ, mul_comm (2 ^ r) 2] at hbig
  have hbig' : 2 ^ r ∣ (4 * m + 1) * (q - 1) :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) hbig
  have hodd : Odd (4 * m + 1) := ⟨2 * m, by ring⟩
  have hcop : Nat.Coprime (2 ^ r) (4 * m + 1) :=
    Nat.Coprime.pow_left r (Nat.coprime_two_left.mpr hodd)
  exact hcop.dvd_of_dvd_mul_left hbig'

theorem three_le_pow_half {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h4 : 4 ≤ p ^ f)
    (hf : Even f) : 3 ≤ p ^ (f / 2) := by
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at h4
    omega
  have hfpos : 1 ≤ f / 2 := by
    obtain ⟨k, hk⟩ := hf
    omega
  calc 3 ≤ p := hp3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ (f / 2) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hfpos

theorem pow_eq_pow_half_mul {p f : ℕ} (hf : Even f) :
    p ^ f = p ^ (f / 2) * p ^ (f / 2) := by
  rw [← pow_add]
  congr 1
  obtain ⟨k, hk⟩ := hf
  omega

theorem intCast_pow_sub_one {p f : ℕ} (hp : 0 < p) (hf : Even f) :
    ((p ^ f - 1 : ℕ) : ℤ) = (p ^ (f / 2) : ℤ) * p ^ (f / 2) - 1 := by
  rw [pow_eq_pow_half_mul hf]
  have hpos : 0 < p ^ (f / 2) * p ^ (f / 2) :=
    mul_pos (pow_pos hp _) (pow_pos hp _)
  rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ p ^ (f / 2) * p ^ (f / 2))]
  push_cast
  ring

end Twist

section Large

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Q : Subgroup X} {r : ℕ}
  {p f : ℕ}

theorem exists_large_element [Fact p.Prime] (E : PGamEmb X F)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h4 : 4 ≤ p ^ f) (hf : Even f) (hidx : (genFittingFStar X).index ≤ 2) (hr : 4 ≤ r)
    (hz : E.ρ (MulAut.conj (quatInvolution r e)) = SemidirectProduct.inl (pD (-1)))
    {σ₀ : F ≃+* F} (hσ₀1 : σ₀ ≠ 1) (hσ₀2 : σ₀ * σ₀ = 1)
    (hq : ∀ x : F, σ₀ x = x ^ (p ^ (f / 2))) (hbig : 2 ^ (r + 1) ∣ p ^ f - 1) :
    ∃ w : X, w * quatInvolution r e = quatInvolution r e * w ∧ 2 ^ (r + 1) ∣ orderOf w := by
  have h2 : (2 : F) ≠ 0 := (field_facts (Fact.out : p.Prime) hp2 hF h4).2
  have hcard : Nat.card Fˣ = p ^ (f / 2) * p ^ (f / 2) - 1 :=
    card_units_eq_sq_sub_one hF hf
  have hq3 : 3 ≤ p ^ (f / 2) := three_le_pow_half hp2 h4 hf
  have hpf : p ^ f = p ^ (f / 2) * p ^ (f / 2) := pow_eq_pow_half_mul hf
  have hbig' : 2 ^ (r + 1) ∣ p ^ (f / 2) * p ^ (f / 2) - 1 := by
    rw [← hpf]
    exact hbig
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨x₀, y, hx₀, _, hB⟩ := quat_structure E e hF hp2 h4 hidx hr hz hσ₀1 hσ₀2
  let b : X := ((e.symm (QuaternionGroup.xa 0) : ↥Q) : X)
  have hbq : E.ρ (MulAut.conj b) = qEmb E e (QuaternionGroup.xa 0) := by rw [qEmb_apply]
  have hub : ubar F = E.ρ (MulAut.conj (quatInvolution r e)) := by
    rw [ubar_eq, ← inl_pD_eq, ← hz]
  have hcard4 : 4 ∣ Nat.card Fˣ := by
    rw [hcard]
    have hqodd : Odd (p ^ (f / 2)) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    obtain ⟨k, hk⟩ := hqodd
    rw [hk]
    have hsq : (2 * k + 1) * (2 * k + 1) = 4 * (k * (k + 1)) + 1 := by ring
    exact ⟨k * (k + 1), by omega⟩
  have hγns : ¬ IsSquare γ := not_isSquare_of_generator h2 hγ
  have hsneg : IsSquare (-1 : Fˣ) := isSquare_neg_one_of_four_dvd hcard4
  rcases hB with ⟨hBd, hxd, hyd⟩ | ⟨hBa, hxa, hya⟩
  · have hxd' : x₀ ^ (p ^ (f / 2)) = x₀⁻¹ := (autU_eq_pow hq x₀).symm.trans hxd
    have hxq1 : x₀ ^ (p ^ (f / 2) + 1) = 1 := by rw [pow_succ, hxd', inv_mul_cancel]
    have hdvd : 2 ^ (r - 1) ∣ p ^ (f / 2) + 1 := by
      rw [← hx₀]
      exact orderOf_dvd_of_pow_eq_one hxq1
    have hq8 : p ^ (f / 2) % 8 = 7 := q_mod_eight_of_dvd_add_one hr hdvd
    have h2r : 2 ^ r ∣ p ^ (f / 2) + 1 := two_pow_dvd_add_one_of_big hq8 hbig'
    have hgord : 2 * (p ^ (f / 2) + 1) ∣ orderOf (gA γ σ₀) :=
      two_mul_dvd_orderOf_gA hσ₀1 hσ₀2 hq hcard hq3 hγ
    have hdiv : 2 ^ (r + 1) ∣ orderOf (gA γ σ₀) := by
      have h2r' : 2 * 2 ^ r ∣ 2 * (p ^ (f / 2) + 1) := mul_dvd_mul_left 2 h2r
      have hpoweq : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ, mul_comm]
      rw [hpoweq]
      exact h2r'.trans hgord
    have hny : ¬ IsSquare y := not_isSquare_y_diag h2 hq hcard hr hx₀ hxd hyd
    have hsquare : IsSquare (-(γ * y)) := by
      have h1 : IsSquare (γ * y) := isSquare_mul_of_not_isSquare h2 hγns hny
      have hneg : -(γ * y) = (-1 : Fˣ) * (γ * y) := by ext; simp
      rw [hneg]
      exact hsneg.mul h1
    have hb_eq : E.ρ (MulAut.conj b) = gD y σ₀ := by rw [hbq, hBd]
    have hquot : gA γ σ₀ * (E.ρ (MulAut.conj b))⁻¹ = gA (γ * y) 1 := by
      rw [hb_eq, third_diag_quot hσ₀2 γ y]
    have h1 : (gA γ σ₀ * (E.ρ (MulAut.conj b))⁻¹).right = 1 := by
      rw [hquot, gA_right]
    have hleft : (gA γ σ₀ * (E.ρ (MulAut.conj b))⁻¹).left ∈ pslRange F := by
      rw [hquot]
      exact (pA_mem_pslRange_iff (γ * y)).mpr hsquare
    obtain ⟨w, hw⟩ := exists_inner_of_quot E h1 hleft
    refine ⟨w, ?_, ?_⟩
    · apply E.conjInj
      apply E.inj
      simp only [map_mul]
      rw [hw, ← hub]
      exact (isMon_iff_comm_ubar h2).mp (isMon_gA γ σ₀)
    · have hordw : orderOf w = orderOf (gA γ σ₀) := by
        rw [← hw]
        exact (orderOf_injective (E.ρ.comp MulAut.conj) (E.inj.comp E.conjInj) w).symm
      rw [hordw]
      exact hdiv
  · have hxa' : x₀ ^ (p ^ (f / 2)) = x₀ := (autU_eq_pow hq x₀).symm.trans hxa
    have hq1 : 1 ≤ p ^ (f / 2) := by omega
    have hxqm1 : x₀ ^ (p ^ (f / 2) - 1) = 1 := by
      have h : x₀ ^ (p ^ (f / 2) - 1) * x₀ = 1 * x₀ := by
        rw [one_mul, ← pow_succ, Nat.sub_add_cancel hq1, hxa']
      exact mul_right_cancel h
    have hdvd : 2 ^ (r - 1) ∣ p ^ (f / 2) - 1 := by
      rw [← hx₀]
      exact orderOf_dvd_of_pow_eq_one hxqm1
    have hq8 : p ^ (f / 2) % 8 = 1 := q_mod_eight_of_dvd_sub_one hr hq1 hdvd
    have h2r : 2 ^ r ∣ p ^ (f / 2) - 1 := two_pow_dvd_sub_one_of_big hq8 hbig'
    have hgord : 2 * (p ^ (f / 2) - 1) ∣ orderOf (gD γ σ₀) :=
      two_mul_dvd_orderOf_gD hσ₀1 hσ₀2 hq hcard hq3 hγ
    have hdiv : 2 ^ (r + 1) ∣ orderOf (gD γ σ₀) := by
      have h2r' : 2 * 2 ^ r ∣ 2 * (p ^ (f / 2) - 1) := mul_dvd_mul_left 2 h2r
      have hpoweq : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ, mul_comm]
      rw [hpoweq]
      exact h2r'.trans hgord
    have hny : ¬ IsSquare y := not_isSquare_y_anti h2 hq hcard hr hx₀ hxa hya
    have hsquare : IsSquare (-(γ * y)) := by
      have h1 : IsSquare (γ * y) := isSquare_mul_of_not_isSquare h2 hγns hny
      have hneg : -(γ * y) = (-1 : Fˣ) * (γ * y) := by ext; simp
      rw [hneg]
      exact hsneg.mul h1
    have hb_eq : E.ρ (MulAut.conj b) = gA y σ₀ := by rw [hbq, hBa]
    have hquot : gD γ σ₀ * (E.ρ (MulAut.conj b))⁻¹ = gA (γ * y) 1 := by
      rw [hb_eq, third_anti_quot hσ₀2 γ y]
    have h1 : (gD γ σ₀ * (E.ρ (MulAut.conj b))⁻¹).right = 1 := by
      rw [hquot, gA_right]
    have hleft : (gD γ σ₀ * (E.ρ (MulAut.conj b))⁻¹).left ∈ pslRange F := by
      rw [hquot]
      exact (pA_mem_pslRange_iff (γ * y)).mpr hsquare
    obtain ⟨w, hw⟩ := exists_inner_of_quot E h1 hleft
    refine ⟨w, ?_, ?_⟩
    · apply E.conjInj
      apply E.inj
      simp only [map_mul]
      rw [hw, ← hub]
      exact (isMon_iff_comm_ubar h2).mp (isMon_gD γ σ₀)
    · have hordw : orderOf w = orderOf (gD γ σ₀) := by
        rw [← hw]
        exact (orderOf_injective (E.ρ.comp MulAut.conj) (E.inj.comp E.conjInj) w).symm
      rw [hordw]
      exact hdiv

theorem two_pow_dvd_card_sub_one [Fact p.Prime] (E : PGamEmb X F)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h4 : 4 ≤ p ^ f) (hf : Even f) (hidx : (genFittingFStar X).index ≤ 2) (hr : 4 ≤ r)
    (hz : E.ρ (MulAut.conj (quatInvolution r e)) = SemidirectProduct.inl (pD (-1)))
    {σ₀ : F ≃+* F} (hσ₀1 : σ₀ ≠ 1) (hσ₀2 : σ₀ * σ₀ = 1)
    (hq : ∀ x : F, σ₀ x = x ^ (p ^ (f / 2))) : 2 ^ r ∣ p ^ f - 1 := by
  have hcard : Nat.card Fˣ = p ^ (f / 2) * p ^ (f / 2) - 1 :=
    card_units_eq_sq_sub_one hF hf
  have hq3 : 3 ≤ p ^ (f / 2) := three_le_pow_half hp2 h4 hf
  have hcast : ((p ^ f - 1 : ℕ) : ℤ) = (p ^ (f / 2) : ℤ) * p ^ (f / 2) - 1 :=
    intCast_pow_sub_one (Fact.out : p.Prime).pos hf
  obtain ⟨x₀, y, hx₀, _, hB⟩ := quat_structure E e hF hp2 h4 hidx hr hz hσ₀1 hσ₀2
  rcases hB with ⟨_, hxd, _⟩ | ⟨_, hxa, _⟩
  · have hxd' : x₀ ^ (p ^ (f / 2)) = x₀⁻¹ := (autU_eq_pow hq x₀).symm.trans hxd
    have hxq1 : x₀ ^ (p ^ (f / 2) + 1) = 1 := by rw [pow_succ, hxd', inv_mul_cancel]
    have hdvd : 2 ^ (r - 1) ∣ p ^ (f / 2) + 1 := by
      rw [← hx₀]
      exact orderOf_dvd_of_pow_eq_one hxq1
    have hdvdZ : ((2 : ℤ) ^ (r - 1)) ∣ (p ^ (f / 2) : ℤ) + 1 := by exact_mod_cast hdvd
    have hzdiv := pow_two_dvd_sq_sub_one_of_dvd_add (by omega : 2 ≤ r) hdvdZ
    have hz2 : ((2 : ℤ) ^ r) ∣ ((p ^ f - 1 : ℕ) : ℤ) := by
      rw [hcast]
      exact hzdiv
    exact_mod_cast hz2
  · have hxa' : x₀ ^ (p ^ (f / 2)) = x₀ := (autU_eq_pow hq x₀).symm.trans hxa
    have hq1 : 1 ≤ p ^ (f / 2) := by omega
    have hxqm1 : x₀ ^ (p ^ (f / 2) - 1) = 1 := by
      have h : x₀ ^ (p ^ (f / 2) - 1) * x₀ = 1 * x₀ := by
        rw [one_mul, ← pow_succ, Nat.sub_add_cancel hq1, hxa']
      exact mul_right_cancel h
    have hdvd : 2 ^ (r - 1) ∣ p ^ (f / 2) - 1 := by
      rw [← hx₀]
      exact orderOf_dvd_of_pow_eq_one hxqm1
    have hdvdZ : ((2 : ℤ) ^ (r - 1)) ∣ (p ^ (f / 2) : ℤ) - 1 := by exact_mod_cast hdvd
    have hzdiv := pow_two_dvd_sq_sub_one_of_dvd_sub (by omega : 2 ≤ r) hdvdZ
    have hz2 : ((2 : ℤ) ^ r) ∣ ((p ^ f - 1 : ℕ) : ℤ) := by
      rw [hcast]
      exact hzdiv
    exact_mod_cast hz2

end Large

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
