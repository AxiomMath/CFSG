module

public import CFSG.Open.Defs

public section

namespace CFSG.ComponentClassification.GSThmB.X10Orth

open CFSG.Open

theorem prod_Icc_three (x : ℕ) :
    ∏ i ∈ Finset.Icc 1 (4 - 1), (x ^ (2 * i) - 1) = (x ^ 2 - 1) * (x ^ 4 - 1) * (x ^ 6 - 1) := by
  rw [show Finset.Icc 1 (4 - 1) = {1, 2, 3} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

theorem four_dvd_pow_four_sub_one {x : ℕ} (hx : Odd x) : 4 ∣ x ^ 4 - 1 := by
  obtain ⟨k, rfl⟩ := hx
  have h1 : 1 ≤ (2 * k + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  refine ⟨4 * k ^ 4 + 8 * k ^ 3 + 6 * k ^ 2 + 2 * k, ?_⟩
  have : (2 * k + 1) ^ 4 = 4 * (4 * k ^ 4 + 8 * k ^ 3 + 6 * k ^ 2 + 2 * k) + 1 := by ring
  omega

theorem gcd_four_pow_four_sub_one {x : ℕ} (hx : Odd x) : Nat.gcd 4 (x ^ 4 - 1) = 4 :=
  Nat.gcd_eq_left (four_dvd_pow_four_sub_one hx)

theorem gcd_four_pow_four_add_one {x : ℕ} (hx : Odd x) : Nat.gcd 4 (x ^ 4 + 1) = 2 := by
  obtain ⟨m, hm⟩ := four_dvd_pow_four_sub_one hx
  have h1 : 1 ≤ x ^ 4 := Nat.one_le_pow _ _ (by obtain ⟨k, rfl⟩ := hx; omega)
  have : x ^ 4 + 1 = 4 * m + 2 := by omega
  rw [this]
  have : Nat.gcd 4 (4 * m + 2) = Nat.gcd 4 2 := by
    rw [Nat.gcd_comm, Nat.gcd_comm 4 2]
    simp [Nat.gcd_comm]
  rw [this]
  rfl

theorem not_dvd_ordD_four {x X : ℕ} (hx : Odd x) (hx3 : 3 ≤ x)
    (hX : X * 2 = (x ^ 2) ^ 4 * (((x ^ 2) ^ 2 - 1) * ((x ^ 2) ^ 4 - 1))) : ¬ X ∣ ordD 4 x := by
  intro hdvd
  have h1 : 1 ≤ x := by omega
  have hp : ∀ k : ℕ, 1 ≤ x ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  set num := x ^ (4 * (4 - 1)) * (x ^ 4 - 1) * ∏ i ∈ Finset.Icc 1 (4 - 1), (x ^ (2 * i) - 1)
    with hnum
  have h4 : 4 ∣ num := Dvd.dvd.mul_right (Dvd.dvd.mul_left (four_dvd_pow_four_sub_one hx) _) _
  have hN : ordD 4 x * 4 = num := by
    rw [ordD, gcd_four_pow_four_sub_one hx]
    exact Nat.div_mul_cancel h4
  have hdvd' : X * 4 ∣ num := hN ▸ Nat.mul_dvd_mul_right hdvd 4
  rw [hnum, prod_Icc_three] at hdvd'
  have hZ : ((X * 4 : ℕ) : ℤ) ∣ ((x ^ (4 * (4 - 1)) * (x ^ 4 - 1) *
      ((x ^ 2 - 1) * (x ^ 4 - 1) * (x ^ 6 - 1)) : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hdvd'
  have hX' : ((X * 4 : ℕ) : ℤ) = 2 * (x : ℤ) ^ 8 * ((x : ℤ) ^ 4 - 1) ^ 2 * ((x : ℤ) ^ 4 + 1) := by
    have e := congrArg (fun n : ℕ => (n : ℤ)) hX
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at e
    rw [Nat.cast_sub (by rw [← pow_mul]; exact hp _), Nat.cast_sub (by rw [← pow_mul]; exact hp _)]
      at e
    push_cast at e ⊢
    linear_combination 2 * e
  rw [hX'] at hZ
  push_cast [Nat.cast_sub (hp 4), Nat.cast_sub (hp 2), Nat.cast_sub (hp 6)] at hZ
  set a : ℤ := (x : ℤ) with ha
  have ha3 : 3 ≤ a := by rw [ha]; exact_mod_cast hx3
  have hne : a ^ 8 * (a ^ 4 - 1) ^ 2 ≠ 0 := by
    have : 0 < a ^ 4 - 1 := by nlinarith [pow_le_pow_left₀ (by norm_num) ha3 4]
    positivity
  have h2 : 2 * (a ^ 4 + 1) ∣ a ^ 4 * ((a ^ 2 - 1) * (a ^ 6 - 1)) := by
    have e : a ^ (4 * (4 - 1)) * (a ^ 4 - 1) * ((a ^ 2 - 1) * (a ^ 4 - 1) * (a ^ 6 - 1)) =
        (a ^ 8 * (a ^ 4 - 1) ^ 2) * (a ^ 4 * ((a ^ 2 - 1) * (a ^ 6 - 1))) := by ring
    have e' : 2 * a ^ 8 * (a ^ 4 - 1) ^ 2 * (a ^ 4 + 1) =
        (a ^ 8 * (a ^ 4 - 1) ^ 2) * (2 * (a ^ 4 + 1)) := by ring
    rw [e, e'] at hZ
    exact (mul_dvd_mul_iff_left hne).1 hZ
  have h3 : a ^ 4 + 1 ∣ 2 := by
    have e : (2 : ℤ) = (a ^ 4 + 1) * (a ^ 8 - a ^ 6 - a ^ 4 + 2) -
        a ^ 4 * ((a ^ 2 - 1) * (a ^ 6 - 1)) := by ring
    rw [e]
    exact dvd_sub (dvd_mul_right _ _) ((dvd_mul_left _ _).trans h2)
  have := Int.le_of_dvd (by norm_num) h3
  nlinarith [pow_le_pow_left₀ (by norm_num) ha3 4]

theorem not_dvd_ordTwistedD_four {x X : ℕ} (hx : Odd x) (hx3 : 3 ≤ x)
    (hX : X * 2 = (x ^ 2) ^ 4 * (((x ^ 2) ^ 2 - 1) * ((x ^ 2) ^ 4 - 1))) :
    ¬ X ∣ ordTwistedD 4 x := by
  intro hdvd
  have hp : ∀ k : ℕ, 1 ≤ x ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  set num := x ^ (4 * (4 - 1)) * (x ^ 4 + 1) * ∏ i ∈ Finset.Icc 1 (4 - 1), (x ^ (2 * i) - 1)
    with hnum
  have h2d : 2 ∣ num := by
    obtain ⟨m, hm⟩ := four_dvd_pow_four_sub_one hx
    have : x ^ 4 + 1 = 2 * (2 * m + 1) := by have := hp 4; omega
    rw [hnum, this]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_mul_right 2 _) _) _
  have hN : ordTwistedD 4 x * 2 = num := by
    rw [ordTwistedD, gcd_four_pow_four_add_one hx]
    exact Nat.div_mul_cancel h2d
  have hdvd' : X * 2 ∣ num := hN ▸ Nat.mul_dvd_mul_right hdvd 2
  rw [hnum, prod_Icc_three] at hdvd'
  have hZ : ((X * 2 : ℕ) : ℤ) ∣ ((x ^ (4 * (4 - 1)) * (x ^ 4 + 1) *
      ((x ^ 2 - 1) * (x ^ 4 - 1) * (x ^ 6 - 1)) : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hdvd'
  have hX' : ((X * 2 : ℕ) : ℤ) = (x : ℤ) ^ 8 * ((x : ℤ) ^ 4 - 1) ^ 2 * ((x : ℤ) ^ 4 + 1) := by
    have e := congrArg (fun n : ℕ => (n : ℤ)) hX
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at e
    rw [Nat.cast_sub (by rw [← pow_mul]; exact hp _), Nat.cast_sub (by rw [← pow_mul]; exact hp _)]
      at e
    push_cast at e ⊢
    linear_combination e
  rw [hX'] at hZ
  push_cast [Nat.cast_sub (hp 4), Nat.cast_sub (hp 2), Nat.cast_sub (hp 6)] at hZ
  set a : ℤ := (x : ℤ) with ha
  have ha3 : 3 ≤ a := by rw [ha]; exact_mod_cast hx3
  have hne : a ^ 8 * (a ^ 4 + 1) * (a ^ 2 - 1) ^ 2 ≠ 0 := by
    have : 0 < a ^ 2 - 1 := by nlinarith
    positivity
  have h2 : a ^ 2 + 1 ∣ a ^ 4 * (a ^ 6 - 1) := by
    have e : a ^ (4 * (4 - 1)) * (a ^ 4 + 1) * ((a ^ 2 - 1) * (a ^ 4 - 1) * (a ^ 6 - 1)) =
        (a ^ 8 * (a ^ 4 + 1) * (a ^ 2 - 1) ^ 2) * ((a ^ 2 + 1) * (a ^ 4 * (a ^ 6 - 1))) := by
      ring
    have e' : a ^ 8 * (a ^ 4 - 1) ^ 2 * (a ^ 4 + 1) =
        (a ^ 8 * (a ^ 4 + 1) * (a ^ 2 - 1) ^ 2) * ((a ^ 2 + 1) * (a ^ 2 + 1)) := by ring
    rw [e, e'] at hZ
    have := (mul_dvd_mul_iff_left hne).1 hZ
    have hne' : a ^ 2 + 1 ≠ 0 := by positivity
    exact (mul_dvd_mul_iff_left hne').1 this
  have h3 : a ^ 2 + 1 ∣ 2 := by
    have e : (2 : ℤ) = (a ^ 2 + 1) * (a ^ 8 - a ^ 6 + a ^ 4 - 2 * a ^ 2 + 2) -
        a ^ 4 * (a ^ 6 - 1) := by ring
    rw [e]
    exact dvd_sub (dvd_mul_right _ _) h2
  have := Int.le_of_dvd (by norm_num) h3
  nlinarith

end CFSG.ComponentClassification.GSThmB.X10Orth
