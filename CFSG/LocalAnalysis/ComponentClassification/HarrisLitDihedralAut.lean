module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.DedekindFinite
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ComponentClassification.HarrisLit

open DihedralGroup

variable {m : ℕ}

theorem zmod_neg_one_ne_one (hm : 2 ≤ m) : (-1 : ZMod (2 ^ m)) ≠ 1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod (2 ^ m)) = 0 := by
    have : (2 : ZMod (2 ^ m)) = 1 - (-1) := by ring
    rw [Nat.cast_ofNat, this, h, sub_self]
  rw [ZMod.natCast_eq_zero_iff] at h2
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem dihedral_mulAut_eq_one_of_odd (hm : 2 ≤ m) (ψ : MulAut (DihedralGroup (2 ^ m)))
    {k : ℕ} (hk : Odd k) (hψk : ψ ^ k = 1) : ψ = 1 := by
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨a, ha⟩ : ∃ a, ψ (r 1) = r a := by
    rcases hψ : ψ (r 1) with a | b
    · exact ⟨a, rfl⟩
    · exfalso
      have h1 := MulEquiv.orderOf_eq ψ (r 1)
      rw [hψ, orderOf_sr, orderOf_r_one] at h1
      omega
  obtain ⟨b, hb⟩ : ∃ b, ψ (sr 0) = sr b := by
    rcases hψ : ψ (sr 0) with c | b
    · exfalso
      have hcomm : ψ (sr 0 * r 1) = ψ (r 1 * sr 0) := by
        rw [map_mul, map_mul, hψ, ha, r_mul_r, r_mul_r, add_comm]
      have := ψ.injective hcomm
      rw [sr_mul_r, r_mul_sr, sr.injEq, zero_add, zero_sub] at this
      exact zmod_neg_one_ne_one hm this.symm
    · exact ⟨b, rfl⟩
  have hr : ∀ i : ZMod (2 ^ m), ψ (r i) = r (a * i) := by
    intro i
    have : r i = (r 1 : DihedralGroup (2 ^ m)) ^ i.val := by
      rw [r_one_pow, ZMod.natCast_zmod_val]
    rw [this, map_pow, ha, r_pow, ZMod.natCast_zmod_val]
  have hsr : ∀ j : ZMod (2 ^ m), ψ (sr j) = sr (b + a * j) := by
    intro j
    have : sr j = sr 0 * r j := by rw [sr_mul_r, zero_add]
    rw [this, map_mul, hb, hr, sr_mul_r]
  have hiter : ∀ n : ℕ, ∀ i j : ZMod (2 ^ m), (ψ ^ n) (r i) = r (a ^ n * i) ∧
      (ψ ^ n) (sr j) = sr (b * (∑ l ∈ Finset.range n, a ^ l) + a ^ n * j) := by
    intro n
    induction n with
    | zero =>
      intro i j
      simp
    | succ n ih =>
      intro i j
      rw [pow_succ, MulAut.mul_apply, MulAut.mul_apply, hr, hsr, (ih (a * i) 0).1,
        (ih 0 (b + a * j)).2, Finset.sum_range_succ]
      constructor
      · congr 1
        ring
      · congr 1
        ring
  have hak : a ^ k = 1 := by
    have h1 := (hiter k 1 0).1
    rw [hψk, MulAut.one_apply, mul_one] at h1
    exact (r.inj h1).symm
  have hka : Nat.Coprime k (2 ^ (m - 1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hk)
  have ha1 : a = 1 := by
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact (Nat.not_odd_zero hk)
    let U : (ZMod (2 ^ m))ˣ := Units.mkOfMulEqOne a (a ^ (k - 1)) (by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0), hak])
    have hU : U ^ k = 1 := Units.ext (by simp [U, hak])
    have hdvd1 : orderOf U ∣ k := orderOf_dvd_of_pow_eq_one hU
    have hdvd2 : orderOf U ∣ 2 ^ (m - 1) := by
      have := orderOf_dvd_natCard U
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (by omega)] at this
      simpa using this
    have h1 : orderOf U = 1 := Nat.eq_one_of_dvd_coprimes hka hdvd1 hdvd2
    rw [orderOf_eq_one_iff] at h1
    have := congrArg Units.val h1
    simpa [U] using this
  subst ha1
  have hb0 : b = 0 := by
    have h1 := (hiter k 0 0).2
    rw [hψk, MulAut.one_apply] at h1
    have h2 := (sr.inj h1).symm
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      mul_zero, add_zero] at h2
    have hkm : Nat.Coprime k (2 ^ m) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hk)
    have hunit : IsUnit (k : ZMod (2 ^ m)) := (ZMod.unitOfCoprime k hkm).isUnit
    rcases hunit with ⟨v, hv⟩
    calc b = b * (k : ZMod (2 ^ m)) * (v⁻¹ : (ZMod (2 ^ m))ˣ) := by
          rw [← hv, mul_assoc, Units.mul_inv, mul_one]
      _ = 0 := by rw [h2, zero_mul]
  subst hb0
  ext x
  rcases x with i | j
  · rw [hr, one_mul, MulAut.one_apply]
  · rw [hsr, zero_add, one_mul, MulAut.one_apply]

end CFSG.ComponentClassification.HarrisLit
