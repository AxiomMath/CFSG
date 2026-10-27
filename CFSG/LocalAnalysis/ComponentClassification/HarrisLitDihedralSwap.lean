module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma410

public section

namespace CFSG.ComponentClassification.HarrisLit

open DihedralGroup

variable {m : ℕ}

theorem zmod_two_mul_eq_zero_iff (hm : 1 ≤ m) (x : ZMod (2 ^ m)) :
    2 * x = 0 ↔ x = 0 ∨ x = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hm]
  constructor
  · intro h
    have hx := ZMod.natCast_zmod_val x
    have h2 : ((2 * x.val : ℕ) : ZMod (2 ^ m)) = 0 := by
      push_cast
      rw [hx, h]
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hlt := ZMod.val_lt x
    obtain ⟨c, hc⟩ := h2
    have hc2 : 2 * x.val = 2 * (2 ^ (m - 1) * c) := by
      calc 2 * x.val = 2 ^ m * c := hc
        _ = 2 * (2 ^ (m - 1) * c) := by rw [hpow, mul_assoc]
    have hc' : x.val = 2 ^ (m - 1) * c := Nat.eq_of_mul_eq_mul_left (by norm_num) hc2
    have hc1 : c < 2 := by
      by_contra hc2
      have : 2 ^ (m - 1) * 2 ≤ 2 ^ (m - 1) * c := Nat.mul_le_mul_left _ (by omega)
      omega
    interval_cases c
    · left
      rw [← hx, hc', mul_zero, Nat.cast_zero]
    · right
      rw [← hx, hc', mul_one]
  · rintro (rfl | rfl)
    · rw [mul_zero]
    · rw [show (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) by norm_num, ← Nat.cast_mul,
        ← hpow, ZMod.natCast_self]

theorem zmod_two_mul_eq_half_iff (hm : 2 ≤ m) (x : ZMod (2 ^ m)) :
    2 * x = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ↔
      x = ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) ∨ x = -((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) := by
  have h1 : (2 : ZMod (2 ^ m)) * ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) =
      ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    rw [show (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) by norm_num, ← Nat.cast_mul,
      ← pow_succ', show m - 2 + 1 = m - 1 by omega]
  have h2 : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = -((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    rw [eq_neg_iff_add_eq_zero, ← two_mul]
    exact (zmod_two_mul_eq_zero_iff (by omega) _).mpr (Or.inr rfl)
  constructor
  · intro h
    have h3 : 2 * (x - ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))) = 0 := by
      rw [mul_sub, h, h1, sub_self]
    rcases (zmod_two_mul_eq_zero_iff (by omega) _).mp h3 with h4 | h4
    · left
      exact sub_eq_zero.mp h4
    · right
      have h0 := (zmod_two_mul_eq_zero_iff (by omega) ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))).mpr
        (Or.inr rfl)
      linear_combination h4 + h1 + h0
  · rintro (rfl | rfl)
    · exact h1
    · rw [mul_neg, h1, ← h2]

theorem dihedral_commute_sr_iff (hm : 1 ≤ m) (g : DihedralGroup (2 ^ m)) (i : ZMod (2 ^ m)) :
    g * sr i = sr i * g ↔ g = 1 ∨ g = r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ∨ g = sr i ∨
      g = sr (i + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) := by
  rcases g with k | k
  · rw [r_mul_sr, sr_mul_r, sr.injEq, one_def, r.injEq, r.injEq]
    simp only [reduceCtorEq, or_false]
    constructor
    · intro h
      have : 2 * k = 0 := by linear_combination -h
      exact (zmod_two_mul_eq_zero_iff hm k).mp this
    · rintro (rfl | rfl)
      · ring
      · have := (zmod_two_mul_eq_zero_iff hm ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))).mpr (Or.inr rfl)
        linear_combination -this
  · rw [sr_mul_sr, sr_mul_sr, r.injEq, one_def, sr.injEq, sr.injEq]
    simp only [reduceCtorEq, false_or]
    constructor
    · intro h
      have : 2 * (k - i) = 0 := by linear_combination -h
      rcases (zmod_two_mul_eq_zero_iff hm _).mp this with h' | h'
      · left
        exact sub_eq_zero.mp h'
      · right
        rw [← h']
        ring
    · rintro (rfl | rfl)
      · ring
      · have := (zmod_two_mul_eq_zero_iff hm ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))).mpr (Or.inr rfl)
        linear_combination -this

theorem dihedral_sq_eq_one_iff (hm : 1 ≤ m) (g : DihedralGroup (2 ^ m)) :
    g ^ 2 = 1 ↔ g = 1 ∨ g = r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ∨ ∃ i, g = sr i := by
  rcases g with k | k
  · simp only [sq, r_mul_r, one_def, r.injEq, reduceCtorEq, exists_false, or_false]
    rw [← two_mul]
    exact zmod_two_mul_eq_zero_iff hm k
  · constructor
    · intro _
      right
      right
      exact ⟨k, rfl⟩
    · intro _
      rw [sq, sr_mul_sr, sub_self, r_zero]

theorem dihedral_swap_eq (hm : 3 ≤ m) (ψ : DihedralGroup (2 ^ m) →* DihedralGroup (2 ^ m))
    (hψ : ∀ g, ψ (ψ g) = g)
    (hsw : ∀ i : ZMod (2 ^ m), ∀ c : DihedralGroup (2 ^ m), c⁻¹ * sr i * c ≠ ψ (sr i)) :
    ∃ a : ZMod (2 ^ m), ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) a ≠ 0 ∧
      ∀ i, ψ (r i) = r (-i) ∧ ψ (sr i) = sr (a - i) := by
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  have hinj : Function.Injective ψ := fun a b hab => by rw [← hψ a, hab, hψ]
  obtain ⟨k, hk⟩ : ∃ k, ψ (r 1) = r k := by
    rcases hr : ψ (r 1) with k | k
    · exact ⟨k, rfl⟩
    · exfalso
      have h1 : orderOf (ψ (r 1)) = orderOf (r 1 : DihedralGroup (2 ^ m)) :=
        orderOf_injective ψ hinj _
      rw [hr, orderOf_sr, orderOf_r_one] at h1
      have : 8 ≤ 2 ^ m := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
  have hrot : ∀ i, ψ (r i) = r (k * i) := by
    intro i
    have : (r i : DihedralGroup (2 ^ m)) = r 1 ^ i.val := by
      rw [r_one_pow, ZMod.natCast_zmod_val]
    rw [this, map_pow, hk, r_pow, ZMod.natCast_zmod_val]
  obtain ⟨a, ha⟩ : ∃ a, ψ (sr 0) = sr a := by
    rcases hs : ψ (sr 0) with j | j
    · exfalso
      have h4 := hψ (sr 0)
      rw [hs, hrot] at h4
      exact absurd h4 (by simp)
    · exact ⟨j, rfl⟩
  have hodd : ZMod.castHom (dvd_pow_self 2 (by omega : m ≠ 0)) (ZMod 2) a ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := dihedral_exists_conj_of_parity (by omega : 1 ≤ m) (i := 0) (j := a)
      (by rw [map_zero, h0])
    exact hsw 0 c (by rw [hc, ha])
  have hsr : ∀ i, ψ (sr i) = sr (a + k * i) := by
    intro i
    have : (sr i : DihedralGroup (2 ^ m)) = sr 0 * r i := by rw [sr_mul_r, zero_add]
    rw [this, map_mul, ha, hrot, sr_mul_r]
  have hk1 : k = -1 := by
    have h1 : ψ (ψ (sr 0)) = sr 0 := hψ _
    rw [ha, hsr, sr.injEq] at h1
    have hunit : IsUnit a := by
      have hval : (a.val : ZMod 2) ≠ 0 := by
        rwa [ZMod.castHom_apply, ZMod.cast_eq_val] at hodd
      have h2 : ¬ 2 ∣ a.val := fun h' => hval ((ZMod.natCast_eq_zero_iff _ 2).mpr h')
      have hcop : Nat.Coprime a.val (2 ^ m) := Nat.Coprime.pow_right m
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))
      refine ⟨ZMod.unitOfCoprime a.val hcop, ?_⟩
      rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]
    have h2 : a * (1 + k) = 0 := by linear_combination h1
    have h3 := (hunit.mul_right_eq_zero).mp h2
    linear_combination h3
  refine ⟨a, hodd, fun i => ⟨?_, ?_⟩⟩
  · rw [hrot, hk1]
    congr 1
    ring
  · rw [hsr, hk1]
    congr 1
    ring

theorem dihedral_swap_fixed_iff (hm : 3 ≤ m) (ψ : DihedralGroup (2 ^ m) →* DihedralGroup (2 ^ m))
    (hψ : ∀ g, ψ (ψ g) = g)
    (hsw : ∀ i : ZMod (2 ^ m), ∀ c : DihedralGroup (2 ^ m), c⁻¹ * sr i * c ≠ ψ (sr i))
    (g : DihedralGroup (2 ^ m)) :
    ψ g = g ↔ g = 1 ∨ g = r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  obtain ⟨a, hodd, hψa⟩ := dihedral_swap_eq hm ψ hψ hsw
  rcases g with i | i
  · rw [(hψa i).1, r.injEq, one_def, r.injEq, r.injEq]
    rw [← zmod_two_mul_eq_zero_iff (by omega) i]
    constructor
    · intro h
      linear_combination -h
    · intro h
      linear_combination -h
  · rw [(hψa i).2, sr.injEq, one_def]
    simp only [reduceCtorEq, or_self, iff_false]
    intro h
    apply hodd
    have : a = 2 * i := by linear_combination h
    rw [this, map_mul, map_ofNat, show (2 : ZMod 2) = 0 by decide, zero_mul]

theorem dihedral_swap_twisted_iff (hm : 3 ≤ m) (ψ : DihedralGroup (2 ^ m) →* DihedralGroup (2 ^ m))
    (hψ : ∀ g, ψ (ψ g) = g)
    (hsw : ∀ i : ZMod (2 ^ m), ∀ c : DihedralGroup (2 ^ m), c⁻¹ * sr i * c ≠ ψ (sr i))
    (g : DihedralGroup (2 ^ m)) :
    g⁻¹ * ψ g = r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ↔
      g = r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) ∨ g = r (-((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))) := by
  obtain ⟨a, hodd, hψa⟩ := dihedral_swap_eq hm ψ hψ hsw
  rcases g with i | i
  · rw [(hψa i).1, inv_r, r_mul_r, r.injEq, r.injEq, r.injEq]
    have h := zmod_two_mul_eq_half_iff (by omega : 2 ≤ m) (-i)
    constructor
    · intro h'
      rcases h.mp (by linear_combination h') with h1 | h1
      · right
        linear_combination -h1
      · left
        linear_combination -h1
    · rintro (h1 | h1)
      · have := h.mpr (Or.inr (by rw [h1]))
        linear_combination this
      · have := h.mpr (Or.inl (by rw [h1, neg_neg]))
        linear_combination this
  · rw [(hψa i).2, inv_sr, sr_mul_sr]
    simp only [r.injEq, reduceCtorEq, or_self, iff_false]
    intro h
    apply hodd
    have h2 : a = 2 * (i + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))) := by
      have h1 : (2 : ZMod (2 ^ m)) * ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) =
          ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        rw [show (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) by norm_num, ← Nat.cast_mul,
          ← pow_succ', show m - 2 + 1 = m - 1 by omega]
      linear_combination h - h1
    rw [h2, map_mul, map_ofNat, show (2 : ZMod 2) = 0 by decide, zero_mul]

end CFSG.ComponentClassification.HarrisLit
