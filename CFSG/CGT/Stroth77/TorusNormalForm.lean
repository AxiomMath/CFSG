module

public import Mathlib.Data.ZMod.Units
public import Mathlib.Tactic.IntervalCases
public import CFSG.CGT.Stroth77.Types120

public section

namespace CFSG.CGT.Stroth77

open Matrix

theorem intCast_eq_of_two_pow_dvd_sub {k : ℕ} {a b : ℤ} (h : (2 : ℤ) ^ k ∣ a - b) :
    (a : ZMod (2 ^ k)) = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have h' : (2 : ℤ) ^ k ∣ b - a := by
    rw [show b - a = -(a - b) by ring]
    exact h.neg_right
  exact_mod_cast h'

theorem isUnit_intCast_of_odd {k : ℕ} {z : ℤ} (hz : Odd z) : IsUnit (z : ZMod (2 ^ k)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  have h2 : IsCoprime (2 : ℤ) z := by
    obtain ⟨w, rfl⟩ := hz
    exact ⟨-w, 1, by ring⟩
  have h := h2.pow_left (m := k)
  exact_mod_cast h

theorem three_mul_inv_three (k : ℕ) : (3 : ZMod (2 ^ k)) * 3⁻¹ = 1 := by
  have h := isUnit_intCast_of_odd (k := k) (z := 3) ⟨1, by norm_num⟩
  have h' : IsUnit (3 : ZMod (2 ^ k)) := by exact_mod_cast h
  exact ZMod.mul_inv_of_unit _ h'

theorem intCast_eq_mul_inv_three {k : ℕ} {x r : ℤ} (h : (2 : ℤ) ^ k ∣ 3 * x - r) :
    (x : ZMod (2 ^ k)) = r * 3⁻¹ := by
  have h3 : ((3 * x : ℤ) : ZMod (2 ^ k)) = r := intCast_eq_of_two_pow_dvd_sub h
  push_cast at h3
  calc (x : ZMod (2 ^ k)) = (3 * 3⁻¹) * x := by rw [three_mul_inv_three, one_mul]
    _ = (3 * x) * 3⁻¹ := by ring
    _ = r * 3⁻¹ := by rw [h3]

theorem two_mul_two_pow_pred (n : ℕ) : (2 * 2 ^ (n - 1) : ZMod (2 ^ n)) = 0 := by
  rcases n with _ | n
  · decide
  · rw [Nat.add_sub_cancel, ← pow_succ']
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (le_refl (n + 1))

theorem two_pow_pred_ne_zero {n : ℕ} (hn : 1 ≤ n) : (2 ^ (n - 1) : ZMod (2 ^ n)) ≠ 0 := by
  intro h
  have h' : ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have hle : 2 ^ n ≤ 2 ^ (n - 1) := Nat.le_of_dvd (by positivity) h'
  have hlt : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem intCast_mul_two_pow_pred_of_odd {n : ℕ} {z : ℤ} (hz : Odd z) :
    ((z * 2 ^ (n - 1) : ℤ) : ZMod (2 ^ n)) = 2 ^ (n - 1) := by
  obtain ⟨w, rfl⟩ := hz
  push_cast
  linear_combination (w : ZMod (2 ^ n)) * two_mul_two_pow_pred n

namespace Type120

theorem three_mul_iV (n : ℕ) : 3 * iV n = 2 ^ (2 * n + 1) + 1 := by
  unfold iV
  apply Int.mul_ediv_cancel'
  have h4 : (3 : ℤ) ∣ 4 ^ n - 1 := by simpa using sub_one_dvd_pow_sub_one (4 : ℤ) n
  have h : (2 : ℤ) ^ (2 * n + 1) + 1 = 2 * (4 ^ n - 1) + 3 := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_right h4 2) (dvd_refl 3)

theorem three_mul_FV (n : ℕ) : 3 * FV n = 4 ^ n - 1 := by
  unfold FV
  exact Int.mul_ediv_cancel' (by simpa using sub_one_dvd_pow_sub_one (4 : ℤ) n)

theorem three_mul_GV (n : ℕ) : 3 * GV n = 4 ^ (n - 1) - 7 := by
  unfold GV
  apply Int.mul_ediv_cancel'
  have h1 : (3 : ℤ) ∣ 4 ^ (n - 1) - 1 := by
    simpa using sub_one_dvd_pow_sub_one (4 : ℤ) (n - 1)
  have h : (4 : ℤ) ^ (n - 1) - 7 = (4 ^ (n - 1) - 1) - 3 * 2 := by ring
  rw [h]
  exact dvd_sub h1 (dvd_mul_right 3 2)

theorem iV_cast {n k : ℕ} (hk : k ≤ 2 * n + 1) : (iV n : ZMod (2 ^ k)) = 3⁻¹ := by
  have h := intCast_eq_mul_inv_three (k := k) (x := iV n) (r := 1) (by
    rw [three_mul_iV, add_sub_cancel_right]
    exact pow_dvd_pow 2 hk)
  simpa using h

theorem FV_cast {n k : ℕ} (hk : k ≤ 2 * n) : (FV n : ZMod (2 ^ k)) = -3⁻¹ := by
  have h := intCast_eq_mul_inv_three (k := k) (x := FV n) (r := -1) (by
    rw [three_mul_FV, sub_neg_eq_add, sub_add_cancel,
      show (4 : ℤ) ^ n = 2 ^ (2 * n) by rw [pow_mul]; norm_num]
    exact pow_dvd_pow 2 hk)
  simpa using h

theorem GV_cast {n k : ℕ} (hk : k ≤ 2 * (n - 1)) : (GV n : ZMod (2 ^ k)) = -7 * 3⁻¹ := by
  have h := intCast_eq_mul_inv_three (k := k) (x := GV n) (r := -7) (by
    rw [three_mul_GV, sub_neg_eq_add, sub_add_cancel,
      show (4 : ℤ) ^ (n - 1) = 2 ^ (2 * (n - 1)) by rw [pow_mul]; norm_num]
    exact pow_dvd_pow 2 hk)
  simpa using h

end Type120

namespace Torus

variable {k : Fin 3 → ℕ}

@[expose] def ofInt (k : Fin 3 → ℕ) (v : Fin 3 → ℤ) : Torus k := fun i => (v i : ZMod (2 ^ k i))

@[simp] theorem ofInt_apply (v : Fin 3 → ℤ) (i : Fin 3) :
    ofInt k v i = (v i : ZMod (2 ^ k i)) := rfl

theorem ofInt_eq_zsmul_gens (v : Fin 3 → ℤ) :
    ofInt k v = v 0 • gen k 0 + v 1 • gen k 1 + v 2 • gen k 2 := by
  funext i
  fin_cases i <;> simp [ofInt, gen, Pi.single_apply, zsmul_eq_mul]

theorem exists_ofInt (x : Torus k) : ∃ v : Fin 3 → ℤ, ofInt k v = x := by
  choose v hv using fun i : Fin 3 => ZMod.intCast_surjective (x i)
  exact ⟨v, funext hv⟩

@[simp] theorem ofInt_zero : ofInt k 0 = 0 := by
  funext i
  simp [ofInt]

@[simp] theorem ofInt_add (v w : Fin 3 → ℤ) : ofInt k (v + w) = ofInt k v + ofInt k w := by
  funext i
  simp [ofInt]

@[simp] theorem ofInt_neg (v : Fin 3 → ℤ) : ofInt k (-v) = -ofInt k v := by
  funext i
  simp [ofInt]

@[simp] theorem ofInt_sub (v w : Fin 3 → ℤ) : ofInt k (v - w) = ofInt k v - ofInt k w := by
  funext i
  simp [ofInt]

@[simp] theorem ofInt_zsmul (z : ℤ) (v : Fin 3 → ℤ) : ofInt k (z • v) = z • ofInt k v := by
  funext i
  simp [ofInt, zsmul_eq_mul]

theorem ofInt_eq_ofInt_iff {v w : Fin 3 → ℤ} :
    ofInt k v = ofInt k w ↔ ∀ i, v i ≡ w i [ZMOD 2 ^ k i] := by
  constructor
  · intro h i
    have h' := (ZMod.intCast_eq_intCast_iff (v i) (w i) (2 ^ k i)).1 (congrFun h i)
    exact_mod_cast h'
  · intro h
    funext i
    exact (ZMod.intCast_eq_intCast_iff (v i) (w i) (2 ^ k i)).2 (by exact_mod_cast h i)

theorem ofInt_eq_zero_iff {v : Fin 3 → ℤ} : ofInt k v = 0 ↔ ∀ i, (2 : ℤ) ^ k i ∣ v i := by
  constructor
  · intro h i
    have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd (v i) (2 ^ k i)).1 (congrFun h i)
    exact_mod_cast h'
  · intro h
    funext i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (v i) (2 ^ k i)).2 (by exact_mod_cast h i)

private theorem zmod_two_mul_eq_zero_iff_aux {t : ℕ} (x : ZMod (2 ^ (t + 1))) :
    2 * x = 0 ↔ x = 0 ∨ x = 2 ^ t := by
  haveI : NeZero (2 ^ (t + 1)) := ⟨by positivity⟩
  constructor
  · intro h
    obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, n < 2 ^ (t + 1) ∧ (n : ZMod (2 ^ (t + 1))) = x :=
      ⟨x.val, ZMod.val_lt x, ZMod.natCast_zmod_val x⟩
    have h2 : ((2 * n : ℕ) : ZMod (2 ^ (t + 1))) = 0 := by
      push_cast
      exact h
    rw [ZMod.natCast_eq_zero_iff, pow_succ'] at h2
    obtain ⟨q, rfl⟩ : 2 ^ t ∣ n := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).1 h2
    have hq : q < 2 := by
      have h' : 2 ^ t * q < 2 ^ t * 2 := by rw [← pow_succ]; exact hn
      exact Nat.lt_of_mul_lt_mul_left h'
    interval_cases q
    · left
      simp
    · right
      simp
  · rintro (rfl | rfl)
    · simp
    · rw [← pow_succ']
      simpa using ZMod.natCast_pow_eq_zero_of_le 2 (le_refl (t + 1))

private theorem eq_zero_or_eq_two_pow_pred_of_two_mul_eq_zero {n : ℕ} (hn : 1 ≤ n)
    (y : ZMod (2 ^ n)) (h : 2 * y = 0) : y = 0 ∨ y = 2 ^ (n - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact (zmod_two_mul_eq_zero_iff_aux y).1 h

theorem two_zsmul_eq_zero_iff (hk : ∀ i, 1 ≤ k i) (x : Torus k) :
    (2 : ℤ) • x = 0 ↔ ∃ e : Fin 3 → ℤ, (∀ i, e i = 0 ∨ e i = 1) ∧
      x = ofInt k (fun i => e i * 2 ^ (k i - 1)) := by
  classical
  constructor
  · intro h
    have hcoord : ∀ i, x i = 0 ∨ x i = 2 ^ (k i - 1) := fun i => by
      have h2 : 2 * x i = 0 := by
        have := congrFun h i
        simpa [zsmul_eq_mul] using this
      exact eq_zero_or_eq_two_pow_pred_of_two_mul_eq_zero (hk i) (x i) h2
    refine ⟨fun i => if x i = 0 then 0 else 1, fun i => by by_cases h0 : x i = 0 <;> simp [h0], ?_⟩
    funext i
    rcases hcoord i with h0 | h1
    · simp [h0]
    · by_cases h0 : x i = 0
      · simp [h0]
      · simp [h0, h1]
  · rintro ⟨e, -, rfl⟩
    funext i
    simp only [Pi.smul_apply, ofInt_apply, Pi.zero_apply, zsmul_eq_mul]
    push_cast
    linear_combination (e i : ZMod (2 ^ k i)) * two_mul_two_pow_pred (k i)

theorem exists_two_zsmul_eq_iff (hk : ∀ i, 1 ≤ k i) (v : Fin 3 → ℤ) :
    (∃ y : Torus k, (2 : ℤ) • y = ofInt k v) ↔ ∀ i, Even (v i) := by
  constructor
  · rintro ⟨y, hy⟩ i
    obtain ⟨w, hw⟩ := ZMod.intCast_surjective (y i)
    have h : (2 : ℤ) • y i = (v i : ZMod (2 ^ k i)) := congrFun hy i
    rw [← hw, zsmul_eq_mul] at h
    have h' : ((2 * w : ℤ) : ZMod (2 ^ k i)) = (v i : ZMod (2 ^ k i)) := by
      rw [Int.cast_mul]
      exact h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
    have h2 : (2 : ℤ) ∣ v i - 2 * w :=
      (dvd_pow_self 2 (by have := hk i; omega : k i ≠ 0)).trans (by exact_mod_cast h')
    have h3 : (2 : ℤ) ∣ v i := by
      have := dvd_add h2 (dvd_mul_right 2 w)
      simpa using this
    exact even_iff_two_dvd.mpr h3
  · intro h
    choose w hw using h
    refine ⟨ofInt k w, ?_⟩
    funext i
    simp only [Pi.smul_apply, ofInt_apply, zsmul_eq_mul, hw i]
    push_cast
    ring

end Torus

theorem matAct_ofInt {k : Fin 3 → ℕ} (M : IntMat) (hM : Compat k M) (v : Fin 3 → ℤ) :
    matAct k M hM (Torus.ofInt k v) = Torus.ofInt k (M *ᵥ v) := by
  funext i
  rw [matAct_apply]
  simp only [Torus.ofInt_apply, entryHom_intCast, Matrix.mulVec, dotProduct, Int.cast_sum]
  exact Finset.sum_congr rfl fun j _ => by push_cast; ring

@[simp] theorem ofCols_mulVec (c a b v : Fin 3 → ℤ) :
    ofCols c a b *ᵥ v = v 0 • c + v 1 • a + v 2 • b := by
  funext i
  simp [ofCols, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem uMat_mulVec (cu : Fin 3 → ℤ) (κ : ℤ) (v : Fin 3 → ℤ) :
    uMat cu κ *ᵥ v = v 0 • cu + v 1 • ![κ, 0, 1] + v 2 • (![0, 1, 0] - κ • cu) := by
  rw [uMat, ofCols_mulVec]

section MatEqAlgebra

variable {k : Fin 3 → ℕ}

theorem MatEq.symm {A B : IntMat} (h : MatEq k A B) : MatEq k B A := fun i j => (h i j).symm

theorem MatEq.trans {A B C : IntMat} (h₁ : MatEq k A B) (h₂ : MatEq k B C) : MatEq k A C :=
  fun i j => (h₁ i j).trans (h₂ i j)

theorem MatEq.mul {A A' B B' : IntMat} (hA : Compat k A) (h₁ : MatEq k A A')
    (h₂ : MatEq k B B') : MatEq k (A * B) (A' * B') := by
  intro i j
  rw [Int.modEq_iff_dvd]
  simp only [Matrix.mul_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun l _ => ?_
  obtain ⟨w, hw⟩ := Int.modEq_iff_dvd.1 (h₂ l j)
  obtain ⟨c, hc⟩ := hA i l
  obtain ⟨u, hu⟩ := Int.modEq_iff_dvd.1 (h₁ i l)
  exact ⟨c * w + u * B' l j, by linear_combination (A i l) * hw + w * hc + (B' l j) * hu⟩

end MatEqAlgebra

namespace SigmaFourAction

variable {k : Fin 3 → ℕ} (S : SigmaFourAction k) (x : Torus k)

theorem φuv_φuv : S.φuv (S.φuv x) = x := DFunLike.congr_fun S.rels.uv_sq x

theorem φu_φu : S.φu (S.φu x) = x := DFunLike.congr_fun S.rels.u_sq x

theorem φρ_φρ_φρ : S.φρ (S.φρ (S.φρ x)) = x := DFunLike.congr_fun S.rels.rho_cube x

theorem φu_φuv : S.φu (S.φuv x) = S.φuv (S.φu x) := DFunLike.congr_fun S.rels.uv_comm_u x

theorem φρ_φu_φρ_φu : S.φρ (S.φu (S.φρ (S.φu x))) = x := DFunLike.congr_fun S.rels.u_rho x

end SigmaFourAction

end CFSG.CGT.Stroth77
