module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CGT.Stroth77.TorusMat

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Stroth225Frame

theorem two_mul_two_pow_pred_eq_zero (n : ℕ) : (2 : ZMod (2 ^ n)) * 2 ^ (n - 1) = 0 := by
  rcases n with _ | n
  · decide
  · rw [Nat.add_sub_cancel, ← pow_succ']
    exact_mod_cast ZMod.natCast_self (2 ^ (n + 1))

@[expose] def halfHom (n : ℕ) : ZMod 2 →+ ZMod (2 ^ n) :=
  ZMod.lift 2 ⟨zmultiplesHom (ZMod (2 ^ n)) ((2 : ZMod (2 ^ n)) ^ (n - 1)), by
    rw [zmultiplesHom_apply, Nat.cast_ofNat, two_zsmul, ← two_mul]
    exact two_mul_two_pow_pred_eq_zero n⟩

theorem halfHom_zero (n : ℕ) : halfHom n 0 = 0 := map_zero _

theorem halfHom_one (n : ℕ) : halfHom n 1 = 2 ^ (n - 1) := by
  have h : ((1 : ℤ) : ZMod 2) = 1 := Int.cast_one
  rw [← h, halfHom, ZMod.lift_coe]
  simp

@[expose] def torusBar (k : Fin 3 → ℕ) (hk : ∀ i, 1 ≤ k i) : Torus k →+ (Fin 3 → ZMod 2) :=
  Pi.addMonoidHom fun i =>
    (ZMod.castHom (dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp (hk i))) (ZMod 2)).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun j => ZMod (2 ^ k j)) i)

theorem torusBar_apply (k : Fin 3 → ℕ) (hk : ∀ i, 1 ≤ k i) (v : Torus k) (i : Fin 3) :
    torusBar k hk v i = ZMod.cast (v i) := rfl

@[expose] def torusHalf (k : Fin 3 → ℕ) : (Fin 3 → ZMod 2) →+ Torus k :=
  Pi.addMonoidHom fun i => (halfHom (k i)).comp (Pi.evalAddMonoidHom (fun _ => ZMod 2) i)

theorem torusHalf_apply (k : Fin 3 → ℕ) (ε : Fin 3 → ZMod 2) (i : Fin 3) :
    torusHalf k ε i = halfHom (k i) (ε i) := rfl

theorem eq_halfHom_of_two_mul_eq_zero {n : ℕ} (hn : 1 ≤ n) {x : ZMod (2 ^ n)}
    (hx : 2 * x = 0) : ∃ y : ZMod 2, halfHom n y = x := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  have h2 : ((2 * z : ℤ) : ZMod (2 ^ n)) = 0 := by push_cast; exact hx
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have h2' : (2 : ℤ) ^ n' ∣ z := by
    push_cast at h2
    rw [pow_succ'] at h2
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h2
  obtain ⟨w, rfl⟩ := h2'
  refine ⟨(w : ZMod 2), ?_⟩
  rw [halfHom, ZMod.lift_coe]
  simp only [zmultiplesHom_apply, Nat.add_sub_cancel, zsmul_eq_mul]
  push_cast
  ring

theorem two_pow_pred_ne_zero {n : ℕ} (hn : 1 ≤ n) : (2 : ZMod (2 ^ n)) ^ (n - 1) ≠ 0 := by
  intro h
  have h' : (((2 ^ (n - 1) : ℕ) : ℤ) : ZMod (2 ^ n)) = 0 := by exact_mod_cast h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
  have hlt : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have := Int.le_of_dvd (by positivity) h'
  exact absurd (by exact_mod_cast this : 2 ^ n ≤ 2 ^ (n - 1)) (by omega)

theorem halfHom_injective {n : ℕ} (hn : 1 ≤ n) : Function.Injective (halfHom n) := by
  refine (injective_iff_map_eq_zero (halfHom n)).mpr fun y hy => ?_
  fin_cases y
  · rfl
  · exact absurd ((halfHom_one n).symm.trans hy) (two_pow_pred_ne_zero hn)

theorem torusHalf_injective (k : Fin 3 → ℕ) (hk : ∀ i, 1 ≤ k i) :
    Function.Injective (torusHalf k) := fun _ _ h =>
  funext fun i => halfHom_injective (hk i) (congrFun h i)

theorem exists_torusHalf_eq (k : Fin 3 → ℕ) (hk : ∀ i, 1 ≤ k i) {v : Torus k}
    (hv : (2 : ℤ) • v = 0) : ∃ ε, torusHalf k ε = v := by
  have hi : ∀ i, ∃ y : ZMod 2, halfHom (k i) y = v i := fun i =>
    eq_halfHom_of_two_mul_eq_zero (hk i) (by
      have := congrFun hv i
      simpa [two_zsmul, two_mul] using this)
  choose ε hε using hi
  exact ⟨ε, funext hε⟩

theorem torusBar_matAct (k : Fin 3 → ℕ) (hk : ∀ i, 1 ≤ k i) (M : IntMat) (hM : Compat k M)
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hA : ∀ i j, ((M i j : ℤ) : ZMod 2) = A i j)
    (v : Torus k) : torusBar k hk (matAct k M hM v) = A *ᵥ torusBar k hk v := by
  funext i
  have hdi : 2 ∣ 2 ^ k i := dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp (hk i))
  have hcast : ∀ j, ZMod.cast (entryHom k M hM i j (v j)) = A i j * ZMod.cast (v j) := by
    intro j
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective (v j)
    rw [← hz, entryHom_intCast]
    have hdj : 2 ∣ 2 ^ k j := dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp (hk j))
    rw [ZMod.cast_intCast hdi, ZMod.cast_intCast hdj, ← hA i j]
    push_cast
    ring
  rw [torusBar_apply, matAct_apply, Matrix.mulVec, dotProduct, ← ZMod.castHom_apply (h := hdi),
    map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [ZMod.castHom_apply, hcast j, torusBar_apply]

theorem halfHom_eq_intCast (n : ℕ) (y : ZMod 2) :
    halfHom n y = (((2 : ℤ) ^ (n - 1) * (y.val : ℤ) : ℤ) : ZMod (2 ^ n)) := by
  fin_cases y
  · show halfHom n 0 = (((2 : ℤ) ^ (n - 1) * ((0 : ZMod 2).val : ℤ) : ℤ) : ZMod (2 ^ n))
    rw [halfHom_zero, ZMod.val_zero]
    simp
  · show halfHom n 1 = (((2 : ℤ) ^ (n - 1) * ((1 : ZMod 2).val : ℤ) : ℤ) : ZMod (2 ^ n))
    have h1 : (1 : ZMod 2).val = 1 := rfl
    rw [halfHom_one, h1]
    push_cast
    ring

theorem torusBar_torusHalf (k : Fin 3 → ℕ) (hk : ∀ i, 1 ≤ k i) (hk2 : ∀ i, 2 ≤ k i)
    (ε : Fin 3 → ZMod 2) : torusBar k hk (torusHalf k ε) = 0 := by
  funext i
  rw [torusBar_apply, torusHalf_apply, halfHom_eq_intCast,
    ZMod.cast_intCast (dvd_pow_self 2 (by have := hk i; omega)), Pi.zero_apply]
  obtain ⟨n, hn⟩ : ∃ n, k i = n + 2 := ⟨k i - 2, by have := hk2 i; omega⟩
  rw [hn, show n + 2 - 1 = n + 1 by omega]
  push_cast
  rw [pow_succ, show (2 : ZMod 2) = 0 by decide]
  ring

theorem entryHom_halfHom {k : Fin 3 → ℕ} {M : IntMat} (hM : Compat k M) (i j : Fin 3)
    (a y : ZMod 2) (h : (2 : ℤ) ^ k i ∣ 2 ^ (k j - 1) * M i j - 2 ^ (k i - 1) * (a.val : ℤ)) :
    entryHom k M hM i j (halfHom (k j) y) = halfHom (k i) (a * y) := by
  fin_cases y
  · show entryHom k M hM i j (halfHom (k j) 0) = halfHom (k i) (a * 0)
    rw [halfHom_zero, map_zero, mul_zero, halfHom_zero]
  · show entryHom k M hM i j (halfHom (k j) 1) = halfHom (k i) (a * 1)
    rw [mul_one, halfHom_one, halfHom_eq_intCast]
    have h1 : ((2 : ZMod (2 ^ k j)) ^ (k j - 1)) =
        (((2 : ℤ) ^ (k j - 1) : ℤ) : ZMod (2 ^ k j)) := by
      push_cast; rfl
    rw [h1, entryHom_intCast, ZMod.intCast_eq_intCast_iff_dvd_sub]
    have h2 : ((2 ^ k i : ℕ) : ℤ) = (2 : ℤ) ^ k i := by push_cast; rfl
    rw [h2]
    have h3 : (2 : ℤ) ^ (k i - 1) * (a.val : ℤ) - 2 ^ (k j - 1) * M i j =
        -(2 ^ (k j - 1) * M i j - 2 ^ (k i - 1) * (a.val : ℤ)) := by ring
    rw [h3]
    exact (dvd_neg).mpr h

theorem two_dvd_sub_val_of_intCast_eq {z : ℤ} {a : ZMod 2} (h : (z : ZMod 2) = a) :
    (2 : ℤ) ∣ z - (a.val : ℤ) := by
  have ha : (((a.val : ℕ) : ℤ) : ZMod 2) = a := by simp
  rw [← ha, ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have h' : (2 : ℤ) ∣ ((a.val : ℕ) : ℤ) - z := by exact_mod_cast h
  have := dvd_neg.mpr h'
  simpa using this

theorem matAct_torusHalf_familyTwo {k : Fin 3 → ℕ} {m : ℕ} (hk : k = ![m, m + 2, m + 2])
    (hm : 1 ≤ m) (M : IntMat) (hM : Compat k M) (A : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (h00 : ((M 0 0 : ℤ) : ZMod 2) = A 0 0) (h01 : A 0 1 = 0) (h02 : A 0 2 = 0)
    (h10 : (8 : ℤ) ∣ M 1 0 - 4 * ((A 1 0).val : ℤ)) (h11 : ((M 1 1 : ℤ) : ZMod 2) = A 1 1)
    (h12 : ((M 1 2 : ℤ) : ZMod 2) = A 1 2) (h20 : (8 : ℤ) ∣ M 2 0 - 4 * ((A 2 0).val : ℤ))
    (h21 : ((M 2 1 : ℤ) : ZMod 2) = A 2 1) (h22 : ((M 2 2 : ℤ) : ZMod 2) = A 2 2)
    (ε : Fin 3 → ZMod 2) :
    matAct k M hM (torusHalf k ε) = torusHalf k (A *ᵥ ε) := by
  subst hk
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have same : ∀ (n : ℕ) (z : ℤ) (a : ZMod 2), 1 ≤ n → (z : ZMod 2) = a →
      (2 : ℤ) ^ n ∣ 2 ^ (n - 1) * z - 2 ^ (n - 1) * (a.val : ℤ) := by
    intro n z a hn h
    obtain ⟨t, ht⟩ := two_dvd_sub_val_of_intCast_eq h
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    refine ⟨t, ?_⟩
    rw [Nat.add_sub_cancel, ← mul_sub, ht, pow_succ]
    ring
  have key : ∀ i j, (2 : ℤ) ^ (![m + 1, m + 1 + 2, m + 1 + 2] i) ∣
      2 ^ (![m + 1, m + 1 + 2, m + 1 + 2] j - 1) * M i j -
        2 ^ (![m + 1, m + 1 + 2, m + 1 + 2] i - 1) * ((A i j).val : ℤ) := by
    intro i j
    fin_cases i <;> fin_cases j
    · show (2 : ℤ) ^ (m + 1) ∣ 2 ^ (m + 1 - 1) * M 0 0 - 2 ^ (m + 1 - 1) * ((A 0 0).val : ℤ)
      exact same _ _ _ (by omega) h00
    · show (2 : ℤ) ^ (m + 1) ∣ 2 ^ (m + 2) * M 0 1 - 2 ^ m * ((A 0 1).val : ℤ)
      rw [h01, ZMod.val_zero, Nat.cast_zero, mul_zero, sub_zero]
      exact ⟨2 * M 0 1, by ring⟩
    · show (2 : ℤ) ^ (m + 1) ∣ 2 ^ (m + 2) * M 0 2 - 2 ^ m * ((A 0 2).val : ℤ)
      rw [h02, ZMod.val_zero, Nat.cast_zero, mul_zero, sub_zero]
      exact ⟨2 * M 0 2, by ring⟩
    · show (2 : ℤ) ^ (m + 3) ∣ 2 ^ m * M 1 0 - 2 ^ (m + 2) * ((A 1 0).val : ℤ)
      obtain ⟨t, ht⟩ := h10
      exact ⟨t, by linear_combination (2 : ℤ) ^ m * ht⟩
    · show (2 : ℤ) ^ (m + 1 + 2) ∣ 2 ^ (m + 1 + 2 - 1) * M 1 1 -
        2 ^ (m + 1 + 2 - 1) * ((A 1 1).val : ℤ)
      exact same _ _ _ (by omega) h11
    · show (2 : ℤ) ^ (m + 1 + 2) ∣ 2 ^ (m + 1 + 2 - 1) * M 1 2 -
        2 ^ (m + 1 + 2 - 1) * ((A 1 2).val : ℤ)
      exact same _ _ _ (by omega) h12
    · show (2 : ℤ) ^ (m + 3) ∣ 2 ^ m * M 2 0 - 2 ^ (m + 2) * ((A 2 0).val : ℤ)
      obtain ⟨t, ht⟩ := h20
      exact ⟨t, by linear_combination (2 : ℤ) ^ m * ht⟩
    · show (2 : ℤ) ^ (m + 1 + 2) ∣ 2 ^ (m + 1 + 2 - 1) * M 2 1 -
        2 ^ (m + 1 + 2 - 1) * ((A 2 1).val : ℤ)
      exact same _ _ _ (by omega) h21
    · show (2 : ℤ) ^ (m + 1 + 2) ∣ 2 ^ (m + 1 + 2 - 1) * M 2 2 -
        2 ^ (m + 1 + 2 - 1) * ((A 2 2).val : ℤ)
      exact same _ _ _ (by omega) h22
  funext i
  rw [matAct_apply, torusHalf_apply, Matrix.mulVec, dotProduct, map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [torusHalf_apply]
    exact entryHom_halfHom hM i j _ _ (key i j)

end Stroth225Frame

end CFSG.CGT.Stroth77
