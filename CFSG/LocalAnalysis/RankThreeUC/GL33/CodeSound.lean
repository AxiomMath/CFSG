module

public import Certificates.Data.GL33.Code
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.GL33

open CFSG.GL33.Native
open scoped Matrix

@[expose] def toM (c : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod 3) := fun i j => (ent c i j : ZMod 3)

@[expose] def toV (v : ℕ) : Fin 3 → ZMod 3 := fun i => (dig v i : ZMod 3)

@[expose] def encode (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) : ℕ :=
  horner [(A 0 0).val, (A 0 1).val, (A 0 2).val, (A 1 0).val, (A 1 1).val, (A 1 2).val,
    (A 2 0).val, (A 2 1).val, (A 2 2).val]

@[expose] def encV (w : Fin 3 → ZMod 3) : ℕ := horner [(w 0).val, (w 1).val, (w 2).val]

theorem dig_horner (l : List ℕ) (k : ℕ) : dig (horner l) k = l.getD k 0 % 3 := by
  induction l generalizing k with
  | nil => simp [horner, dig]
  | cons a l ih =>
    cases k with
    | zero => simp [horner, dig]
    | succ k =>
      have h : (a % 3 + 3 * horner l) / 3 ^ (k + 1) = horner l / 3 ^ k := by
        rw [pow_succ', ← Nat.div_div_eq_div_mul]
        congr 1
        omega
      simp only [dig, horner, List.getD_cons_succ]
      rw [h]
      exact ih k

theorem horner_lt (l : List ℕ) : horner l < 3 ^ l.length := by
  induction l with
  | nil => simp [horner]
  | cons a l ih =>
    simp only [horner, List.length_cons, pow_succ]
    have := Nat.mod_lt a (show 0 < 3 by norm_num)
    omega

private theorem dig_horner_map (f : ℕ → ℕ) {n k : ℕ} (hk : k < n) :
    dig (horner ((List.range n).map f)) k = f k % 3 := by
  rw [dig_horner, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp

private theorem ent_horner_map (f : ℕ → ℕ) {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    ent (horner ((List.range 9).map f)) i j = f (3 * i + j) % 3 :=
  dig_horner_map f (by omega)

private theorem ent_mulC {a b i j : ℕ} (hi : i < 3) (hj : j < 3) :
    ent (mulC a b) i j =
      (ent a i 0 * ent b 0 j + ent a i 1 * ent b 1 j + ent a i 2 * ent b 2 j) % 3 := by
  unfold mulC
  rw [ent_horner_map _ hi hj]
  have h1 : (3 * i + j) / 3 = i := by omega
  have h2 : (3 * i + j) % 3 = j := by omega
  simp only [h1, h2]

theorem toM_mulC (a b : ℕ) : toM (mulC a b) = toM a * toM b := by
  ext x y
  simp only [toM, Matrix.mul_apply]
  rw [ent_mulC x.2 y.2, ZMod.natCast_mod, Fin.sum_univ_three]
  push_cast
  rfl

private theorem ent_oneC : ∀ i < 3, ∀ j < 3, ent oneC i j = if i = j then 1 else 0 := by
  decide

theorem toM_oneC : toM oneC = 1 := by
  ext x y
  simp only [toM, Matrix.one_apply, ent_oneC _ x.2 _ y.2, Fin.val_inj]
  split_ifs <;> simp

theorem toM_powC (a e : ℕ) : toM (powC a e) = toM a ^ e := by
  induction e with
  | zero => simp [powC, toM_oneC]
  | succ e ih => rw [powC, toM_mulC, ih, pow_succ]

private theorem dig_lt (c k : ℕ) : dig c k < 3 := Nat.mod_lt _ (by norm_num)

private theorem natCast_inj3 {m n : ℕ} (hm : m < 3) (hn : n < 3) :
    (m : ZMod 3) = n ↔ m = n := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn]

theorem toV_vecC (c v : ℕ) : toV (vecC c v) = toM c *ᵥ toV v := by
  funext x
  simp only [toV, toM, vecC, Matrix.mulVec, dotProduct]
  rw [dig_horner_map _ x.2, ZMod.natCast_mod, Fin.sum_univ_three]
  push_cast
  rfl

theorem toV_covC (f c : ℕ) : toV (covC f c) = toV f ᵥ* toM c := by
  funext y
  simp only [toV, toM, covC, Matrix.vecMul, dotProduct]
  rw [dig_horner_map _ y.2, ZMod.natCast_mod, Fin.sum_univ_three]
  push_cast
  rfl

theorem toM_encode (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) : toM (encode A) = A := by
  ext x y
  fin_cases x <;> fin_cases y <;> simp [toM, encode, ent, dig_horner]

theorem encode_lt (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) : encode A < 3 ^ 9 := by
  unfold encode
  exact lt_of_lt_of_eq (horner_lt _) (by simp)

theorem toV_encV (w : Fin 3 → ZMod 3) : toV (encV w) = w := by
  funext x
  fin_cases x <;> simp [toV, encV, dig_horner]

theorem encV_lt (w : Fin 3 → ZMod 3) : encV w < 27 := by
  unfold encV
  exact lt_of_lt_of_eq (horner_lt _) (by simp)

theorem toV_zero : toV 0 = 0 := by
  funext x
  simp [toV, dig]

private theorem dig_div (a k : ℕ) : dig (a / 3) k = dig a (k + 1) := by
  simp only [dig, Nat.div_div_eq_div_mul, pow_succ']

private theorem eq_of_dig_eq : ∀ (n a b : ℕ), a < 3 ^ n → b < 3 ^ n →
    (∀ k < n, dig a k = dig b k) → a = b
  | 0, a, b, ha, hb, _ => by simp at ha hb; omega
  | n + 1, a, b, ha, hb, h => by
    have h0 := h 0 (by omega)
    have h1 : a / 3 = b / 3 := by
      refine eq_of_dig_eq n _ _ ?_ ?_ fun k hk => ?_
      · rw [pow_succ] at ha; omega
      · rw [pow_succ] at hb; omega
      · rw [dig_div, dig_div]; exact h (k + 1) (by omega)
    simp only [dig, pow_zero, Nat.div_one] at h0
    omega

private theorem ent_eq_of_toM_eq {a b : ℕ} (h : toM a = toM b) {i j : ℕ} (hi : i < 3)
    (hj : j < 3) : ent a i j = ent b i j := by
  have := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
  simp only [toM] at this
  exact (natCast_inj3 (dig_lt _ _) (dig_lt _ _)).1 this

theorem eq_of_toM_eq {a b : ℕ} (ha : a < 3 ^ 9) (hb : b < 3 ^ 9) (h : toM a = toM b) :
    a = b := by
  refine eq_of_dig_eq 9 a b ha hb fun k hk => ?_
  have := ent_eq_of_toM_eq h (i := k / 3) (j := k % 3) (by omega) (by omega)
  simpa [ent, Nat.div_add_mod] using this

theorem eq_of_toV_eq {u v : ℕ} (hu : u < 27) (hv : v < 27) (h : toV u = toV v) : u = v := by
  refine eq_of_dig_eq 3 u v (by simpa using hu) (by simpa using hv) fun k hk => ?_
  have := congrFun h ⟨k, hk⟩
  simp only [toV] at this
  exact (natCast_inj3 (dig_lt _ _) (dig_lt _ _)).1 this

theorem vecC_lt (c v : ℕ) : vecC c v < 27 := by
  unfold vecC
  exact lt_of_lt_of_eq (horner_lt _) (by simp)

theorem covC_lt (f c : ℕ) : covC f c < 27 := by
  unfold covC
  exact lt_of_lt_of_eq (horner_lt _) (by simp)

theorem mulC_lt (a b : ℕ) : mulC a b < 3 ^ 9 := by
  unfold mulC
  exact lt_of_lt_of_eq (horner_lt _) (by simp)

theorem det_toM (c : ℕ) : (toM c).det = (detC c : ZMod 3) := by
  have h2 : (2 : ZMod 3) = -1 := by decide
  rw [Matrix.det_fin_three]
  simp only [detC, toM, ZMod.natCast_mod]
  push_cast
  rw [h2]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  ring

theorem mem_glCodes_iff (c : ℕ) : c ∈ glCodes () ↔ c < 3 ^ 9 ∧ (toM c).det ≠ 0 := by
  have hlt : detC c < 3 := Nat.mod_lt _ (by norm_num)
  have hdet : (toM c).det ≠ 0 ↔ detC c ≠ 0 := by
    rw [det_toM, Ne, Ne, ZMod.natCast_eq_zero_iff]
    omega
  rw [hdet]
  simp only [glCodes, List.mem_filter, List.mem_range, bne_iff_ne, ne_eq]
  norm_num

end CFSG.GL33

end
