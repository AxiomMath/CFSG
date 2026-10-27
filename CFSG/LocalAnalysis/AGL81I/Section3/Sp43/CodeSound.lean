module

public import Certificates.Data.Sp43.Code
public import Mathlib.LinearAlgebra.SymplecticGroup

public section

namespace CFSG.Sp43

open CFSG.Sp43.Native
open scoped Matrix

@[expose] def ix : Fin 2 ⊕ Fin 2 → ℕ
  | .inl i => i
  | .inr i => 2 + i

@[expose] def idx (k : ℕ) : Fin 2 ⊕ Fin 2 :=
  if h : k < 2 then .inl ⟨k, h⟩ else if h' : k < 4 then .inr ⟨k - 2, by omega⟩ else .inl 0

@[expose] def toM (c : ℕ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  fun a b => (ent c (ix a) (ix b) : ZMod 3)

@[expose] def toV (v : ℕ) : Fin 2 ⊕ Fin 2 → ZMod 3 := fun a => (dig v (ix a) : ZMod 3)

@[expose] def encode (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) : ℕ :=
  horner ((List.range 16).map fun k => (A (idx (k / 4)) (idx (k % 4))).val)

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

private theorem ix_lt (a : Fin 2 ⊕ Fin 2) : ix a < 4 := by
  rcases a with i | i <;> simp only [ix] <;> omega

private theorem ix_idx {k : ℕ} (hk : k < 4) : ix (idx k) = k := by
  unfold idx
  split_ifs with h <;> simp [ix]
  omega

private theorem ix_inj {a b : Fin 2 ⊕ Fin 2} : ix a = ix b ↔ a = b := by
  rcases a with ⟨i, hi⟩ | ⟨i, hi⟩ <;> rcases b with ⟨j, hj⟩ | ⟨j, hj⟩ <;> simp [ix] <;> omega

private theorem idx_ix (a : Fin 2 ⊕ Fin 2) : idx (ix a) = a :=
  ix_inj.1 (ix_idx (ix_lt a))

private theorem sum_ix {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ k : Fin 2 ⊕ Fin 2, g (ix k) = g 0 + g 1 + g 2 + g 3 := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [ix, Fin.val_zero, Fin.val_one]
  abel

private theorem ent_horner_map (f : ℕ → ℕ) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    ent (horner ((List.range 16).map f)) i j = f (4 * i + j) % 3 :=
  dig_horner_map f (by omega)

private theorem ent_mulC {a b i j : ℕ} (hi : i < 4) (hj : j < 4) :
    ent (mulC a b) i j = (ent a i 0 * ent b 0 j + ent a i 1 * ent b 1 j + ent a i 2 * ent b 2 j +
      ent a i 3 * ent b 3 j) % 3 := by
  unfold mulC
  rw [ent_horner_map _ hi hj]
  have h1 : (4 * i + j) / 4 = i := by omega
  have h2 : (4 * i + j) % 4 = j := by omega
  simp only [h1, h2]

theorem toM_mulC (a b : ℕ) : toM (mulC a b) = toM a * toM b := by
  ext x y
  simp only [toM, Matrix.mul_apply]
  rw [ent_mulC (ix_lt x) (ix_lt y), ZMod.natCast_mod,
    sum_ix (fun m => (ent a (ix x) m : ZMod 3) * (ent b m (ix y) : ZMod 3))]
  push_cast
  rfl

private theorem ent_oneC : ∀ i < 4, ∀ j < 4, ent oneC i j = if i = j then 1 else 0 := by
  decide

theorem toM_oneC : toM oneC = 1 := by
  ext x y
  simp only [toM, Matrix.one_apply, ent_oneC _ (ix_lt x) _ (ix_lt y), ix_inj]
  split_ifs <;> simp

private theorem dig_lt (c k : ℕ) : dig c k < 3 := Nat.mod_lt _ (by norm_num)

private theorem natCast_inj3 {m n : ℕ} (hm : m < 3) (hn : n < 3) :
    (m : ZMod 3) = n ↔ m = n := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn]

theorem toV_vecC (c v : ℕ) : toV (vecC c v) = toM c *ᵥ toV v := by
  funext x
  simp only [toV, toM, vecC, Matrix.mulVec, dotProduct]
  rw [dig_horner_map _ (ix_lt x), ZMod.natCast_mod,
    sum_ix (fun m => (ent c (ix x) m : ZMod 3) * (dig v m : ZMod 3))]
  push_cast
  rfl

theorem toM_encode (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) :
    toM (encode A) = A := by
  ext x y
  simp only [toM, encode]
  rw [ent_horner_map _ (ix_lt x) (ix_lt y)]
  have hy := ix_lt y
  have h1 : (4 * ix x + ix y) / 4 = ix x := by omega
  have h2 : (4 * ix x + ix y) % 4 = ix y := by omega
  rw [h1, h2, idx_ix, idx_ix, ZMod.natCast_mod, ZMod.natCast_zmod_val]

theorem encode_lt (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) : encode A < 3 ^ 16 := by
  unfold encode
  exact lt_of_lt_of_eq (horner_lt _) (by simp)

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

private theorem ent_eq_of_toM_eq {a b : ℕ} (h : toM a = toM b) {i j : ℕ} (hi : i < 4)
    (hj : j < 4) : ent a i j = ent b i j := by
  have := congrFun (congrFun h (idx i)) (idx j)
  simp only [toM, ix_idx hi, ix_idx hj] at this
  exact (natCast_inj3 (dig_lt _ _) (dig_lt _ _)).1 this

theorem eq_of_toM_eq {a b : ℕ} (ha : a < 3 ^ 16) (hb : b < 3 ^ 16) (h : toM a = toM b) :
    a = b := by
  refine eq_of_dig_eq 16 a b ha hb fun k hk => ?_
  have := ent_eq_of_toM_eq h (i := k / 4) (j := k % 4) (by omega) (by omega)
  simpa [ent, Nat.div_add_mod] using this

theorem eq_of_toV_eq {u v : ℕ} (hu : u < 81) (hv : v < 81) (h : toV u = toV v) : u = v := by
  refine eq_of_dig_eq 4 u v (by simpa using hu) (by simpa using hv) fun k hk => ?_
  have := congrFun h (idx k)
  simp only [toV, ix_idx hk] at this
  exact (natCast_inj3 (dig_lt _ _) (dig_lt _ _)).1 this

theorem vecC_lt (c v : ℕ) : vecC c v < 81 := by
  unfold vecC
  exact lt_of_lt_of_eq (horner_lt _) (by simp)

theorem mulC_lt (a b : ℕ) : mulC a b < 3 ^ 16 := by
  unfold mulC
  exact lt_of_lt_of_eq (horner_lt _) (by simp)

private theorem omg_lt (x y : ℕ) : omg x y < 3 := Nat.mod_lt _ (by norm_num)

private theorem omg_cast (x y : ℕ) : (omg x y : ZMod 3) =
    2 * ((dig x 0 : ZMod 3) * dig y 2) + 2 * ((dig x 1 : ZMod 3) * dig y 3) +
      (dig x 2 : ZMod 3) * dig y 0 + (dig x 3 : ZMod 3) * dig y 1 := by
  simp only [omg, ZMod.natCast_mod]
  push_cast
  rfl

private theorem dig_row (c i j : ℕ) (hj : j < 4) : dig (c / 81 ^ i % 81) j = ent c i j := by
  have h : 3 ^ (4 * i + j) = 81 ^ i * 3 ^ j := by
    rw [pow_add, pow_mul]
    norm_num
  simp only [ent, dig, h, ← Nat.div_div_eq_div_mul]
  generalize c / 81 ^ i = t
  interval_cases j <;> omega

private theorem omg_row (c i i' : ℕ) :
    (omg (c / 81 ^ i % 81) (c / 81 ^ i' % 81) : ZMod 3) =
      2 * ((ent c i 0 : ZMod 3) * ent c i' 2) + 2 * ((ent c i 1 : ZMod 3) * ent c i' 3) +
        (ent c i 2 : ZMod 3) * ent c i' 0 + (ent c i 3 : ZMod 3) * ent c i' 1 := by
  rw [omg_cast, dig_row c i 0 (by norm_num), dig_row c i 1 (by norm_num),
    dig_row c i 2 (by norm_num), dig_row c i 3 (by norm_num), dig_row c i' 0 (by norm_num),
    dig_row c i' 1 (by norm_num), dig_row c i' 2 (by norm_num), dig_row c i' 3 (by norm_num)]

private theorem mem_spCodes_iff' (c : ℕ) :
    c ∈ spCodes () ↔ ∃ r0 r1 r2 r3, r0 < 81 ∧ r1 < 81 ∧ r2 < 81 ∧ r3 < 81 ∧
      omg r2 r3 = 0 ∧ omg r1 r2 = 0 ∧ omg r1 r3 = 2 ∧ omg r0 r1 = 0 ∧ omg r0 r2 = 2 ∧
      omg r0 r3 = 0 ∧ c = r0 + 81 * r1 + 6561 * r2 + 531441 * r3 := by
  simp only [spCodes, List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_range,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨r3, h3, r2, ⟨h2, h23⟩, r1, ⟨h1, h12, h13⟩, r0, ⟨h0, ⟨h01, h02⟩, h03⟩, rfl⟩
    exact ⟨r0, r1, r2, r3, h0, h1, h2, h3, h23, h12, h13, h01, h02, h03, rfl⟩
  · rintro ⟨r0, r1, r2, r3, h0, h1, h2, h3, h23, h12, h13, h01, h02, h03, rfl⟩
    exact ⟨r3, h3, r2, ⟨h2, h23⟩, r1, ⟨h1, h12, h13⟩, r0, ⟨h0, ⟨h01, h02⟩, h03⟩, rfl⟩

private theorem toM_J_toM (c : ℕ) (a b : Fin 2 ⊕ Fin 2) :
    (toM c * Matrix.J (Fin 2) (ZMod 3) * (toM c)ᵀ) a b =
      (omg (c / 81 ^ ix a % 81) (c / 81 ^ ix b % 81) : ZMod 3) := by
  have h2 : (2 : ZMod 3) = -1 := by decide
  have e0 : ix (.inl 0) = 0 := rfl
  have e1 : ix (.inl 1) = 1 := rfl
  have e2 : ix (.inr 0) = 2 := rfl
  have e3 : ix (.inr 1) = 3 := rfl
  rw [omg_row]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    toM, e0, e1, e2, e3]
  simp [Matrix.J]
  rw [h2]
  ring

private theorem mem_sp_iff (c : ℕ) :
    toM c ∈ Matrix.symplecticGroup (Fin 2) (ZMod 3) ↔
      ∀ a b, (omg (c / 81 ^ ix a % 81) (c / 81 ^ ix b % 81) : ZMod 3) =
        Matrix.J (Fin 2) (ZMod 3) a b := by
  rw [SymplecticGroup.mem_iff, ← Matrix.ext_iff]
  simp only [toM_J_toM]

private theorem omg_swap (x y : ℕ) : (omg y x : ZMod 3) = -(omg x y : ZMod 3) := by
  have h2 : (2 : ZMod 3) = -1 := by decide
  rw [omg_cast, omg_cast, h2]
  ring

private theorem omg_self (x : ℕ) : (omg x x : ZMod 3) = 0 := by
  have h2 : (2 : ZMod 3) = -1 := by decide
  rw [omg_cast, h2]
  ring

private theorem omg_eq_zero {x y : ℕ} (h : (omg x y : ZMod 3) = 0) : omg x y = 0 :=
  (natCast_inj3 (omg_lt x y) (by norm_num)).1 (by simpa using h)

private theorem omg_eq_two {x y : ℕ} (h : (omg x y : ZMod 3) = -1) : omg x y = 2 := by
  refine (natCast_inj3 (omg_lt x y) (by norm_num)).1 ?_
  rw [h]
  decide

theorem mem_spCodes_iff (c : ℕ) :
    c ∈ spCodes () ↔ c < 3 ^ 16 ∧ toM c ∈ Matrix.symplecticGroup (Fin 2) (ZMod 3) := by
  rw [mem_spCodes_iff', mem_sp_iff]
  constructor
  · rintro ⟨r0, r1, r2, r3, h0, h1, h2, h3, h23, h12, h13, h01, h02, h03, hc⟩
    refine ⟨by norm_num; omega, ?_⟩
    have hr0 : c / 81 ^ ix (.inl 0) % 81 = r0 := by simp [ix]; omega
    have hr1 : c / 81 ^ ix (.inl 1) % 81 = r1 := by simp [ix]; omega
    have hr2 : c / 81 ^ ix (.inr 0) % 81 = r2 := by simp [ix]; omega
    have hr3 : c / 81 ^ ix (.inr 1) % 81 = r3 := by simp [ix]; omega
    have e01 : (omg r0 r1 : ZMod 3) = 0 := by rw [h01]; rfl
    have e02 : (omg r0 r2 : ZMod 3) = -1 := by rw [h02]; decide
    have e03 : (omg r0 r3 : ZMod 3) = 0 := by rw [h03]; rfl
    have e12 : (omg r1 r2 : ZMod 3) = 0 := by rw [h12]; rfl
    have e13 : (omg r1 r3 : ZMod 3) = -1 := by rw [h13]; decide
    have e23 : (omg r2 r3 : ZMod 3) = 0 := by rw [h23]; rfl
    simp only [Sum.forall, Fin.forall_fin_two, hr0, hr1, hr2, hr3]
    simp [Matrix.J, omg_self, omg_swap r0 r1, omg_swap r0 r2, omg_swap r0 r3, omg_swap r1 r2,
      omg_swap r1 r3, omg_swap r2 r3, e01, e02, e03, e12, e13, e23]
  · rintro ⟨hc, hmem⟩
    have hr0 : c / 81 ^ ix (.inl 0) % 81 = c % 81 := by simp [ix]
    have hr1 : c / 81 ^ ix (.inl 1) % 81 = c / 81 % 81 := by simp [ix]
    have hr2 : c / 81 ^ ix (.inr 0) % 81 = c / 6561 % 81 := by simp [ix]
    have hr3 : c / 81 ^ ix (.inr 1) % 81 = c / 531441 % 81 := by simp [ix]
    have h01 := hmem (.inl 0) (.inl 1)
    have h02 := hmem (.inl 0) (.inr 0)
    have h03 := hmem (.inl 0) (.inr 1)
    have h12 := hmem (.inl 1) (.inr 0)
    have h13 := hmem (.inl 1) (.inr 1)
    have h23 := hmem (.inr 0) (.inr 1)
    simp only [hr0, hr1, hr2, hr3] at h01 h02 h03 h12 h13 h23
    simp [Matrix.J] at h01 h02 h03 h12 h13 h23
    norm_num at hc
    exact ⟨c % 81, c / 81 % 81, c / 6561 % 81, c / 531441 % 81, by omega, by omega, by omega,
      by omega, omg_eq_zero h23, omg_eq_zero h12, omg_eq_two h13, omg_eq_zero h01,
      omg_eq_two h02, omg_eq_zero h03, by omega⟩

end CFSG.Sp43

end
