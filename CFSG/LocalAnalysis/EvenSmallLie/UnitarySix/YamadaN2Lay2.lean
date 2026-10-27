module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Flag

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem c2C_lt (k : Fin 16) : c2C k < 18 := by revert k; decide

@[expose] def c2F (k : Fin 16) : Fin 18 := ⟨c2C k, c2C_lt k⟩

theorem c2I_lt_iff (c : Fin 18) : c2I c < 16 ↔ clsN c ≠ 0 := by revert c; decide

theorem c2F_c2I (c : Fin 18) (h : c2I c < 16) : c2F ⟨c2I c, h⟩ = c := by revert c; decide

theorem clsN_zero_iff (r : Fin 18) : clsN r = 0 ↔ (r : ℕ) = 0 ∨ (r : ℕ) = 9 := by revert r; decide

@[expose] def r2F (k : Fin 32) : Fin 18 := if (k : ℕ) < 16 then 0 else 9

@[expose] def k16 (k : Fin 32) : Fin 16 := ⟨(k : ℕ) % 16, Nat.mod_lt _ (by norm_num)⟩

@[expose] def emb2M (d : Fin 32 → ZMod 2) : Mat18 :=
  Matrix.of fun r c => if h : c2I c < 16 then
    (if (r : ℕ) = 0 then d ⟨c2I c, by omega⟩ else if (r : ℕ) = 9 then d ⟨16 + c2I c, by omega⟩
      else 0) else 0

@[expose] def blk2M (M : Mat18) : Fin 32 → ZMod 2 := fun k => M (r2F k) (c2F (k16 k))

theorem emb2M_add (d d' : Fin 32 → ZMod 2) : emb2M (d + d') = emb2M d + emb2M d' := by
  ext r c; simp only [emb2M, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp

theorem emb2M_smul (a : ZMod 2) (d : Fin 32 → ZMod 2) : emb2M (a • d) = a • emb2M d := by
  ext r c; simp only [emb2M, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply]
  split_ifs <;> simp

theorem blk2M_add (M N : Mat18) : blk2M (M + N) = blk2M M + blk2M N := by
  ext k; simp [blk2M]

theorem blk2M_smul (a : ZMod 2) (M : Mat18) : blk2M (a • M) = a • blk2M M := by
  ext k; simp [blk2M]

theorem toMat_emb2Bits (d : ℕ) : toMat 18 18 (emb2Bits d) = emb2M (toVec 32 d) := by
  ext r c
  simp only [toMat_apply, emb2Bits, getD_ofFn, emb2M, Matrix.of_apply]
  by_cases hc : c2I c < 16
  · rw [dite_eq_left_of_eq_true (eq_true hc)]
    split_ifs with h0 h9
    · rw [testBit_bitsOf]; simp [c.isLt, hc, toVec]
    · rw [testBit_bitsOf]; simp [c.isLt, hc, toVec]
    · simp
  · rw [dite_eq_right_of_eq_false (eq_false hc)]
    split_ifs with h0 h9
    · rw [testBit_bitsOf]; simp [c.isLt, hc]
    · rw [testBit_bitsOf]; simp [c.isLt, hc]
    · simp

theorem toVec_blk2Bits (A : Array ℕ) : toVec 32 (blk2Bits A) = blk2M (toMat 18 18 A) := by
  ext k
  simp only [toVec, blk2Bits, testBit_bitsOf, k.isLt, decide_true, Bool.true_and, blk2M,
    toMat_apply, r2F, k16, c2F]
  congr 2
  split_ifs <;> rfl

theorem emb2M_blk2M_apply (Δ : Mat18) (r c : Fin 18) :
    emb2M (blk2M Δ) r c = if clsN r = 0 ∧ clsN c ≠ 0 then Δ r c else 0 := by
  simp only [emb2M, blk2M, Matrix.of_apply]
  by_cases hc : c2I c < 16
  · rw [dite_eq_left hc]
    have hcls : clsN c ≠ 0 := (c2I_lt_iff c).mp hc
    have hk1 : k16 ⟨c2I c, by omega⟩ = ⟨c2I c, hc⟩ := Fin.ext (by simp [k16]; omega)
    have hk2 : k16 ⟨16 + c2I c, by omega⟩ = ⟨c2I c, hc⟩ := Fin.ext (by simp [k16]; omega)
    have hr1 : r2F ⟨c2I c, by omega⟩ = 0 := by simp [r2F, hc]
    have hr2 : r2F ⟨16 + c2I c, by omega⟩ = 9 := by simp [r2F]
    by_cases h0 : (r : ℕ) = 0
    · rw [ite_eq_left h0, ite_eq_left ⟨(clsN_zero_iff r).mpr (Or.inl h0), hcls⟩, hk1, hr1,
        c2F_c2I c hc]
      congr 1; exact Fin.ext h0.symm
    · rw [ite_eq_right h0]
      by_cases h9 : (r : ℕ) = 9
      · rw [ite_eq_left h9, ite_eq_left ⟨(clsN_zero_iff r).mpr (Or.inr h9), hcls⟩, hk2, hr2,
          c2F_c2I c hc]
        congr 1; exact Fin.ext h9.symm
      · rw [ite_eq_right h9, ite_eq_right]
        intro h; rcases (clsN_zero_iff r).mp h.1 with h' | h' <;> contradiction
  · rw [dite_eq_right hc]
    have hcls : clsN c = 0 := by
      by_contra h; exact hc ((c2I_lt_iff c).mpr h)
    rw [ite_eq_right (by intro h; exact absurd hcls h.2)]

theorem eq_emb2M {Δ : Mat18} (hΔ : ∀ r c : Fin 18, ¬ (clsN r = 0 ∧ clsN c ≠ 0) → Δ r c = 0) :
    Δ = emb2M (blk2M Δ) := by
  ext r c
  rw [emb2M_blk2M_apply]
  split_ifs with h
  · rfl
  · exact hΔ r c h

theorem rowV1_emb2M (d : Fin 32 → ZMod 2) : RowV1 (emb2M d) := by
  intro r c hr
  have : (r : ℕ) ≠ 0 ∧ (r : ℕ) ≠ 9 := by
    have := (clsN_zero_iff r).not.mp hr; omega
  simp only [emb2M, Matrix.of_apply, this.1, this.2, ↓reduceIte, dite_eq_ite, ite_self]

theorem colNV1_emb2M (d : Fin 32 → ZMod 2) : ColNV1 (emb2M d) := by
  intro r c hc
  have : ¬ c2I c < 16 := fun h => (c2I_lt_iff c).mp h hc
  simp only [emb2M, Matrix.of_apply, this, dite_false]

theorem testBit_catW (w : ℕ) (l : List ℕ) (k i : ℕ) (hi : i < w) :
    (catW w l).testBit (w * k + i) = (l.getD k 0).testBit i := by
  induction l generalizing k with
  | nil => simp [catW]
  | cons a l ih =>
    rw [catW, Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases k with _ | k
    · simp only [mul_zero, zero_add, List.getD_cons_zero, ge_iff_le, show ¬ (w ≤ i) by omega,
        decide_false, Bool.false_and, Bool.or_false]
      rw [Nat.testBit_mod_two_pow]; simp [hi]
    · have h1 : (a % 2 ^ w).testBit (w * (k + 1) + i) = false := by
        rw [Nat.testBit_mod_two_pow]; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not,
          not_lt]; left; nlinarith
      rw [h1, Bool.false_or, List.getD_cons_succ,
        show w * (k + 1) + i - w = w * k + i by rw [Nat.mul_succ]; omega, ih]
      simp only [ge_iff_le, show w ≤ w * (k + 1) + i by nlinarith, decide_true, Bool.true_and]

theorem toVec_cat20 (f : ℕ → ℕ) (k : Fin 20) (i : Fin 32) :
    toVec (20 * 32) (cat20 f) ⟨32 * k + i, by omega⟩ = toVec 32 (f k) i := by
  simp only [toVec, cat20]
  rw [testBit_catW 32 _ k i i.isLt]
  congr 2
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]

theorem toVec_split32 (v : ℕ) (m : ℕ) (i : Fin 32) :
    toVec 32 ((v >>> (32 * m)) % 2 ^ 32) i = bz (v.testBit (32 * m + i)) := by
  simp only [toVec]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp only [i.isLt, decide_true, Bool.true_and]

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
