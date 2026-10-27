module

public import Certificates.Data.Kernel.ThCentU.Defs
public import CFSG.Certificates.Kernel.Th.Spec.Big
public import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.ThCent.PinSound
public import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.KC.ThCentU

open CFSG.KC.Th CFSG.KC.ThCent CFSG.KC.Th.Spec CFSG.KC.Th.BigS
open CFSG.KC.Misc.Clos (allN_iff letB_eq andB_eq_true)

theorem dig3_eq (a p : ℕ) : dig3 a p = a / 3 ^ p % 3 := rfl

theorem dig3_lt (a p : ℕ) : dig3 a p < 3 := Nat.mod_lt _ (by norm_num)

theorem eq_of_dig3 : ∀ {n x y : ℕ}, x < 3 ^ n → y < 3 ^ n → (∀ q < n, dig3 x q = dig3 y q) → x = y
  | 0, x, y, hx, hy, _ => by simp at hx hy; omega
  | n + 1, x, y, hx, hy, h => by
    have h0 := h 0 (Nat.succ_pos n)
    simp only [dig3_eq, pow_zero, Nat.div_one] at h0
    have hq : x / 3 = y / 3 := by
      refine eq_of_dig3 (n := n) ?_ ?_ fun q hq => ?_
      · rw [pow_succ] at hx
        omega
      · rw [pow_succ] at hy
        omega
      · have := h (q + 1) (by omega)
        simpa only [dig3_eq, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm] using this
    omega

theorem dot5_eq (a b i j : ℕ) :
    dot5 a b i j = ∑ k ∈ Finset.range 5, dig3 a (5 * i + k) * dig3 b (5 * k + j) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rfl

theorem prod5_spec {z a b : ℕ} (h : prod5 z a b = true) :
    z < 3 ^ 25 ∧ ∀ q < 25, dig3 z q = dot5 a b (q / 5) (q % 5) % 3 := by
  obtain ⟨h1, h2⟩ := andB_eq_true h
  refine ⟨by have := Nat.blt_eq.mp h1; norm_num; exact this, fun q hq => ?_⟩
  exact Nat.eq_of_beq_eq_true ((allN_iff _ _).1 h2 q hq)

theorem one5_spec {z : ℕ} (h : one5 z = true) :
    z < 3 ^ 25 ∧ ∀ q < 25, dig3 z q = if q / 5 = q % 5 then 1 else 0 := by
  obtain ⟨h1, h2⟩ := andB_eq_true h
  refine ⟨by have := Nat.blt_eq.mp h1; norm_num; exact this, fun q hq => ?_⟩
  have e : dig3 z q = Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (q / 5) (q % 5)) :=
    Nat.eq_of_beq_eq_true ((allN_iff _ _).1 h2 q hq)
  rw [e]
  by_cases hd : q / 5 = q % 5
  · rw [if_pos hd, show Nat.beq (q / 5) (q % 5) = true from Nat.beq_eq_true_eq _ _ ▸ hd]
  · rw [if_neg hd, beq_false' hd]

theorem tree_ind {G E PA : ℕ → ℕ} {nG N : ℕ} (ht : ∀ k < N, node5 G nG E PA k = true)
    (P : ℕ → Prop) (h0 : ∀ z, one5 z = true → P z)
    (hs : ∀ z a l, l < nG → P a → prod5 z a (G l) = true → P z) : ∀ k < N, P (E k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    cases k with
    | zero => exact h0 _ (ht 0 hk)
    | succ k =>
      have h := ht (k + 1) hk
      change CFSG.KC.LQT.P.letB (PA (k + 1)) (fun r =>
        CFSG.KC.LQT.P.letB (Nat.land r 16777215) fun p =>
          CFSG.KC.LQT.P.letB (Nat.shiftRight r 24) fun l =>
            CFSG.KC.Ord.andB (Nat.blt p (k + 1)) (CFSG.KC.Ord.andB (Nat.blt l nG)
              (prod5 (E (k + 1)) (E p) (G l)))) = true at h
      rw [letB_eq, letB_eq, letB_eq] at h
      obtain ⟨hp, h⟩ := andB_eq_true h
      obtain ⟨hl, h⟩ := andB_eq_true h
      have hp' := Nat.blt_eq.mp hp
      exact hs _ _ _ (Nat.blt_eq.mp hl) (ih _ hp' (by omega)) h

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
include hk

theorem pkMat_wordH (H₁ H₂ : ℕ) (w : List ℕ) :
    pkMat (wordH c rm ONE H₁ H₂ w) =
      (w.map fun l => if l = 0 then pkMat H₁ else pkMat H₂).prod := by
  suffices H : ∀ X, pkMat (wordFromH c rm H₁ H₂ w X) =
      pkMat X * (w.map fun l => if l = 0 then pkMat H₁ else pkMat H₂).prod by
    rw [wordH, H, pkMat_one hk, one_mul]
  induction w with
  | nil =>
    intro X
    change pkMat X = _
    simp
  | cons l w ih =>
    intro X
    change pkMat (strictF (mulB c rm X (Bool.rec (motive := fun _ => ℕ) H₂ H₁ (Nat.beq l 0)))
      (wordFromH c rm H₁ H₂ w)) = _
    rw [strictF_eq, ih, pkMat_mulB hk, List.map_cons, List.prod_cons, mul_assoc]
    congr 2
    by_cases hl : l = 0
    · subst hl
      rfl
    · rw [beq_false' hl, if_neg hl]

omit hk in
theorem pkMat_rpw {M : ℕ → ℕ} (ONE' : ℕ) (h1 : pkMat ONE' = 1) {i : ℕ}
    (hM : pkMat (M (5 + i)) = pkMat (M i) ^ 2) {e : ℕ} (he : e < 3) :
    pkMat (rpw M ONE' i e) = pkMat (M i) ^ e := by
  interval_cases e
  · exact h1
  · change pkMat (M i) = _
    rw [pow_one]
  · exact hM

theorem pkMat_phiK (M : ℕ → ℕ) (hM : ∀ i < 5, pkMat (M (5 + i)) = pkMat (M i) ^ 2) (A j : ℕ) :
    pkMat (phiK c rm ONE M A j) =
      ((List.range 5).map fun i => pkMat (M i) ^ dig3 A (5 * j + i)).prod := by
  suffices H : ∀ n ≤ 5, pkMat (Nat.rec (motive := fun _ => ℕ) ONE
      (fun i acc => strictF (mulB c rm acc
        (rpw M ONE i (dig3 A (Nat.add (Nat.mul 5 j) i)))) fun v => v) n) =
      ((List.range n).map fun i => pkMat (M i) ^ dig3 A (5 * j + i)).prod from H 5 le_rfl
  intro n hn
  induction n with
  | zero => exact pkMat_one hk
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ← ih (by omega)]
    change pkMat (strictF (mulB c rm _ _) fun v => v) = _
    rw [strictF_eq, pkMat_mulB hk, pkMat_rpw ONE (pkMat_one hk) (hM n (by omega)) (dig3_lt _ _)]
    simp

theorem keyK_step (M : ℕ → ℕ) {n : ℕ} (hM : pkMat (M (5 + n)) = pkMat (M n) ^ 2) (acc : ℕ)
    {e : ℕ} (he : e < 3) :
    pkVec (Bool.rec (motive := fun _ => ℕ)
      (strictF (vecB rm acc (Bool.rec (motive := fun _ => ℕ) (M (Nat.add 5 n)) (M n)
        (Nat.beq e 1))) fun v => v) acc (Nat.beq e 0)) =
      Matrix.vecMul (pkVec acc) (pkMat (M n) ^ e) := by
  interval_cases e
  · simp
  · change pkVec (strictF (vecB rm acc (M n)) fun v => v) = _
    rw [strictF_eq, pkVec_vecB hk, pow_one]
  · change pkVec (strictF (vecB rm acc (M (5 + n))) fun v => v) = _
    rw [strictF_eq, pkVec_vecB hk, hM]

theorem keyK_lt (M : ℕ → ℕ) (hv : M 12 < 2 ^ 248) (x : ℕ) : keyK rm M x < 2 ^ 248 := by
  suffices H : ∀ n, (Nat.rec (motive := fun _ => ℕ) (M 12)
      (fun i acc => strictF (dig3 x i) fun e => Bool.rec (motive := fun _ => ℕ)
        (strictF (vecB rm acc (Bool.rec (motive := fun _ => ℕ) (M (Nat.add 5 i)) (M i)
          (Nat.beq e 1))) fun v => v) acc (Nat.beq e 0)) n : ℕ) < 2 ^ 248 from H 5
  have step : ∀ i acc, acc < 2 ^ 248 → (strictF (dig3 x i) fun e => Bool.rec (motive := fun _ => ℕ)
      (strictF (vecB rm acc (Bool.rec (motive := fun _ => ℕ) (M (Nat.add 5 i)) (M i)
        (Nat.beq e 1))) fun v => v) acc (Nat.beq e 0)) < 2 ^ 248 := by
    intro i acc ha
    rw [strictF_eq]
    beta_reduce
    cases Nat.beq (dig3 x i) 0
    · rw [strictF_eq]
      exact vecB_lt hk _ _
    · exact ha
  intro n
  induction n with
  | zero => exact hv
  | succ n ih => exact step n _ ih

theorem pkVec_keyK (M : ℕ → ℕ) (hM : ∀ i < 5, pkMat (M (5 + i)) = pkMat (M i) ^ 2) (x : ℕ) :
    pkVec (keyK rm M x) = Matrix.vecMul (pkVec (M 12))
      ((List.range 5).map fun i => pkMat (M i) ^ dig3 x i).prod := by
  suffices H : ∀ n ≤ 5, pkVec (Nat.rec (motive := fun _ => ℕ) (M 12)
      (fun i acc => strictF (dig3 x i) fun e => Bool.rec (motive := fun _ => ℕ)
        (strictF (vecB rm acc (Bool.rec (motive := fun _ => ℕ) (M (Nat.add 5 i)) (M i)
          (Nat.beq e 1))) fun v => v) acc (Nat.beq e 0)) n) =
      Matrix.vecMul (pkVec (M 12)) ((List.range n).map fun i => pkMat (M i) ^ dig3 x i).prod
    from H 5 le_rfl
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ← Matrix.vecMul_vecMul,
      ← ih (by omega)]
    change pkVec (strictF (dig3 x n) fun e => Bool.rec (motive := fun _ => ℕ)
      (strictF (vecB rm _ (Bool.rec (motive := fun _ => ℕ) (M (Nat.add 5 n)) (M n)
        (Nat.beq e 1))) fun v => v) _ (Nat.beq e 0)) = _
    rw [strictF_eq, keyK_step hk M (hM n (by omega)) _ (dig3_lt x n)]
    simp

end CFSG.KC.ThCentU

end
