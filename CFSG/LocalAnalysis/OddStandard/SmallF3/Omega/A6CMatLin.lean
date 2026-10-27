module

public import Certificates.Data.A6CMat
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Certificates.A6C

@[expose] def A6CToMat (n : ℕ) (x : Mat) : Matrix (Fin n) (Fin n) (ZMod 3) :=
  Matrix.of fun i j => ((x[n * i.val + j.val]! : ℕ) : ZMod 3)

@[expose] def A6CWf (n : ℕ) (x : Mat) : Prop := x.size = n * n ∧ ∀ e ∈ x, e < 3

@[expose] def A6CSimMat {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 3)) : Prop :=
  M * M.transpose = 1 ∨ M * M.transpose = -1

private lemma idx_lt (n : ℕ) (i j : Fin n) : n * i.val + j.val < n * n := by
  calc n * i.val + j.val < n * i.val + n := Nat.add_lt_add_left j.isLt _
    _ = n * (i.val + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * n := Nat.mul_le_mul_left n (Nat.succ_le_of_lt i.isLt)

private lemma idx_div (n : ℕ) (i j : Fin n) :
    (n * i.val + j.val) / n = i.val := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt j.isLt, Nat.zero_add]

private lemma idx_mod (n : ℕ) (i j : Fin n) :
    (n * i.val + j.val) % n = j.val := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]

private lemma foldl_range_add (f : ℕ → ℕ) (n : ℕ) :
    (List.range n).foldl (fun s j => s + f j) 0 = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    rfl

theorem a6c_toMat_mulN (n : ℕ) (x y : Mat) :
    A6CToMat n (mulN n x y) = A6CToMat n x * A6CToMat n y := by
  ext i k
  have hp : n * i.val + k.val < n * n := idx_lt n i k
  simp only [A6CToMat, Matrix.of_apply, Matrix.mul_apply]
  rw [getElem!_pos (mulN n x y) (n * i.val + k.val) (by simpa [mulN] using hp)]
  simp only [mulN, Array.getElem_ofFn, Fin.val_mk]
  rw [idx_div, idx_mod, foldl_range_add, ZMod.natCast_mod, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range
      (fun j => ((x[n * i.val + j]! * y[n * j + k.val]! : ℕ) : ZMod 3))]
  simp [Nat.cast_mul]

theorem a6c_toMat_trN (n : ℕ) (x : Mat) : A6CToMat n (trN n x) = (A6CToMat n x).transpose := by
  ext i j
  have hp : n * i.val + j.val < n * n := idx_lt n i j
  simp only [A6CToMat, Matrix.of_apply, Matrix.transpose_apply]
  rw [getElem!_pos (trN n x) (n * i.val + j.val) (by simpa [trN] using hp)]
  simp only [trN, Array.getElem_ofFn, Fin.val_mk]
  rw [idx_div, idx_mod]

theorem a6c_toMat_negM (n : ℕ) (x : Mat) : A6CToMat n (negM x) = -A6CToMat n x := by
  ext i j
  simp only [A6CToMat, Matrix.of_apply, Matrix.neg_apply, negM]
  by_cases hp : n * i.val + j.val < x.size
  · have hps : n * i.val + j.val < (x.map fun e => (2 * e) % 3).size := by
      simpa using hp
    rw [getElem!_pos (x.map fun e => (2 * e) % 3) _ hps, Array.getElem_map,
      getElem!_pos x _ hp]
    rw [ZMod.natCast_mod, Nat.cast_mul]
    have h2 : ((2 : ℕ) : ZMod 3) = -1 := by decide
    rw [h2, neg_one_mul]
  · have hps : ¬ n * i.val + j.val < (x.map fun e => (2 * e) % 3).size := by
      simpa using hp
    rw [getElem!_neg (x.map fun e => (2 * e) % 3) _ hps, getElem!_neg x _ hp]
    simp

theorem a6c_toMat_idN (n : ℕ) : A6CToMat n (idN n) = 1 := by
  ext i j
  have hp : n * i.val + j.val < n * n := idx_lt n i j
  simp only [A6CToMat, Matrix.of_apply]
  rw [getElem!_pos (idN n) (n * i.val + j.val) (by simpa [idN] using hp)]
  simp only [idN, Array.getElem_ofFn, Fin.val_mk]
  rw [idx_div, idx_mod, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · have hij : i.val ≠ j.val := fun h' => h (Fin.ext h')
    simp [h, hij]

theorem a6c_toMat_addM (n : ℕ) (x y : Mat) (hx : n * n ≤ x.size) :
    A6CToMat n (addM x y) = A6CToMat n x + A6CToMat n y := by
  ext i j
  have hp : n * i.val + j.val < n * n := idx_lt n i j
  have hp' : n * i.val + j.val < x.size := lt_of_lt_of_le hp hx
  simp only [A6CToMat, Matrix.of_apply, Matrix.add_apply]
  rw [getElem!_pos (addM x y) (n * i.val + j.val) (by simpa [addM] using hp')]
  simp only [addM, Array.getElem_ofFn, Fin.val_mk]
  rw [ZMod.natCast_mod, Nat.cast_add]

theorem a6c_toMat_powM (n : ℕ) (x : Mat) (k : ℕ) :
    A6CToMat n (powM n x k) = A6CToMat n x ^ k := by
  induction k with
  | zero =>
    rw [show powM n x 0 = idN n from rfl, a6c_toMat_idN, pow_zero]
  | succ k ih =>
    rw [show powM n x (k + 1) = mulN n x (powM n x k) from rfl, a6c_toMat_mulN, ih,
      pow_succ']

theorem a6c_toMat_conjN (n : ℕ) (g x : Mat) :
    A6CToMat n (conjN n g x) = A6CToMat n g * A6CToMat n x * (A6CToMat n g).transpose := by
  rw [conjN, a6c_toMat_mulN, a6c_toMat_mulN, a6c_toMat_trN]

theorem a6c_wf_mulN (n : ℕ) (x y : Mat) : A6CWf n (mulN n x y) := by
  refine ⟨by simp [mulN], fun e he => ?_⟩
  rw [mulN, Array.mem_ofFn] at he
  obtain ⟨p, rfl⟩ := he
  exact Nat.mod_lt _ (by decide)

theorem a6c_wf_idN (n : ℕ) : A6CWf n (idN n) := by
  refine ⟨by simp [idN], fun e he => ?_⟩
  rw [idN, Array.mem_ofFn] at he
  obtain ⟨p, rfl⟩ := he
  split_ifs <;> decide

theorem a6c_wf_trN (n : ℕ) {x : Mat} (hx : A6CWf n x) : A6CWf n (trN n x) := by
  obtain ⟨hxs, hxl⟩ := hx
  refine ⟨by simp [trN], fun e he => ?_⟩
  rw [trN, Array.mem_ofFn] at he
  obtain ⟨p, rfl⟩ := he
  have hlt : n * (p.val % n) + p.val / n < x.size := by
    rw [hxs]
    have hdiv : p.val / n < n := Nat.div_lt_of_lt_mul p.isLt
    have hn : n ≠ 0 := by
      rintro rfl
      exact absurd p.isLt (by simp)
    have hmod : p.val % n < n := Nat.mod_lt _ (Nat.pos_of_ne_zero hn)
    calc n * (p.val % n) + p.val / n < n * (p.val % n) + n :=
          Nat.add_lt_add_left hdiv _
      _ = n * (p.val % n + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ n * n := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hmod)
  rw [getElem!_pos x _ hlt]
  exact hxl _ (Array.getElem_mem hlt)

theorem a6c_wf_negM (n : ℕ) {x : Mat} (hx : A6CWf n x) : A6CWf n (negM x) := by
  obtain ⟨hxs, hxl⟩ := hx
  refine ⟨by simp [negM, hxs], fun e he => ?_⟩
  rw [negM, Array.mem_map] at he
  obtain ⟨a, _, rfl⟩ := he
  exact Nat.mod_lt _ (by decide)

theorem a6c_wf_powM (n : ℕ) (x : Mat) (k : ℕ) : A6CWf n (powM n x k) := by
  induction k with
  | zero => rw [show powM n x 0 = idN n from rfl]; exact a6c_wf_idN n
  | succ k ih =>
    rw [show powM n x (k + 1) = mulN n x (powM n x k) from rfl]
    exact a6c_wf_mulN n x (powM n x k)

theorem a6c_toMat_injective (n : ℕ) {x y : Mat} (hx : A6CWf n x) (hy : A6CWf n y)
    (h : A6CToMat n x = A6CToMat n y) : x = y := by
  obtain ⟨hxs, hxl⟩ := hx
  obtain ⟨hys, hyl⟩ := hy
  refine Array.ext (hxs.trans hys.symm) fun p hpA hpB => ?_
  have hp : p < n * n := hxs ▸ hpA
  have hdiv : p / n < n := Nat.div_lt_of_lt_mul hp
  have hn : n ≠ 0 := by
    rintro rfl
    exact absurd hp (by simp)
  have hmod : p % n < n := Nat.mod_lt _ (Nat.pos_of_ne_zero hn)
  have key := congrFun (congrFun h ⟨p / n, hdiv⟩) ⟨p % n, hmod⟩
  simp only [A6CToMat, Matrix.of_apply] at key
  have he : n * (p / n) + p % n = p := Nat.div_add_mod p n
  simp only [he] at key
  have hx3 : x[p]! < 3 := by
    rw [getElem!_pos x p hpA]
    exact hxl _ (Array.getElem_mem hpA)
  have hy3 : y[p]! < 3 := by
    rw [getElem!_pos y p hpB]
    exact hyl _ (Array.getElem_mem hpB)
  have hmod3 := (ZMod.natCast_eq_natCast_iff' (x[p]!) (y[p]!) 3).1 key
  rw [Nat.mod_eq_of_lt hx3, Nat.mod_eq_of_lt hy3] at hmod3
  rw [← getElem!_pos x p hpA, ← getElem!_pos y p hpB]
  exact hmod3

end CFSG.OddStandard.SmallF3.Omega
