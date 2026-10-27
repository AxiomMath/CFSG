module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43Check
public import CFSG.LieType.Multipliers.U43Field
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43

open CFSG.LieType.Multipliers.U43 (F9)
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check
open Matrix

@[expose] def uncode9 (c : ℕ) : F9 := ⟨(reC c : ZMod 3), (imC c : ZMod 3)⟩

@[expose] def bar9 (x : F9) : F9 := ⟨x.re, -x.im⟩

theorem mulC_lt (c d : ℕ) : mulC c d < 9 := by
  unfold mulC
  have h1 := Nat.mod_lt (reC c * reC d + 2 * (imC c * imC d)) (show 0 < 3 by norm_num)
  have h2 := Nat.mod_lt (reC c * imC d + imC c * reC d) (show 0 < 3 by norm_num)
  omega

theorem addC_lt (c d : ℕ) : addC c d < 9 := by
  unfold addC
  have h1 := Nat.mod_lt (reC c + reC d) (show 0 < 3 by norm_num)
  have h2 := Nat.mod_lt (imC c + imC d) (show 0 < 3 by norm_num)
  omega

theorem negC_lt (c : ℕ) : negC c < 9 := by
  unfold negC
  have h1 := Nat.mod_lt (2 * reC c) (show 0 < 3 by norm_num)
  have h2 := Nat.mod_lt (2 * imC c) (show 0 < 3 by norm_num)
  omega

theorem subC_lt (c d : ℕ) : subC c d < 9 := addC_lt _ _

theorem barC_lt (c : ℕ) : barC c < 9 := by
  unfold barC
  have h1 : reC c < 3 := Nat.mod_lt _ (show 0 < 3 by norm_num)
  have h2 := Nat.mod_lt (2 * imC c) (show 0 < 3 by norm_num)
  omega

theorem uncode9_mulC_aux : ∀ c : Fin 9, ∀ d : Fin 9,
    uncode9 (mulC c d) = uncode9 c * uncode9 d := by decide

theorem uncode9_addC_aux : ∀ c : Fin 9, ∀ d : Fin 9,
    uncode9 (addC c d) = uncode9 c + uncode9 d := by decide

theorem uncode9_negC_aux : ∀ c : Fin 9, uncode9 (negC c) = - uncode9 c := by decide

theorem uncode9_barC_aux : ∀ c : Fin 9, uncode9 (barC c) = bar9 (uncode9 c) := by decide

theorem uncode9_inj_aux : ∀ c : Fin 9, ∀ d : Fin 9, uncode9 c = uncode9 d → c = d := by decide

theorem uncode9_mulC {c d : ℕ} (hc : c < 9) (hd : d < 9) :
    uncode9 (mulC c d) = uncode9 c * uncode9 d := uncode9_mulC_aux ⟨c, hc⟩ ⟨d, hd⟩

theorem uncode9_addC {c d : ℕ} (hc : c < 9) (hd : d < 9) :
    uncode9 (addC c d) = uncode9 c + uncode9 d := uncode9_addC_aux ⟨c, hc⟩ ⟨d, hd⟩

theorem uncode9_negC {c : ℕ} (hc : c < 9) : uncode9 (negC c) = - uncode9 c :=
  uncode9_negC_aux ⟨c, hc⟩

theorem uncode9_subC {c d : ℕ} (hc : c < 9) (hd : d < 9) :
    uncode9 (subC c d) = uncode9 c - uncode9 d := by
  unfold subC
  rw [uncode9_addC hc (negC_lt d), uncode9_negC hd, sub_eq_add_neg]

theorem uncode9_barC {c : ℕ} (hc : c < 9) : uncode9 (barC c) = bar9 (uncode9 c) :=
  uncode9_barC_aux ⟨c, hc⟩

theorem uncode9_inj {c d : ℕ} (hc : c < 9) (hd : d < 9) (h : uncode9 c = uncode9 d) : c = d :=
  congrArg Fin.val (uncode9_inj_aux ⟨c, hc⟩ ⟨d, hd⟩ h)

theorem uncode9_zero : uncode9 0 = 0 := by decide

theorem uncode9_three : uncode9 3 = 1 := by decide

theorem bar9_bar9 (x : F9) : bar9 (bar9 x) = x := by
  revert x
  decide

theorem bar9_mul (x y : F9) : bar9 (x * y) = bar9 x * bar9 y := by
  revert x y
  decide

theorem bar9_add (x y : F9) : bar9 (x + y) = bar9 x + bar9 y := by
  revert x y
  decide

theorem bar9_zero : bar9 0 = 0 := by decide

theorem bar9_one : bar9 1 = 1 := by decide

@[expose] def barRE : F9 ≃+* F9 where
  toFun := bar9
  invFun := bar9
  left_inv := bar9_bar9
  right_inv := bar9_bar9
  map_mul' := bar9_mul
  map_add' := bar9_add

theorem barRE_apply (x : F9) : barRE x = bar9 x := rfl

theorem map_mul_bar9 {m : Type} [Fintype m] (A B : Matrix m m F9) :
    (A * B).map bar9 = A.map bar9 * B.map bar9 :=
  Matrix.map_mul (f := (barRE : F9 →+* F9))

theorem map_map_bar9 {m n : Type} (M : Matrix m n F9) : (M.map bar9).map bar9 = M := by
  refine Matrix.ext fun i j => ?_
  simp [Matrix.map_apply, bar9_bar9]

@[expose] def matC (z : Array ℕ) : Matrix (Fin 4) (Fin 4) F9 :=
  Matrix.of fun i j => uncode9 z[4 * (i : ℕ) + (j : ℕ)]!

theorem mulMat_getElem (x y : Array ℕ) (sw : Bool) {k : ℕ} (hk : k < 16) :
    (mulMat x y sw)[k]! = mulEntry x y sw (k / 4) (k % 4) := by
  unfold mulMat
  rw [getElem!_pos _ _ (by simpa using hk)]
  simp

theorem mulEntry_lt (x y : Array ℕ) (sw : Bool) (i j : ℕ) : mulEntry x y sw i j < 9 :=
  addC_lt _ _

theorem size_mulMat (x y : Array ℕ) (sw : Bool) : (mulMat x y sw).size = 16 := by
  simp [mulMat]

theorem mulMat_lt (x y : Array ℕ) (sw : Bool) {k : ℕ} (hk : k < 16) : (mulMat x y sw)[k]! < 9 := by
  rw [mulMat_getElem x y sw hk]
  exact mulEntry_lt _ _ _ _ _

theorem matC_mulMat {x y : Array ℕ} (sw : Bool) (hx : ∀ k < 16, x[k]! < 9)
    (hy : ∀ k < 16, y[k]! < 9) :
    matC (mulMat x y sw) = matC x * (if sw then (matC y).map bar9 else matC y) := by
  refine Matrix.ext fun i j => ?_
  have hk : 4 * (i : ℕ) + (j : ℕ) < 16 := by omega
  have hd : (4 * (i : ℕ) + (j : ℕ)) / 4 = (i : ℕ) := by omega
  have hm : (4 * (i : ℕ) + (j : ℕ)) % 4 = (j : ℕ) := by omega
  have hx0 : x[4 * (i : ℕ)]! < 9 := hx _ (by omega)
  have hx1 : x[4 * (i : ℕ) + 1]! < 9 := hx _ (by omega)
  have hx2 : x[4 * (i : ℕ) + 2]! < 9 := hx _ (by omega)
  have hx3 : x[4 * (i : ℕ) + 3]! < 9 := hx _ (by omega)
  have hy0 : y[(j : ℕ)]! < 9 := hy _ (by omega)
  have hy1 : y[4 + (j : ℕ)]! < 9 := hy _ (by omega)
  have hy2 : y[8 + (j : ℕ)]! < 9 := hy _ (by omega)
  have hy3 : y[12 + (j : ℕ)]! < 9 := hy _ (by omega)
  simp only [matC, Matrix.of_apply]
  rw [mulMat_getElem x y sw hk, hd, hm]
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  cases sw
  · simp only [mulEntry, Bool.false_eq_true, if_false, Matrix.of_apply]
    rw [uncode9_addC (addC_lt _ _) (mulC_lt _ _), uncode9_addC (addC_lt _ _) (mulC_lt _ _),
      uncode9_addC (mulC_lt _ _) (mulC_lt _ _), uncode9_mulC hx0 hy0, uncode9_mulC hx1 hy1,
      uncode9_mulC hx2 hy2, uncode9_mulC hx3 hy3]
    simp [add_assoc]
  · simp only [mulEntry, if_true, Matrix.of_apply, Matrix.map_apply]
    rw [uncode9_addC (addC_lt _ _) (mulC_lt _ _), uncode9_addC (addC_lt _ _) (mulC_lt _ _),
      uncode9_addC (mulC_lt _ _) (mulC_lt _ _), uncode9_mulC hx0 (barC_lt _),
      uncode9_mulC hx1 (barC_lt _), uncode9_mulC hx2 (barC_lt _), uncode9_mulC hx3 (barC_lt _),
      uncode9_barC hy0, uncode9_barC hy1, uncode9_barC hy2, uncode9_barC hy3]
    simp [add_assoc]


theorem matC_inj {a b : Array ℕ} (ha : a.size = 16) (hb : b.size = 16)
    (ha9 : ∀ k < 16, a[k]! < 9) (hb9 : ∀ k < 16, b[k]! < 9) (h : matC a = matC b) : a = b := by
  apply Array.ext (by rw [ha, hb])
  intro k hka hkb
  have hk : k < 16 := ha ▸ hka
  have h1 := congrFun (congrFun h ⟨k / 4, by omega⟩) ⟨k % 4, by omega⟩
  simp only [matC, Matrix.of_apply] at h1
  have e : 4 * (k / 4) + k % 4 = k := by omega
  rw [e] at h1
  have h2 := uncode9_inj (ha9 k hk) (hb9 k hk) h1
  rwa [getElem!_pos a k hka, getElem!_pos b k hkb] at h2

theorem arr_ext {a b : Array ℕ} {n : ℕ} (ha : a.size = n) (hb : b.size = n)
    (h : ∀ k < n, a[k]! = b[k]!) : a = b := by
  apply Array.ext (by rw [ha, hb])
  intro k hka hkb
  have hk : k < n := ha ▸ hka
  have h1 := h k hk
  rwa [getElem!_pos a k hka, getElem!_pos b k hkb] at h1

theorem getElem_eq_of_matC_eq {a b : Array ℕ} (ha9 : ∀ k < 16, a[k]! < 9)
    (hb9 : ∀ k < 16, b[k]! < 9) (h : matC a = matC b) {k : ℕ} (hk : k < 16) : a[k]! = b[k]! := by
  have h1 := congrFun (congrFun h ⟨k / 4, by omega⟩) ⟨k % 4, by omega⟩
  simp only [matC, Matrix.of_apply] at h1
  have e : 4 * (k / 4) + k % 4 = k := by omega
  rw [e] at h1
  exact uncode9_inj (ha9 k hk) (hb9 k hk) h1

theorem arr17_ext {a b : Array ℕ} (ha : a.size = 17) (hb : b.size = 17)
    (ha9 : ∀ k < 16, a[k]! < 9) (hb9 : ∀ k < 16, b[k]! < 9) (hm : matC a = matC b)
    (h16 : a[16]! = b[16]!) : a = b := by
  refine arr_ext ha hb fun k hk => ?_
  by_cases hk16 : k < 16
  · exact getElem_eq_of_matC_eq ha9 hb9 hm hk16
  · have : k = 16 := by omega
    subst this
    exact h16

theorem matC_idMat : matC idMat = 1 := by
  decide

theorem size_idMat : idMat.size = 16 := rfl

theorem idMat_lt {k : ℕ} (hk : k < 16) : idMat[k]! < 9 := by
  have : ∀ k : Fin 16, idMat[(k : ℕ)]! < 9 := by decide
  exact this ⟨k, hk⟩

theorem size_conjT (z : Array ℕ) : (conjT z).size = 17 := by
  simp [conjT]

theorem conjT_getElem (z : Array ℕ) {k : ℕ} (hk : k < 16) :
    (conjT z)[k]! = barC z[4 * (k % 4) + k / 4]! := by
  unfold conjT
  rw [getElem!_pos _ _ (by simp; omega)]
  simp [hk]

theorem conjT_lt (z : Array ℕ) {k : ℕ} (hk : k < 16) : (conjT z)[k]! < 9 := by
  rw [conjT_getElem z hk]
  exact barC_lt _

theorem matC_conjT {z : Array ℕ} (hz : ∀ k < 16, z[k]! < 9) :
    matC (conjT z) = ((matC z).map bar9)ᵀ := by
  refine Matrix.ext fun i j => ?_
  have hk : 4 * (i : ℕ) + (j : ℕ) < 16 := by omega
  have hm : (4 * (i : ℕ) + (j : ℕ)) % 4 = (j : ℕ) := by omega
  have hd : (4 * (i : ℕ) + (j : ℕ)) / 4 = (i : ℕ) := by omega
  simp only [matC, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [conjT_getElem z hk, hm, hd, uncode9_barC (hz _ (by omega))]

theorem rawValid_iff (z : Array ℕ) : rawValid z = true ↔
    z.size = 17 ∧ (∀ k < 16, z[k]! < 9) ∧ z[16]! < 2 ∧ ((matC z).map bar9)ᵀ * matC z = 1 := by
  simp only [rawValid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, and_assoc]
  refine and_congr_right fun hs => and_congr_right fun h9 => and_congr_right fun h2 => ?_
  constructor
  · intro h
    have h1 := congrArg matC h
    rw [matC_mulMat false (fun k hk => conjT_lt z hk) h9, matC_conjT h9, matC_idMat] at h1
    simpa using h1
  · intro h
    apply matC_inj (size_mulMat _ _ _) size_idMat (fun k hk => mulMat_lt _ _ _ hk)
      (fun k hk => idMat_lt hk)
    rw [matC_mulMat false (fun k hk => conjT_lt z hk) h9, matC_conjT h9, matC_idMat]
    simpa using h

theorem size_mulRaw (x y : Array ℕ) : (mulRaw x y).size = 17 := by
  simp [mulRaw, size_mulMat]

theorem mulRaw_getElem (x y : Array ℕ) {k : ℕ} (hk : k < 16) :
    (mulRaw x y)[k]! = (mulMat x y (x[16]! == 1))[k]! := by
  have hs : k < (mulMat x y (x[16]! == 1)).size := by rw [size_mulMat]; exact hk
  unfold mulRaw
  rw [getElem!_pos _ k (by simp [size_mulMat]; omega), getElem!_pos _ k hs]
  simp [Array.getElem_push_lt hs]

theorem mulRaw_getElem_16 (x y : Array ℕ) : (mulRaw x y)[16]! = (x[16]! + y[16]!) % 2 := by
  unfold mulRaw
  rw [getElem!_pos _ 16 (by simp [size_mulMat])]
  simp [Array.getElem_push, size_mulMat]

theorem mulRaw_lt (x y : Array ℕ) {k : ℕ} (hk : k < 16) : (mulRaw x y)[k]! < 9 := by
  rw [mulRaw_getElem x y hk]
  exact mulMat_lt _ _ _ hk

theorem matC_mulRaw {x y : Array ℕ} (hx : ∀ k < 16, x[k]! < 9) (hy : ∀ k < 16, y[k]! < 9) :
    matC (mulRaw x y) =
      matC x * (if x[16]! = 1 then (matC y).map bar9 else matC y) := by
  have h : matC (mulRaw x y) = matC (mulMat x y (x[16]! == 1)) := by
    refine Matrix.ext fun i j => ?_
    have hk : 4 * (i : ℕ) + (j : ℕ) < 16 := by omega
    simp only [matC, Matrix.of_apply]
    rw [mulRaw_getElem x y hk]
  rw [h, matC_mulMat _ hx hy]
  by_cases h1 : x[16]! = 1 <;> simp [h1]

theorem rawValid_mulRaw {x y : Array ℕ} (hx : rawValid x = true) (hy : rawValid y = true) :
    rawValid (mulRaw x y) = true := by
  rw [rawValid_iff] at hx hy ⊢
  obtain ⟨-, hx9, hx2, hxu⟩ := hx
  obtain ⟨-, hy9, hy2, hyu⟩ := hy
  refine ⟨size_mulRaw x y, fun k hk => mulRaw_lt x y hk, ?_, ?_⟩
  · rw [mulRaw_getElem_16]
    exact Nat.mod_lt _ (by norm_num)
  · rw [matC_mulRaw hx9 hy9]
    have hmap : ∀ M : Matrix (Fin 4) (Fin 4) F9, ((M.map bar9)ᵀ * M = 1) →
        (((M.map bar9).map bar9)ᵀ * M.map bar9 = 1) := fun M hM => by
      rw [map_map_bar9]
      have h2 := congrArg (fun N : Matrix (Fin 4) (Fin 4) F9 => N.map bar9) hM
      simp only [map_mul_bar9, Matrix.transpose_map] at h2
      have h3 : (1 : Matrix (Fin 4) (Fin 4) F9).map bar9 = 1 :=
        Matrix.map_one _ bar9_zero bar9_one
      rw [h3, map_map_bar9] at h2
      simpa [Matrix.transpose_map] using h2
    have hY : (((if x[16]! = 1 then (matC y).map bar9 else matC y).map bar9)ᵀ *
        (if x[16]! = 1 then (matC y).map bar9 else matC y)) = 1 := by
      split_ifs
      · exact hmap _ hyu
      · exact hyu
    calc ((matC x * (if x[16]! = 1 then (matC y).map bar9 else matC y)).map bar9)ᵀ *
          (matC x * (if x[16]! = 1 then (matC y).map bar9 else matC y))
        = ((if x[16]! = 1 then (matC y).map bar9 else matC y).map bar9)ᵀ *
            (((matC x).map bar9)ᵀ * matC x) *
            (if x[16]! = 1 then (matC y).map bar9 else matC y) := by
          rw [map_mul_bar9, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hxu, Matrix.mul_one]; exact hY


theorem det_matC {z : Array ℕ} (hz : ∀ k < 16, z[k]! < 9) : (matC z).det = uncode9 (detC z) := by
  have h0 := hz 0 (by norm_num)
  have h1 := hz 1 (by norm_num)
  have h2 := hz 2 (by norm_num)
  have h3 := hz 3 (by norm_num)
  have h4 := hz 4 (by norm_num)
  have h5 := hz 5 (by norm_num)
  have h6 := hz 6 (by norm_num)
  have h7 := hz 7 (by norm_num)
  have h8 := hz 8 (by norm_num)
  have h9 := hz 9 (by norm_num)
  have h10 := hz 10 (by norm_num)
  have h11 := hz 11 (by norm_num)
  have h12 := hz 12 (by norm_num)
  have h13 := hz 13 (by norm_num)
  have h14 := hz 14 (by norm_num)
  have h15 := hz 15 (by norm_num)
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove, matC, detC,
    det3C, uncode9_subC, uncode9_addC, uncode9_mulC, mulC_lt, addC_lt, subC_lt, h0, h1, h2, h3,
    h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  ring

theorem size_scal (c : ℕ) : (scal c).size = 17 := rfl

theorem scal_getElem_16 (c : ℕ) : (scal c)[16]! = 0 := rfl

theorem scal_getElem (c : ℕ) {k : ℕ} (hk : k < 16) :
    (scal c)[k]! = if k % 5 = 0 then c else 0 := by
  interval_cases k <;> rfl

theorem scal_lt {c : ℕ} (hc : c < 9) {k : ℕ} (hk : k < 16) : (scal c)[k]! < 9 := by
  rw [scal_getElem c hk]
  split_ifs <;> omega

theorem matC_scal {c : ℕ} (hc : c < 9) :
    matC (scal c) = (uncode9 c) • (1 : Matrix (Fin 4) (Fin 4) F9) := by
  refine Matrix.ext fun i j => ?_
  have hk : 4 * (i : ℕ) + (j : ℕ) < 16 := by omega
  simp only [matC, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply]
  rw [scal_getElem c hk]
  fin_cases i <;> fin_cases j <;> simp [uncode9_zero]

theorem mulRaw_scal_getElem {c : ℕ} {z : Array ℕ} (hc : c < 9) (hz : ∀ k < 16, z[k]! < 9) {k : ℕ}
    (hk : k < 16) : (mulRaw (scal c) z)[k]! = mulC c z[k]! := by
  have hmat := matC_mulRaw (fun k hk => scal_lt hc hk) hz
  rw [scal_getElem_16] at hmat
  simp only [show ¬ ((0 : ℕ) = 1) by norm_num, if_false] at hmat
  rw [matC_scal hc, Matrix.smul_mul, Matrix.one_mul] at hmat
  have h1 := congrFun (congrFun hmat ⟨k / 4, by omega⟩) ⟨k % 4, by omega⟩
  have e : 4 * (k / 4) + k % 4 = k := by omega
  simp only [matC, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, e] at h1
  rw [← uncode9_mulC hc (hz k hk)] at h1
  exact uncode9_inj (mulRaw_lt _ _ hk) (mulC_lt _ _) h1

theorem mulRaw_scal_getElem_16 {c : ℕ} {z : Array ℕ} (hz2 : z[16]! < 2) :
    (mulRaw (scal c) z)[16]! = z[16]! := by
  rw [mulRaw_getElem_16, scal_getElem_16]
  omega

theorem mC_lt (u : ℕ) : mC u < 9 := by
  unfold mC
  split <;> omega

theorem size_smulCode (c : ℕ) (z : Array ℕ) : (smulCode c z).size = 17 := by
  simp [smulCode]

theorem smulCode_getElem (c : ℕ) (z : Array ℕ) {k : ℕ} (hk : k < 16) :
    (smulCode c z)[k]! = mulC c z[k]! := by
  unfold smulCode
  rw [getElem!_pos _ _ (by simp; omega)]
  simp [hk]

theorem smulCode_getElem_16 (c : ℕ) (z : Array ℕ) : (smulCode c z)[16]! = z[16]! := by
  unfold smulCode
  rw [getElem!_pos _ _ (by simp)]
  simp

theorem size_normalize (z : Array ℕ) : (normalize z).size = 17 := size_smulCode _ _

theorem normalize_getElem {z : Array ℕ} {k : ℕ} (hk : k < 16) :
    (normalize z)[k]! = mulC (mC (firstNZ z)) z[k]! :=
  smulCode_getElem _ _ hk

theorem normalize_getElem_16 {z : Array ℕ} : (normalize z)[16]! = z[16]! :=
  smulCode_getElem_16 _ _

theorem smulCode_eq_mulRaw {c : ℕ} {z : Array ℕ} (hc : c < 9) (hz : ∀ k < 16, z[k]! < 9)
    (hz2 : z[16]! < 2) : smulCode c z = mulRaw (scal c) z := by
  refine arr_ext (size_smulCode c z) (size_mulRaw _ _) fun k hk => ?_
  by_cases hk16 : k < 16
  · rw [smulCode_getElem c z hk16, mulRaw_scal_getElem hc hz hk16]
  · have : k = 16 := by omega
    subst this
    rw [smulCode_getElem_16, mulRaw_scal_getElem_16 hz2]

theorem normalize_eq_mulRaw {z : Array ℕ} (hz : ∀ k < 16, z[k]! < 9) (hz2 : z[16]! < 2) :
    normalize z = mulRaw (scal (mC (firstNZ z))) z :=
  smulCode_eq_mulRaw (mC_lt _) hz hz2

theorem normalize_lt {z : Array ℕ} {k : ℕ} (hk : k < 16) : (normalize z)[k]! < 9 := by
  rw [normalize_getElem hk]
  exact mulC_lt _ _

theorem find?_congr' {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.find?_cons, List.find?_cons, h a (by simp)]
    cases q a
    · exact find?_congr' p q l (fun b hb => h b (by simp [hb]))
    · rfl

theorem firstNZ_map {f : ℕ → ℕ} (hf0 : f 0 = 0) (hf : ∀ w, w < 9 → (f w ≠ 0 ↔ w ≠ 0))
    {z z' : Array ℕ} (hz : ∀ k < 16, z[k]! < 9) (hzz : ∀ k < 16, z'[k]! = f z[k]!) :
    firstNZ z' = f (firstNZ z) := by
  unfold firstNZ
  have hl : ((List.range 16).map fun k => z'[k]!) =
      ((List.range 16).map fun k => z[k]!).map f := by
    rw [List.map_map]
    refine List.map_congr_left fun k hk => ?_
    simp only [Function.comp_apply]
    exact hzz k (List.mem_range.mp hk)
  rw [hl, List.find?_map]
  have hc : ((List.range 16).map fun k => z[k]!).find?
      ((fun w => decide (w ≠ 0)) ∘ f) =
      ((List.range 16).map fun k => z[k]!).find? fun w => decide (w ≠ 0) := by
    refine find?_congr' _ _ _ fun a ha => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
    simp only [Function.comp_apply, decide_eq_decide]
    exact hf _ (hz k (List.mem_range.mp hk))
  rw [hc]
  cases ((List.range 16).map fun k => z[k]!).find? fun w => decide (w ≠ 0) with
  | none => simp [hf0]
  | some a => rfl

theorem firstNZ_eq_zero {z : Array ℕ} (h : firstNZ z = 0) : ∀ k < 16, z[k]! = 0 := by
  unfold firstNZ at h
  intro k hk
  cases hf : ((List.range 16).map fun k => z[k]!).find? fun w => decide (w ≠ 0) with
  | none =>
    rw [List.find?_eq_none] at hf
    have := hf (z[k]!) (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
    simpa using this
  | some a =>
    have ha := List.find?_some hf
    rw [hf] at h
    simp only [Option.getD_some] at h
    rw [h] at ha
    simp at ha

theorem firstNZ_ne_zero {z : Array ℕ} (hz : rawValid z = true) : firstNZ z ≠ 0 := by
  intro h
  rw [rawValid_iff] at hz
  obtain ⟨-, h9, -, hu⟩ := hz
  have hall := firstNZ_eq_zero h
  have hm : matC z = 0 := by
    refine Matrix.ext fun i j => ?_
    have hk : 4 * (i : ℕ) + (j : ℕ) < 16 := by omega
    simp only [matC, Matrix.of_apply, hall _ hk, uncode9_zero]
    rfl
  rw [hm, Matrix.mul_zero] at hu
  exact zero_ne_one hu


theorem mulC_zero_right (c : ℕ) : mulC c 0 = 0 := by
  simp [mulC, reC, imC]

theorem mulC_ne_zero_iff_aux : ∀ w : Fin 9,
    (mulC 1 w ≠ 0 ↔ (w : ℕ) ≠ 0) ∧ (mulC 2 w ≠ 0 ↔ (w : ℕ) ≠ 0) ∧
    (mulC 3 w ≠ 0 ↔ (w : ℕ) ≠ 0) ∧ (mulC 6 w ≠ 0 ↔ (w : ℕ) ≠ 0) := by decide +kernel

theorem mulC_mC_mulC_aux : ∀ u : Fin 9, (u : ℕ) ≠ 0 → ∀ w : Fin 9,
    mulC (mC (mulC 1 u)) (mulC 1 w) = mulC (mC u) w ∧
    mulC (mC (mulC 2 u)) (mulC 2 w) = mulC (mC u) w ∧
    mulC (mC (mulC 3 u)) (mulC 3 w) = mulC (mC u) w ∧
    mulC (mC (mulC 6 u)) (mulC 6 w) = mulC (mC u) w := by decide +kernel

theorem firstNZ_lt {z : Array ℕ} (h9 : ∀ k < 16, z[k]! < 9) : firstNZ z < 9 := by
  unfold firstNZ
  cases hf : ((List.range 16).map fun k => z[k]!).find? fun w => decide (w ≠ 0) with
  | none => simp
  | some a =>
    obtain ⟨k, hk', hka⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
    simp only [Option.getD_some]
    rw [← hka]
    exact h9 k (List.mem_range.mp hk')

theorem mulC_ne_zero_iff {cc : ℕ} (hcc : cc = 1 ∨ cc = 2 ∨ cc = 3 ∨ cc = 6) {w : ℕ} (hw : w < 9) :
    mulC cc w ≠ 0 ↔ w ≠ 0 := by
  rcases hcc with rfl | rfl | rfl | rfl
  · exact (mulC_ne_zero_iff_aux ⟨w, hw⟩).1
  · exact (mulC_ne_zero_iff_aux ⟨w, hw⟩).2.1
  · exact (mulC_ne_zero_iff_aux ⟨w, hw⟩).2.2.1
  · exact (mulC_ne_zero_iff_aux ⟨w, hw⟩).2.2.2

theorem mulC_mC_mulC {cc : ℕ} (hcc : cc = 1 ∨ cc = 2 ∨ cc = 3 ∨ cc = 6) {u w : ℕ} (hu : u < 9)
    (hu0 : u ≠ 0) (hw : w < 9) : mulC (mC (mulC cc u)) (mulC cc w) = mulC (mC u) w := by
  rcases hcc with rfl | rfl | rfl | rfl
  · exact (mulC_mC_mulC_aux ⟨u, hu⟩ hu0 ⟨w, hw⟩).1
  · exact (mulC_mC_mulC_aux ⟨u, hu⟩ hu0 ⟨w, hw⟩).2.1
  · exact (mulC_mC_mulC_aux ⟨u, hu⟩ hu0 ⟨w, hw⟩).2.2.1
  · exact (mulC_mC_mulC_aux ⟨u, hu⟩ hu0 ⟨w, hw⟩).2.2.2

theorem firstNZ_mulC {z z' : Array ℕ} {cc : ℕ} (hcc : cc = 1 ∨ cc = 2 ∨ cc = 3 ∨ cc = 6)
    (h9 : ∀ k < 16, z[k]! < 9) (hk : ∀ k < 16, z'[k]! = mulC cc z[k]!) :
    firstNZ z' = mulC cc (firstNZ z) :=
  firstNZ_map (mulC_zero_right cc) (fun w hw => mulC_ne_zero_iff hcc hw) h9 hk

theorem normalize_eq_of_mulC {z z' : Array ℕ} (hz : rawValid z = true) (hz' : rawValid z' = true)
    {cc : ℕ} (hcc : cc = 1 ∨ cc = 2 ∨ cc = 3 ∨ cc = 6) (h16 : z'[16]! = z[16]!)
    (hk : ∀ k < 16, z'[k]! = mulC cc z[k]!) : normalize z' = normalize z := by
  have hu := firstNZ_ne_zero hz
  rw [rawValid_iff] at hz hz'
  obtain ⟨-, h9, h2, -⟩ := hz
  obtain ⟨-, h9', h2', -⟩ := hz'
  have hfz := firstNZ_mulC hcc h9 hk
  have hu9 := firstNZ_lt h9
  refine arr_ext (size_normalize z') (size_normalize z) fun k hk17 => ?_
  by_cases hk16 : k < 16
  · rw [normalize_getElem hk16, normalize_getElem hk16, hfz, hk k hk16]
    exact mulC_mC_mulC hcc hu9 hu (h9 k hk16)
  · have : k = 16 := by omega
    subst this
    rw [normalize_getElem_16, normalize_getElem_16, h16]

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43
