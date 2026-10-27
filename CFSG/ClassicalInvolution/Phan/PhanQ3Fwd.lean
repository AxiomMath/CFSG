module

public import CFSG.ClassicalInvolution.Phan.PhanQ2Act
public import CFSG.ClassicalInvolution.Phan.PhanP15Dict

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

section ColStd

variable {F : Type} [Field F] {ε : F}

@[expose] def ColStd (ε : F) (k : spinGroup (quadPlus 4 F)) : Prop := ColP ε (z0 ε) (k • z0 ε)

theorem colStd_mul_right (hε : ε ≠ 0) {k g : spinGroup (quadPlus 4 F)} {s t : F}
    {hst : s ^ 2 + t ^ 2 / ε = 1} (h : g • z0 ε = (z0 ε).rot hε s t hst) :
    ColStd ε (k * g) ↔ ColStd ε k := by
  unfold ColStd
  rw [NPair.mul_smul', h, smul_rot, colP_rot_right]

theorem colStd_mul_left (hε : ε ≠ 0) {k g : spinGroup (quadPlus 4 F)} {s t : F}
    {hst : s ^ 2 + t ^ 2 / ε = 1} (h : g • z0 ε = (z0 ε).rot hε s t hst) :
    ColStd ε (g * k) ↔ ColStd ε k := by
  have hst' : s ^ 2 + (-t) ^ 2 / ε = 1 := by rw [neg_sq]; exact hst
  unfold ColStd
  rw [NPair.mul_smul', ← colP_smul g⁻¹, NPair.inv_smul_smul', inv_smul_z0_of_rot hε hst' h,
    colP_rot_left]

end ColStd

section Parab

variable {p e : ℕ} [Fact p.Prime]

theorem exists_rot_of_mem_parab (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    {g : spinGroup (quadPlus 4 (GaloisField p e))} (hg : g ∈ parab M.S {1, 2, 3}) :
    ∃ (s t : GaloisField p e) (hst : s ^ 2 + t ^ 2 / M.ε = 1),
      g • z0 M.ε = (z0 M.ε).rot M.hε s t hst :=
  exists_rot_of_stabJ (two_ne_zero_gf hp2 e)
    (parab_le_stabJ (StdModel.card_K hq) M.good M.spec (two_ne_zero_gf hp2 e)
      (two_ne_zero_gf hp2 (2 * e)) hg)

theorem mem_parab_of_rot (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    {g : spinGroup (quadPlus 4 (GaloisField p e))} {s t : GaloisField p e}
    {hst : s ^ 2 + t ^ 2 / M.ε = 1} (h : g • z0 M.ε = (z0 M.ε).rot M.hε s t hst) :
    g ∈ parab M.S {1, 2, 3} :=
  stabJ_le_parab M hp2 hq (mem_stabJ_of_rot (two_ne_zero_gf hp2 e) M.hε h)

end Parab

section RankOne

variable {F : Type} [Field F] {ε : F}

theorem B8_incl0 (X Y : Matrix (Fin 2) (Fin 2) F) :
    B8 ((frame0 (F := F)).incl X) ((frame0 (F := F)).incl Y) =
      X 1 1 * Y 0 0 + X 0 0 * Y 1 1 - X 1 0 * Y 0 1 - X 0 1 * Y 1 0 := by
  rw [B8, Frame.polar_incl_right, Frame.coords_incl]

theorem z0_x_eq (ε : F) : (z0 ε).x = (frame0 (F := F)).incl 1 := rfl

theorem z0_y_eq (ε : F) : (z0 ε).y = (frame0 (F := F)).incl (Jm ε) := jOp_vecA1 ε

theorem smul_z0_of_La (ε : F) {r : spinGroup (quadPlus 4 F)} {A : SL(2, F)}
    (hA : (frame0 (F := F)).La A = spinAction (quadPlus 4 F) r) :
    (r • z0 ε).x = (frame0 (F := F)).incl (A : Matrix (Fin 2) (Fin 2) F) ∧
      (r • z0 ε).y = (frame0 (F := F)).incl ((A : Matrix (Fin 2) (Fin 2) F) * Jm ε) := by
  constructor
  · rw [NPair.smul_x, z0_x_eq, ← hA, Frame.La_apply_incl, mul_one]
  · rw [NPair.smul_y, z0_y_eq, ← hA, Frame.La_apply_incl]

theorem numbers_of_La (ε : F) {r : spinGroup (quadPlus 4 F)} {A : SL(2, F)}
    (hA : (frame0 (F := F)).La A = spinAction (quadPlus 4 F) r) :
    B8 (z0 ε).x (r • z0 ε).x = (A : Matrix (Fin 2) (Fin 2) F) 0 0 + A 1 1 ∧
      B8 (z0 ε).y (r • z0 ε).x = (A : Matrix (Fin 2) (Fin 2) F) 1 0 - ε * A 0 1 ∧
      B8 (z0 ε).x (r • z0 ε).y = ε * (A : Matrix (Fin 2) (Fin 2) F) 0 1 - A 1 0 ∧
      B8 (z0 ε).y (r • z0 ε).y = ε * ((A : Matrix (Fin 2) (Fin 2) F) 0 0 + A 1 1) := by
  obtain ⟨hx, hy⟩ := smul_z0_of_La ε hA
  rw [hx, hy, z0_x_eq, z0_y_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [B8_incl0]
    simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]
    try ring

theorem FJ_of_sum_sq (hε : ε ≠ 0) (hnsq : ¬ IsSquare (-ε)) {a b : F}
    (h : a ^ 2 + b ^ 2 / ε = 0) : a = 0 ∧ b = 0 := by
  have h' : ε * a ^ 2 + b ^ 2 = 0 := by
    field_simp at h
    linear_combination h
  by_cases ha : a = 0
  · refine ⟨ha, ?_⟩
    rw [ha] at h'
    simpa using h'
  · exfalso
    apply hnsq
    refine ⟨b / a, ?_⟩
    field_simp
    linear_combination -h'

theorem colP_of_La (hε : ε ≠ 0) (hnsq : ¬ IsSquare (-ε)) {r : spinGroup (quadPlus 4 F)}
    {A : SL(2, F)} (hA : (frame0 (F := F)).La A = spinAction (quadPlus 4 F) r)
    (hnot : ¬ ((A : Matrix (Fin 2) (Fin 2) F) 1 1 = A 0 0 ∧ (A : Matrix (Fin 2) (Fin 2) F) 1 0 =
      -ε * A 0 1)) : ColP ε (z0 ε) (r • z0 ε) := by
  obtain ⟨n1, n2, n3, n4⟩ := numbers_of_La ε hA
  have hdet : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.2
    rwa [Matrix.det_fin_two] at this
  refine ⟨?_, ?_, ?_⟩
  · rw [n4, n1]
  · rw [n3, n2]
    ring
  · intro h4
    rw [n1, n2] at h4
    apply hnot
    have hs : ((A : Matrix (Fin 2) (Fin 2) F) 0 0 - A 1 1) ^ 2 +
        ((A : Matrix (Fin 2) (Fin 2) F) 1 0 + ε * A 0 1) ^ 2 / ε = 0 := by
      field_simp at h4 ⊢
      linear_combination h4 - 4 * ε * hdet
    obtain ⟨e1, e2⟩ := FJ_of_sum_sq hε hnsq hs
    exact ⟨by linear_combination -e1, by linear_combination e2⟩

theorem exists_rot_of_La_FJ (hε : ε ≠ 0) {r : spinGroup (quadPlus 4 F)} {A : SL(2, F)}
    (hA : (frame0 (F := F)).La A = spinAction (quadPlus 4 F) r)
    (hFJ : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = A 0 0 ∧ (A : Matrix (Fin 2) (Fin 2) F) 1 0 =
      -ε * A 0 1) :
    ∃ (s t : F) (hst : s ^ 2 + t ^ 2 / ε = 1), r • z0 ε = (z0 ε).rot hε s t hst := by
  obtain ⟨hx, hy⟩ := smul_z0_of_La ε hA
  have hdet : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.2
    rwa [Matrix.det_fin_two] at this
  obtain ⟨h1, h2⟩ := hFJ
  have hst : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 + (ε * A 0 1) ^ 2 / ε = 1 := by
    field_simp
    rw [h1, h2] at hdet
    linear_combination hdet
  refine ⟨(A : Matrix (Fin 2) (Fin 2) F) 0 0, ε * A 0 1, hst, ?_⟩
  ext1
  · rw [hx, NPair.rot_x, z0_x_eq, z0_y_eq, ← map_smul, ← map_smul, ← map_add]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jm, h1, h2] <;> field_simp
  · rw [hy, NPair.rot_y, z0_x_eq, z0_y_eq, ← map_smul, ← map_smul, ← map_add]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jm, Matrix.mul_apply, Fin.sum_univ_two, h1, h2]
    ring

end RankOne

section Fwd

variable {p e : ℕ} [Fact p.Prime]

theorem colStd_of_mem_range_zero (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    {r : spinGroup (quadPlus 4 (GaloisField p e))} (hr : r ∈ (M.S.ι 0).range)
    (hrP : r ∉ parab M.S {1, 2, 3}) : ColStd M.ε r := by
  have hmem : spinAction (quadPlus 4 (GaloisField p e)) r ∈
      (stdFrames M.ε M.hε M.h4 0).La.range := by
    rw [← M.spec.map_range 0]
    exact ⟨r, hr, rfl⟩
  obtain ⟨A, hA⟩ := hmem
  have hA' : (frame0 (F := GaloisField p e)).La A = spinAction (quadPlus 4 (GaloisField p e)) r :=
    hA
  by_cases hFJ : (A : Matrix (Fin 2) (Fin 2) (GaloisField p e)) 1 1 = A 0 0 ∧
      (A : Matrix (Fin 2) (Fin 2) (GaloisField p e)) 1 0 = -M.ε * A 0 1
  · obtain ⟨s, t, hst, hrot⟩ := exists_rot_of_La_FJ M.hε hA' hFJ
    exact absurd (mem_parab_of_rot M hp2 hq hrot) hrP
  · exact colP_of_La M.hε M.nonsq hA' hFJ

end Fwd

end CFSG.ClassicalInvolution.PhanQ
