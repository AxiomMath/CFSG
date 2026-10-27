module

public import CFSG.ClassicalInvolution.Phan.PhanP5Plane

public section

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.MF15
open scoped MatrixGroups Pointwise

section PlaneB

variable {F : Type} [Field F]

@[expose] def FJ' (ε : F) (X : Matrix (Fin 2) (Fin 2) F) : Prop :=
  X 1 1 = -X 0 0 ∧ X 1 0 = ε * X 0 1

@[expose] def planeB (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) : Submodule F (Fin 4 ⊕ Fin 4 → F) :=
  eigSpace ε hε h4 (-1) (-1) 1

theorem FJ'_of_incl_mem_planeB {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}
    {X : Matrix (Fin 2) (Fin 2) F} (hX : (frame0 (F := F)).incl X ∈ planeB ε hε h4) : FJ' ε X := by
  rw [incl_frame0] at hX
  obtain ⟨-, h1, -⟩ := hX
  change (frame1 ε hε h4).La (-1) _ = (-1 : F) • _ at h1
  rw [La_neg_one_frame1] at h1
  have e0 := congrFun h1 (Sum.inl 0)
  have e1 := congrFun h1 (Sum.inl 1)
  simp only [vecXY_inl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Pi.smul_apply, smul_eq_mul] at e0 e1
  refine ⟨?_, ?_⟩
  · linear_combination e0
  · have : X 1 0 = ε * (X 1 0 / ε) := by
      field_simp
    rw [this, e1]
    ring

set_option linter.unnecessarySeqFocus false in
theorem incl_mem_planeB_of_FJ' (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0)
    {X : Matrix (Fin 2) (Fin 2) F} (hX : FJ' ε X) : (frame0 (F := F)).incl X ∈ planeB ε hε h4 := by
  obtain ⟨h1, h2'⟩ := hX
  have hx := incl_frame0 (F := F) X
  refine ⟨?_, ?_, ?_⟩
  · show (frame0 (F := F)).La (-1) _ = (-1 : F) • _
    rw [Frame.La_neg_one_apply, Frame.coords_incl]
    module
  · show (frame1 ε hε h4).La (-1) _ = (-1 : F) • _
    rw [hx, La_neg_one_frame1]
    ext s
    rcases s with i | i <;> fin_cases i <;> simp [h1, h2'] <;> field_simp
  · show (frame2 (F := F)).La (-1) _ = (1 : F) • _
    rw [hx, La_neg_one_frame2]
    ext s
    rcases s with i | i <;> fin_cases i <;> simp

theorem mem_planeB_iff {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0} (h2 : (2 : F) ≠ 0)
    {x : Fin 4 ⊕ Fin 4 → F} :
    x ∈ planeB ε hε h4 ↔
      x = (frame0 (F := F)).incl ((frame0 (F := F)).coords x) ∧
        FJ' ε ((frame0 (F := F)).coords x) := by
  constructor
  · intro hx
    have hx1 : (frame0 (F := F)).La (-1) x = -x := by
      have := hx.1
      change (frame0 (F := F)).La (-1) x = (-1 : F) • x at this
      simpa using this
    have hxx := eq_incl_coords_of_La_neg_one h2 (frame0 (F := F)) hx1
    refine ⟨hxx, FJ'_of_incl_mem_planeB (hε := hε) (h4 := h4) ?_⟩
    rw [← hxx]
    exact hx
  · rintro ⟨hxx, hFJ⟩
    rw [hxx]
    exact incl_mem_planeB_of_FJ' ε hε h4 hFJ

theorem exists_decomp_span {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0} (h2 : (2 : F) ≠ 0)
    (x : Fin 4 ⊕ Fin 4 → F) (hx : x = (frame0 (F := F)).incl ((frame0 (F := F)).coords x)) :
    ∃ a ∈ planeA ε hε h4, ∃ b ∈ planeB ε hε h4, x = a + b := by
  set X := (frame0 (F := F)).coords x with hX
  let YA : Matrix (Fin 2) (Fin 2) F :=
    !![(X 0 0 + X 1 1) / 2, -((X 1 0 / ε - X 0 1) / 2); ε * ((X 1 0 / ε - X 0 1) / 2),
      (X 0 0 + X 1 1) / 2]
  let YB : Matrix (Fin 2) (Fin 2) F :=
    !![(X 0 0 - X 1 1) / 2, (X 1 0 / ε + X 0 1) / 2; ε * ((X 1 0 / ε + X 0 1) / 2),
      -((X 0 0 - X 1 1) / 2)]
  have hA : FJ ε YA := ⟨by simp [YA], by simp [YA]⟩
  have hB : FJ' ε YB := ⟨by simp [YB], by simp [YB]⟩
  refine ⟨(frame0 (F := F)).incl YA, incl_mem_planeA_of_FJ ε hε h4 hA,
    (frame0 (F := F)).incl YB, incl_mem_planeB_of_FJ' ε hε h4 hB, ?_⟩
  rw [← map_add]
  conv_lhs => rw [hx]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [YA, YB] <;> field_simp <;> ring

@[expose] noncomputable def vecA1 (F : Type) [Field F] : Fin 4 ⊕ Fin 4 → F :=
  (frame0 (F := F)).incl 1

@[expose] noncomputable def vecB1 (F : Type) [Field F] : Fin 4 ⊕ Fin 4 → F :=
  (frame0 (F := F)).incl !![1, 0; 0, -1]

theorem vecA1_mem_planeA (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) :
    vecA1 F ∈ planeA ε hε h4 :=
  incl_mem_planeA_of_FJ ε hε h4 ⟨by simp, by simp⟩

theorem vecB1_mem_planeB (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) :
    vecB1 F ∈ planeB ε hε h4 :=
  incl_mem_planeB_of_FJ' ε hε h4 ⟨by simp, by simp⟩

theorem Q_vecA1 : quadPlus 4 F (vecA1 F) = 1 := by
  rw [vecA1, Frame.Q_incl]
  simp

theorem Q_vecB1 : quadPlus 4 F (vecB1 F) = -1 := by
  rw [vecB1, Frame.Q_incl]
  simp [Matrix.det_fin_two_of]

theorem La_eq_one_of_fix {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    (fr : Frame Q) {M : SL(2, F)} {b : V} (hb : b = fr.incl (fr.coords b)) (hQ : Q b ≠ 0)
    (hfix : fr.La M b = b) : M = 1 := by
  set Y := fr.coords b with hY
  have hdet : Y.det ≠ 0 := by
    rw [← fr.Q_incl, ← hb]
    exact hQ
  have hU : IsUnit Y := (Matrix.isUnit_iff_isUnit_det Y).2 (isUnit_iff_ne_zero.2 hdet)
  rw [hb, Frame.La_apply_incl] at hfix
  have h1 := congrArg fr.coords hfix
  rw [Frame.coords_incl, Frame.coords_incl] at h1
  have h2 : (M : Matrix (Fin 2) (Fin 2) F) * Y = 1 * Y := by rw [one_mul]; exact h1
  have h3 := hU.mul_left_inj.1 h2
  exact Subtype.ext (by simpa using h3)

end PlaneB

end CFSG.ClassicalInvolution.PhanP
