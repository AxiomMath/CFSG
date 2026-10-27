module

public import CFSG.ClassicalInvolution.Phan.PhanP3Step0

public section

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.MF15
open scoped MatrixGroups Pointwise

section JOp

variable {F : Type} [Field F]

@[expose] def Jm (ε : F) : Matrix (Fin 2) (Fin 2) F := !![0, -1; ε, 0]

theorem Jm_mul_Jm (ε : F) : Jm ε * Jm ε = (-ε) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] noncomputable def jOp (ε : F) : (Fin 4 ⊕ Fin 4 → F) →ₗ[F] (Fin 4 ⊕ Fin 4 → F) :=
  (frame0 (F := F)).incl ∘ₗ (LinearMap.mulRight F (Jm ε)) ∘ₗ (frame0 (F := F)).coords

theorem jOp_apply (ε : F) (x : Fin 4 ⊕ Fin 4 → F) :
    jOp ε x = (frame0 (F := F)).incl ((frame0 (F := F)).coords x * Jm ε) := rfl

theorem jOp_incl (ε : F) (X : Matrix (Fin 2) (Fin 2) F) :
    jOp ε ((frame0 (F := F)).incl X) = (frame0 (F := F)).incl (X * Jm ε) := by
  rw [jOp_apply, Frame.coords_incl]

theorem jOp_La (ε : F) (M : SL(2, F)) (x : Fin 4 ⊕ Fin 4 → F) :
    jOp ε ((frame0 (F := F)).La M x) = (frame0 (F := F)).La M (jOp ε x) := by
  rw [jOp_apply ε ((frame0 (F := F)).La M x), jOp_apply ε x, Frame.La_apply_incl, Frame.coords_La,
    Matrix.mul_assoc]

theorem FJ_of_incl_mem_planeA {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}
    {M : Matrix (Fin 2) (Fin 2) F} (hM : (frame0 (F := F)).incl M ∈ planeA ε hε h4) : FJ ε M := by
  rw [incl_frame0] at hM
  obtain ⟨-, h1, -⟩ := hM
  change (frame1 ε hε h4).La (-1) _ = _ at h1
  rw [La_neg_one_frame1] at h1
  have e0 := congrFun h1 (Sum.inl 0)
  have e1 := congrFun h1 (Sum.inl 1)
  simp only [vecXY_inl, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul,
    Matrix.cons_val] at e0 e1
  refine ⟨e0, ?_⟩
  have : M 1 0 = ε * (M 1 0 / ε) := by
    field_simp
  rw [this, e1]
  ring

set_option linter.unnecessarySeqFocus false in
theorem incl_mem_planeA_of_FJ (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) F} (hM : FJ ε M) : (frame0 (F := F)).incl M ∈ planeA ε hε h4 := by
  obtain ⟨h1, h2'⟩ := hM
  have hx := incl_frame0 (F := F) M
  refine ⟨?_, ?_, ?_⟩
  · show (frame0 (F := F)).La (-1) _ = _
    rw [Frame.La_neg_one_apply, Frame.coords_incl]
    module
  · show (frame1 ε hε h4).La (-1) _ = _
    rw [hx, La_neg_one_frame1]
    ext s
    rcases s with i | i <;> fin_cases i <;> simp [h1, h2'] <;> field_simp
  · show (frame2 (F := F)).La (-1) _ = _
    rw [hx, La_neg_one_frame2]
    ext s
    rcases s with i | i <;> fin_cases i <;> simp

theorem FJ.mul_Jm {ε : F} {M : Matrix (Fin 2) (Fin 2) F} (hM : FJ ε M) : FJ ε (M * Jm ε) := by
  obtain ⟨h1, h2⟩ := hM
  refine ⟨?_, ?_⟩ <;> simp [Jm, Matrix.mul_apply, Fin.sum_univ_two, h1, h2] <;> ring

theorem mem_planeA_iff {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0} (h2 : (2 : F) ≠ 0)
    {x : Fin 4 ⊕ Fin 4 → F} :
    x ∈ planeA ε hε h4 ↔
      x = (frame0 (F := F)).incl ((frame0 (F := F)).coords x) ∧
        FJ ε ((frame0 (F := F)).coords x) := by
  constructor
  · intro hx
    have hx1 : (frame0 (F := F)).La (-1) x = -x := by
      have := hx.1
      change (frame0 (F := F)).La (-1) x = (-1 : F) • x at this
      simpa using this
    have hxx := eq_incl_coords_of_La_neg_one h2 (frame0 (F := F)) hx1
    refine ⟨hxx, FJ_of_incl_mem_planeA (hε := hε) (h4 := h4) ?_⟩
    rw [← hxx]
    exact hx
  · rintro ⟨hxx, hFJ⟩
    rw [hxx]
    exact incl_mem_planeA_of_FJ ε hε h4 hFJ

theorem jOp_mem_planeA {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0} (h2 : (2 : F) ≠ 0)
    {x : Fin 4 ⊕ Fin 4 → F} (hx : x ∈ planeA ε hε h4) : jOp ε x ∈ planeA ε hε h4 := by
  obtain ⟨hxx, hFJ⟩ := (mem_planeA_iff h2).1 hx
  have : jOp ε x = (frame0 (F := F)).incl ((frame0 (F := F)).coords x * Jm ε) := jOp_apply ε x
  rw [this]
  exact incl_mem_planeA_of_FJ ε hε h4 hFJ.mul_Jm

end JOp

section StabJ

variable {F : Type} [Field F]

@[expose] noncomputable def stabJ (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) :
    Subgroup (spinGroup (quadPlus 4 F)) where
  carrier := {g | g ∈ stabOf (spinAction (quadPlus 4 F)) (planeA ε hε h4) ∧
    ∀ x ∈ planeA ε hε h4,
      spinAction (quadPlus 4 F) g (jOp ε x) = jOp ε (spinAction (quadPlus 4 F) g x)}
  mul_mem' {a b} ha hb := by
    refine ⟨mul_mem ha.1 hb.1, fun x hx => ?_⟩
    have hbx : spinAction (quadPlus 4 F) b x ∈ planeA ε hε h4 := (hb.1 x).2 hx
    rw [map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hb.2 x hx, ha.2 _ hbx]
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  inv_mem' {a} ha := by
    refine ⟨inv_mem ha.1, fun x hx => ?_⟩
    have hy : spinAction (quadPlus 4 F) a⁻¹ x ∈ planeA ε hε h4 := by
      have := (ha.1 (spinAction (quadPlus 4 F) a⁻¹ x)).1
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at this
      exact (inv_mem ha.1 x).2 hx
    have h1 := ha.2 _ hy
    rw [← LinearEquiv.mul_apply (spinAction (quadPlus 4 F) a) (spinAction (quadPlus 4 F) a⁻¹),
      ← map_mul, mul_inv_cancel, map_one] at h1
    simp only [LinearEquiv.coe_one, id_eq] at h1
    have h2 := congrArg (spinAction (quadPlus 4 F) a⁻¹) h1
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h2
    simpa using h2.symm

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {S : PhanFamilyD4 K p f (spinGroup (quadPlus 4 F))} {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

theorem spinAction_comm_jOp_of_mem_range_zero (hS : ModelSpec S ε hε h4)
    {ρ : spinGroup (quadPlus 4 F)} (hρ : ρ ∈ (S.ι 0).range) (x : Fin 4 ⊕ Fin 4 → F) :
    spinAction (quadPlus 4 F) ρ (jOp ε x) = jOp ε (spinAction (quadPlus 4 F) ρ x) := by
  have hmem : spinAction (quadPlus 4 F) ρ ∈ (stdFrames ε hε h4 0).La.range := by
    rw [← hS.map_range 0]
    exact ⟨ρ, hρ, rfl⟩
  obtain ⟨M, hM⟩ := hmem
  rw [← hM]
  exact (jOp_La ε M x).symm

theorem mem_stabJ_of_fix {g : spinGroup (quadPlus 4 F)} (h2 : (2 : F) ≠ 0)
    (hg : ∀ x ∈ planeA ε hε h4, spinAction (quadPlus 4 F) g x = x) : g ∈ stabJ ε hε h4 := by
  refine ⟨mem_stabOf_of_pointwise hg, fun x hx => ?_⟩
  rw [hg x hx, hg _ (jOp_mem_planeA h2 hx)]

theorem torusSub_le_stabJ (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0) :
    torusSub S ≤ stabJ ε hε h4 := by
  rintro _ ⟨s, rfl⟩
  rw [mTor_apply]
  have hj : ∀ (j : Fin 4) (x : normOne (unitaryInvolution K p f)), tor S j x ∈ stabJ ε hε h4 := by
    intro j x
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨torusSub_le_stabOf_eigSpace hK hg hS h2 h2K _ _ _ (tor_mem_torusSub S 0 x),
        fun y _ => spinAction_comm_jOp_of_mem_range_zero hS ⟨_, rfl⟩ y⟩
    · exact mem_stabJ_of_fix h2 (fun y hy => spinAction_fix_planeA hS h2 hj0 ⟨_, rfl⟩ y hy)
  exact mul_mem (mul_mem (mul_mem (hj 0 _) (hj 1 _)) (hj 2 _)) (hj 3 _)

theorem parab_le_stabJ (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0) :
    parab S {1, 2, 3} ≤ stabJ ε hε h4 := by
  refine sup_le (torusSub_le_stabJ hK hg hS h2 h2K) (iSup₂_le fun j hj => ?_)
  rintro _ ⟨A, rfl⟩
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp at hj
  exact mem_stabJ_of_fix h2 (fun y hy => spinAction_fix_planeA hS h2 hj0 ⟨A, rfl⟩ y hy)

end StabJ

end CFSG.ClassicalInvolution.PhanP
