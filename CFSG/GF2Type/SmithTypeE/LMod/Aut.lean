module

public import CFSG.GF2Type.SmithTypeE.LMod.T6
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6 Matrix
open scoped MatrixGroups

attribute [local irreducible] tvIdxTab tvTab tvImg tvList

section Swap

@[expose] def swapSet (p : TvSet) : TvSet :=
  ⟨(p.1.2, p.1.1), p.2.2.1, p.2.1, by rw [dotProduct_comm]; exact p.2.2.2⟩

@[expose] noncomputable def swapIdx (k : Fin 1953) : Fin 1953 :=
  tvEquivTv.symm (swapSet (tvEquivTv k))

theorem tvEquivTv_swapIdx (k : Fin 1953) : tvEquivTv (swapIdx k) = swapSet (tvEquivTv k) :=
  tvEquivTv.apply_symm_apply _

theorem tvVec_swapIdx (k : Fin 1953) : tvVec (swapIdx k) = tvForm k :=
  congrArg (fun p => p.1.1) (tvEquivTv_swapIdx k)

theorem tvForm_swapIdx (k : Fin 1953) : tvForm (swapIdx k) = tvVec k :=
  congrArg (fun p => p.1.2) (tvEquivTv_swapIdx k)

theorem swapIdx_swapIdx (k : Fin 1953) : swapIdx (swapIdx k) = k := by
  apply tvToSet_injective
  apply Subtype.ext
  apply Prod.ext
  · show tvVec (swapIdx (swapIdx k)) = tvVec k
    rw [tvVec_swapIdx, tvForm_swapIdx]
  · show tvForm (swapIdx (swapIdx k)) = tvForm k
    rw [tvForm_swapIdx, tvVec_swapIdx]

theorem tvMatrix_swapIdx (k : Fin 1953) : tvMatrix (swapIdx k) = (tvMatrix k)ᵀ := by
  unfold tvMatrix
  rw [tvVec_swapIdx, tvForm_swapIdx, transpose_add, transpose_one, transpose_vecMulVec]

end Swap

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification

theorem proj_injective_six : Function.Injective (LinearFlag.proj 6 (ZMod 2)) := by
  rw [← MonoidHom.ker_eq_bot_iff, LinearFlag.ker_proj, LinearFlag.scalars_eq_center]
  exact CFSG.LargeExtraspecial.DW.center_specialLinearGroup_zmod_two_eq_bot 6

@[expose] noncomputable def projEquiv : SL(6, ZMod 2) ≃* LinearFlag.projectiveSL 6 (ZMod 2) :=
  MulEquiv.ofBijective (LinearFlag.proj 6 (ZMod 2))
    ⟨proj_injective_six, LinearFlag.proj_surjective 6 (ZMod 2)⟩

theorem projEquiv_apply (A : SL(6, ZMod 2)) : projEquiv A = LinearFlag.proj 6 (ZMod 2) A := rfl

section Aut

@[expose] noncomputable def thetaP : LinearFlag.projectiveSL 6 (ZMod 2) ≃* T6 :=
  projEquiv.symm.trans slT6

theorem thetaP_proj (A : SL(6, ZMod 2)) : thetaP (LinearFlag.proj 6 (ZMod 2) A) = slT6 A := by
  rw [thetaP, MulEquiv.trans_apply, ← projEquiv_apply, MulEquiv.symm_apply_apply]

theorem slT6_tvSL (k : Fin 1953) : slT6 (tvSL k) = ⟨tvP k, tvP_mem k⟩ := rfl

@[expose] def glToSL (A : GL (Fin 6) (ZMod 2)) : SL(6, ZMod 2) :=
  ⟨A.val, by
    have h : (Matrix.GeneralLinearGroup.det A : (ZMod 2)ˣ) = 1 := by
      have : Subsingleton (ZMod 2)ˣ := ⟨by decide⟩
      exact Subsingleton.elim _ _
    have := congrArg Units.val h
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this⟩

theorem coe_glToSL (A : GL (Fin 6) (ZMod 2)) :
    (glToSL A : Matrix (Fin 6) (Fin 6) (ZMod 2)) = A.val := rfl

theorem coe_glToSL_inv (A : GL (Fin 6) (ZMod 2)) :
    ((glToSL A)⁻¹ : SL(6, ZMod 2)) = (A⁻¹).val := by
  have h1 := coe_inv_mul (glToSL A)
  rw [coe_glToSL] at h1
  calc ((glToSL A)⁻¹ : SL(6, ZMod 2)).val = ((A⁻¹).val * A.val) * ((glToSL A)⁻¹ : SL(6, ZMod 2)).val := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    _ = (A⁻¹).val * (A.val * ((glToSL A)⁻¹ : SL(6, ZMod 2)).val) := by rw [Matrix.mul_assoc]
    _ = (A⁻¹).val := by
        rw [show A.val * ((glToSL A)⁻¹ : SL(6, ZMod 2)).val = 1 from coe_mul_inv (glToSL A),
          Matrix.mul_one]

end Aut

section Eval

theorem tvMatrix_actPerm (A : SL(6, ZMod 2)) (k : Fin 1953) :
    tvMatrix (actPerm A k) = (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) * tvMatrix k *
      ((A⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  have h := congrArg (fun B : SL(6, ZMod 2) => (B : Matrix (Fin 6) (Fin 6) (ZMod 2)))
    (tvSL_actPerm A k)
  simpa [coe_tvSL, SpecialLinearGroup.coe_mul] using h

theorem slConjugation_tvSL (A : GL (Fin 6) (ZMod 2)) (k : Fin 1953) :
    CatalogueBHigherLinearAction.slConjugation 6 (ZMod 2) A (tvSL k) =
      tvSL (actPerm (glToSL A) k) := by
  apply Subtype.ext
  rw [CatalogueBHigherLinearAction.slConjugation_matrix]
  show _ = tvMatrix (actPerm (glToSL A) k)
  rw [tvMatrix_actPerm, coe_glToSL, coe_glToSL_inv]
  rfl

theorem slGraphAut_tvSL (k : Fin 1953) :
    CatalogueBGraphForm.slGraphAut 6 (ZMod 2) (tvSL k) = tvSL (swapIdx k) := by
  apply Subtype.ext
  rw [CatalogueBGraphForm.slGraphAut_matrix, tvSL_inv, coe_tvSL, coe_tvSL, tvMatrix_swapIdx]

theorem exists_aut_form (α : MulAut T6) :
    ∃ A : SL(6, ZMod 2),
      (∀ k, α ⟨tvP k, tvP_mem k⟩ = ⟨tvP (actPerm A k), tvP_mem _⟩) ∨
      (∀ k, α ⟨tvP k, tvP_mem k⟩ = ⟨tvP (actPerm A (swapIdx k)), tvP_mem _⟩) := by
  obtain ⟨-, hgen⟩ := LinearFlag.automorphism_generation (K := ZMod 2) (n := 6) (by norm_num)
  obtain ⟨A, σ, ε, hε, hβ⟩ := hgen ((thetaP.trans α).trans thetaP.symm)
  have hσ : σ = 1 := Subsingleton.elim _ _
  have key : ∀ k : Fin 1953, α ⟨tvP k, tvP_mem k⟩ =
      thetaP (((thetaP.trans α).trans thetaP.symm) (LinearFlag.proj 6 (ZMod 2) (tvSL k))) := by
    intro k
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, thetaP_proj,
      slT6_tvSL]
  refine ⟨glToSL A, ?_⟩
  interval_cases ε
  · left
    intro k
    rw [key, hβ, hσ, map_one, pow_zero, mul_one, mul_one, LinearFlag.conjAut_proj,
      slConjugation_tvSL, thetaP_proj, slT6_tvSL]
  · right
    intro k
    rw [key, hβ, hσ, map_one, pow_one, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply,
      LinearFlag.dualAut_proj]
    show thetaP (LinearFlag.conjAut 6 (ZMod 2) A (LinearFlag.proj 6 (ZMod 2)
      (CatalogueBGraphForm.slGraphAut 6 (ZMod 2) (tvSL k)))) = _
    rw [slGraphAut_tvSL, LinearFlag.conjAut_proj, slConjugation_tvSL, thetaP_proj, slT6_tvSL]

theorem exists_tv_image (α : MulAut T6) (k : Fin 1953) :
    ∃ j : Fin 1953, α ⟨tvP k, tvP_mem k⟩ = ⟨tvP j, tvP_mem j⟩ := by
  obtain ⟨A, h | h⟩ := exists_aut_form α
  · exact ⟨_, h k⟩
  · exact ⟨_, h k⟩

end Eval

section AutPerm

theorem tvP_conj_tvP (k a : Fin 1953) : tvP k * tvP a * tvP k = tvP (tvP k a) := by
  have := mul_tvP_mul_inv (tvP_mem k) a
  rwa [tvP_inv] at this

@[expose] noncomputable def autFun (α : MulAut T6) (k : Fin 1953) : Fin 1953 :=
  Classical.choose (exists_tv_image α k)

theorem autFun_spec (α : MulAut T6) (k : Fin 1953) :
    α ⟨tvP k, tvP_mem k⟩ = ⟨tvP (autFun α k), tvP_mem _⟩ :=
  Classical.choose_spec (exists_tv_image α k)

theorem autFun_eq {α : MulAut T6} {k j : Fin 1953}
    (h : α ⟨tvP k, tvP_mem k⟩ = ⟨tvP j, tvP_mem j⟩) : autFun α k = j :=
  tvP_injective (congrArg Subtype.val ((autFun_spec α k).symm.trans h))

theorem autFun_mul (α β : MulAut T6) (k : Fin 1953) :
    autFun (α * β) k = autFun α (autFun β k) :=
  autFun_eq (by rw [MulAut.mul_apply, autFun_spec β, autFun_spec α])

theorem autFun_one (k : Fin 1953) : autFun 1 k = k :=
  autFun_eq (by rw [MulAut.one_apply])

@[expose] noncomputable def autPerm : MulAut T6 →* Equiv.Perm (Fin 1953) where
  toFun α :=
    { toFun := autFun α
      invFun := autFun α⁻¹
      left_inv := fun k => by rw [← autFun_mul, inv_mul_cancel, autFun_one]
      right_inv := fun k => by rw [← autFun_mul, mul_inv_cancel, autFun_one] }
  map_one' := Equiv.ext autFun_one
  map_mul' α β := Equiv.ext (autFun_mul α β)

theorem autPerm_tvP (α : MulAut T6) (k : Fin 1953) :
    α ⟨tvP k, tvP_mem k⟩ = ⟨tvP (autPerm α k), tvP_mem _⟩ :=
  autFun_spec α k

theorem autPerm_eq_iff (α : MulAut T6) (k j : Fin 1953) :
    autPerm α k = j ↔ α ⟨tvP k, tvP_mem k⟩ = ⟨tvP j, tvP_mem j⟩ :=
  ⟨fun h => h ▸ autPerm_tvP α k, autFun_eq⟩

theorem isTvAut_autPerm (α : MulAut T6) : IsTvAut (autPerm α) := by
  refine isTvAut_of_apply fun k a => ?_
  have hx : (⟨tvP k, tvP_mem k⟩ : T6) * ⟨tvP a, tvP_mem a⟩ * ⟨tvP k, tvP_mem k⟩ =
      ⟨tvP (tvP k a), tvP_mem _⟩ := Subtype.ext (tvP_conj_tvP k a)
  have h := congrArg α hx
  rw [map_mul, map_mul, autPerm_tvP, autPerm_tvP, autPerm_tvP] at h
  have h2 := congrArg Subtype.val h
  simp only [Subgroup.coe_mul] at h2
  rw [tvP_conj_tvP] at h2
  exact (tvP_injective h2).symm

theorem autPerm_mem_normalizer (α : MulAut T6) :
    autPerm α ∈ Subgroup.normalizer (T6 : Set (Equiv.Perm (Fin 1953))) :=
  (isTvAut_autPerm α).mem_normalizer

theorem autPerm_injective : Function.Injective (autPerm : MulAut T6 →* Equiv.Perm (Fin 1953)) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  have key : ∀ x (hx : x ∈ T6), ((α ⟨x, hx⟩ : T6) : Equiv.Perm (Fin 1953)) = x := by
    intro x hx
    change x ∈ Subgroup.closure (Set.range tvP) at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      rw [autPerm_tvP, hα]
      rfl
    | one =>
      have : (⟨1, Subgroup.one_mem _⟩ : T6) = 1 := rfl
      rw [this, map_one]
      rfl
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, Subgroup.mul_mem _ hx hy⟩ : T6) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, Subgroup.coe_mul, ihx, ihy]
    | inv x hx ih =>
      have : (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : T6) = ⟨x, hx⟩⁻¹ := rfl
      rw [this, map_inv, Subgroup.coe_inv, ih]
  refine MulEquiv.ext fun x => Subtype.ext ?_
  exact key x.1 x.2

@[expose] noncomputable def swapPerm : Equiv.Perm (Fin 1953) :=
  ⟨swapIdx, swapIdx, swapIdx_swapIdx, swapIdx_swapIdx⟩

theorem swapPerm_apply (k : Fin 1953) : swapPerm k = swapIdx k := rfl

theorem autPerm_form (α : MulAut T6) :
    ∃ A : SL(6, ZMod 2), autPerm α = actPerm A ∨ autPerm α = actPerm A * swapPerm := by
  obtain ⟨A, h | h⟩ := exists_aut_form α
  · exact ⟨A, Or.inl (Equiv.ext fun k => (autPerm_eq_iff α k _).2 (h k))⟩
  · exact ⟨A, Or.inr (Equiv.ext fun k => (autPerm_eq_iff α k _).2 (h k))⟩

theorem autPerm_conj (t : T6) : autPerm (MulAut.conj t) = (t : Equiv.Perm (Fin 1953)) := by
  refine Equiv.ext fun k => ?_
  rw [autPerm_eq_iff]
  apply Subtype.ext
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  exact mul_tvP_mul_inv t.2 k

end AutPerm

end CFSG.GF2Type.SmithTypeE.LMod
