module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.ComponentClassification.Sol78

open Equiv Equiv.Perm Subgroup

theorem permCongr_mem_alternatingGroup {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) {x : Perm α} (hx : x ∈ alternatingGroup α) :
    e.permCongr x ∈ alternatingGroup β := by
  rw [mem_alternatingGroup] at hx ⊢
  rw [sign_permCongr, hx]

@[expose] noncomputable def altCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) : alternatingGroup α ≃* alternatingGroup β where
  toFun x := ⟨e.permCongr x, permCongr_mem_alternatingGroup e x.2⟩
  invFun y := ⟨e.symm.permCongr y, permCongr_mem_alternatingGroup e.symm y.2⟩
  left_inv x := Subtype.ext (by ext a; simp [permCongr_apply])
  right_inv y := Subtype.ext (by ext b; simp [permCongr_apply])
  map_mul' x y := Subtype.ext (by ext a; simp [permCongr_apply, Perm.mul_apply])

@[simp]
theorem altCongr_apply_coe {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (x : alternatingGroup α) : ((altCongr e x : alternatingGroup β) : Perm β) =
      e.permCongr x := rfl

theorem exists_equiv_of_mulEquiv_alternating {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (hm : 5 ≤ Fintype.card α) (hm6 : Fintype.card α ≠ 6)
    (hαβ : Fintype.card α = Fintype.card β) (θ : alternatingGroup α ≃* alternatingGroup β) :
    ∃ τ : α ≃ β, ∀ x : alternatingGroup α, ((θ x : alternatingGroup β) : Perm β) =
      τ.permCongr x := by
  classical
  set m := Fintype.card α with hmdef
  let eα : α ≃ Fin m := Fintype.equivFinOfCardEq rfl
  let eβ : β ≃ Fin m := Fintype.equivFinOfCardEq hαβ.symm
  let κ : MulAut (alternatingGroup (Fin m)) :=
    ((altCongr eα).symm.trans θ).trans (altCongr eβ)
  obtain ⟨σ, hσ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm hm6).2 κ
  refine ⟨(eα.trans σ).trans eβ.symm, fun x => ?_⟩
  have hκ := congrArg (fun f : MulAut (alternatingGroup (Fin m)) => (f (altCongr eα x) :
    Perm (Fin m))) hσ
  simp only [MulAut.conjNormal_apply, altCongr_apply_coe] at hκ
  have h1 : (κ (altCongr eα x) : Perm (Fin m)) = eβ.permCongr (θ x) := by
    simp [κ]
  rw [h1] at hκ
  have h2 : ((θ x : alternatingGroup β) : Perm β) =
      eβ.symm.permCongr (σ * eα.permCongr (x : Perm α) * σ⁻¹) := by
    rw [hκ]
    ext b
    simp [permCongr_apply]
  rw [h2]
  ext b
  simp [permCongr_apply, Perm.mul_apply]

end CFSG.ComponentClassification.Sol78
