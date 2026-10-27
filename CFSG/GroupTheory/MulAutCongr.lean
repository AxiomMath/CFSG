module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG

theorem mulAut_congr_conj {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) (a : A) :
    MulAut.congr ψ (MulAut.conj a) = MulAut.conj (ψ a) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := ψ.surjective x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem map_mulAut_congr {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) (θ : MulAut A)
    (S : Subgroup A) : (S.map ψ.toMonoidHom).map (MulAut.congr ψ θ).toMonoidHom =
      (S.map θ.toMonoidHom).map ψ.toMonoidHom := by
  have h : (MulAut.congr ψ θ).toMonoidHom.comp ψ.toMonoidHom =
      ψ.toMonoidHom.comp θ.toMonoidHom := by
    ext a
    simp [MulAut.congr_apply]
  rw [Subgroup.map_map, Subgroup.map_map, h]

end CFSG
