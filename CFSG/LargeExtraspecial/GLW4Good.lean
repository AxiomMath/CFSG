module

public import CFSG.LargeExtraspecial.GLW4Basis
public import CFSG.LargeExtraspecial.GLRFormModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Module Matrix CFSG.LargeExtraspecial.GLR

@[expose] noncomputable def toModel : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] Model 2 0 where
  toFun u := (![u 0, u 1], ![u 2, u 3], 0)
  invFun w := ![w.1 0, w.1 1, w.2.1 0, w.2.1 1]
  map_add' u v := Prod.ext (funext fun i => by fin_cases i <;> rfl)
    (Prod.ext (funext fun i => by fin_cases i <;> rfl) (funext fun i => i.elim0))
  map_smul' c u := Prod.ext (funext fun i => by fin_cases i <;> rfl)
    (Prod.ext (funext fun i => by fin_cases i <;> rfl) (funext fun i => i.elim0))
  left_inv u := funext fun i => by fin_cases i <;> rfl
  right_inv w := Prod.ext (funext fun i => by fin_cases i <;> rfl)
    (Prod.ext (funext fun i => by fin_cases i <;> rfl) (funext fun i => i.elim0))

theorem modelForm_toModel (u v : Fin 4 → ZMod 2) :
    modelForm 2 0 (toModel u) (toModel v) = u ⬝ᵥ (J *ᵥ v) := by
  simp only [modelForm_apply, toModel, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, J,
    dotProduct, mulVec, Fin.sum_univ_two, Fin.sum_univ_four]
  simp
  ring

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

theorem formOf_eq_dot (e : Basis (Fin 4) (ZMod 2) C.At) {s : S.O} (hs : gram C e s = J)
    (a a' : C.At) : C.formOf s a a' = e.equivFun a ⬝ᵥ (J *ᵥ e.equivFun a') := by
  have hM : LinearMap.BilinForm.toMatrix e (C.formOf s) = J := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    exact congrFun (congrFun hs i) j
  rw [← Matrix.toBilin_toMatrix e (C.formOf s), hM, Matrix.toBilin_apply]
  simp only [dotProduct, mulVec, Basis.equivFun_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem isGoodForm_of_gram (e : Basis (Fin 4) (ZMod 2) C.At) {s : S.O} (hs : gram C e s = J) :
    IsGoodForm (C.formOf s) := by
  have h := (isGoodForm_modelForm (m := 2) (r := 0) (by norm_num) le_rfl).comap
    (e.equivFun.trans toModel)
  convert h using 1
  refine LinearMap.ext₂ fun a a' => ?_
  rw [formOf_eq_dot e hs, LinearMap.compl₁₂_apply]
  exact (modelForm_toModel _ _).symm

end CFSG.LargeExtraspecial.GLW4
