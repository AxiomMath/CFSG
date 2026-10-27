module

public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Pairs

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open F3

variable {m : ℕ} {f f' : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

namespace Beta

@[expose] noncomputable def glOf (e : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)) :
    GL (Fin m) (ZMod 3) :=
  ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]⟩

@[simp]
theorem act_glOf (e : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)) (x : Fin m → ZMod 3) :
    act (glOf e) x = e x :=
  LinearMap.toMatrix'_mulVec _ x

@[simp]
theorem act_glOf_inv (e : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)) (x : Fin m → ZMod 3) :
    act (glOf e)⁻¹ x = e.symm x := by
  conv_lhs => rw [← e.apply_symm_apply x, ← act_glOf]
  exact act_inv_act _ _

variable {e : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)}

theorem glOf_conj_refl (he : ∀ x y, f x y = f' (e x) (e y)) (v : Fin m → ZMod 3) :
    glOf e * refl f v * (glOf e)⁻¹ = refl f' (e v) := by
  by_cases hv : f v v = 1
  · have hv' : f' (e v) (e v) = 1 := by rw [← he, hv]
    refine gl_ext fun x => ?_
    rw [act_mul, act_mul, act_glOf_inv, act_refl hv, act_glOf, act_refl hv', map_add,
      map_smul, e.apply_symm_apply, he, e.apply_symm_apply]
  · have hv' : f' (e v) (e v) ≠ 1 := by rwa [← he]
    rw [refl_of_ne hv, refl_of_ne hv', mul_one, mul_inv_cancel]

theorem map_reflGroup (he : ∀ x y, f x y = f' (e x) (e y)) :
    (reflGroup f).map (MulAut.conj (glOf e)).toMonoidHom = reflGroup f' := by
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, hg, rfl⟩
    obtain ⟨v, hv, rfl⟩ := mem_reflSet_iff.1 hg
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, glOf_conj_refl he]
    exact refl_mem_reflSet (by rw [← he, hv])
  · intro hg
    obtain ⟨w, hw, rfl⟩ := mem_reflSet_iff.1 hg
    refine ⟨refl f (e.symm w), refl_mem_reflSet (by rw [he, e.apply_symm_apply, hw]), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, glOf_conj_refl he, e.apply_symm_apply]

@[expose] noncomputable def reflGroupEquiv (he : ∀ x y, f x y = f' (e x) (e y)) :
    reflGroup f ≃* reflGroup f' :=
  ((MulAut.conj (glOf e)).subgroupMap (reflGroup f)).trans
    (MulEquiv.subgroupCongr (map_reflGroup he))

theorem coe_reflGroupEquiv (he : ∀ x y, f x y = f' (e x) (e y)) (g : reflGroup f) :
    (reflGroupEquiv he g : GL (Fin m) (ZMod 3)) = glOf e * g * (glOf e)⁻¹ :=
  rfl

end Beta

open Beta

variable {e : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)}

@[expose] noncomputable def R3Congr (e : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3))
    (he : ∀ x y, f x y = f' (e x) (e y)) : R3 f ≃* R3 f' :=
  quotientCenterCongr (reflGroupEquiv he)

theorem R3Congr_reflBar (he : ∀ x y, f x y = f' (e x) (e y)) (v : Fin m → ZMod 3) :
    R3Congr e he (reflBar f v) = reflBar f' (e v) := by
  rw [R3Congr, reflBar, quotientCenterCongr_mk, reflBar]
  exact congrArg _ (Subtype.ext (glOf_conj_refl he v))

theorem image_D3_R3Congr (he : ∀ x y, f x y = f' (e x) (e y)) :
    R3Congr e he '' D3 f = D3 f' := by
  ext q
  constructor
  · rintro ⟨_, hq, rfl⟩
    obtain ⟨v, hv, rfl⟩ := mem_D3_iff.1 hq
    rw [R3Congr_reflBar]
    exact reflBar_mem_D3 (by rw [← he, hv])
  · intro hq
    obtain ⟨w, hw, rfl⟩ := mem_D3_iff.1 hq
    refine ⟨reflBar f (e.symm w), reflBar_mem_D3 (by rw [he, e.apply_symm_apply, hw]), ?_⟩
    rw [R3Congr_reflBar, e.apply_symm_apply]

theorem exists_mulEquiv_R3_of_isometry (e : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3))
    (he : ∀ x y, f x y = f' (e x) (e y)) : ∃ ψ : R3 f ≃* R3 f', ψ '' D3 f = D3 f' :=
  ⟨R3Congr e he, image_D3_R3Congr he⟩

end CFSG.Fischer.Classification
