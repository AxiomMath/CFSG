module

public import Mathlib.LinearAlgebra.Projection

public section

namespace CFSG.ClassicalGroups

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Ext

variable {P W : Submodule K V} (hPW : IsCompl P W)

include hPW in
@[expose] noncomputable def extLin (g : W →ₗ[K] W) : V →ₗ[K] V :=
  P.subtype ∘ₗ P.projectionOnto W hPW + W.subtype ∘ₗ g ∘ₗ W.projectionOnto P hPW.symm

theorem extLin_apply (g : W →ₗ[K] W) (v : V) :
    extLin hPW g v = (P.projectionOnto W hPW v : V) +
      (g (W.projectionOnto P hPW.symm v) : V) := rfl

include hPW in
theorem exists_add_eq (v : V) : ∃ p ∈ P, ∃ w ∈ W, p + w = v := by
  have : v ∈ P ⊔ W := by rw [hPW.sup_eq_top]; trivial
  exact Submodule.mem_sup.mp this

include hPW in
theorem extLin_add (g : W →ₗ[K] W) {p w : V} (hp : p ∈ P) (hw : w ∈ W) :
    extLin hPW g (p + w) = p + (g ⟨w, hw⟩ : V) := by
  have e : p + w = ((⟨p, hp⟩ : P) : V) + ((⟨w, hw⟩ : W) : V) := rfl
  rw [e, extLin_apply, map_add, map_add, Submodule.projectionOnto_apply_left,
    Submodule.projectionOnto_apply_right, Submodule.projectionOnto_apply_right,
    Submodule.projectionOnto_apply_left]
  simp

include hPW in
theorem extLin_one : extLin hPW (1 : W →ₗ[K] W) = 1 := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨p, hp, w, hw, rfl⟩ := exists_add_eq hPW v
  rw [extLin_add hPW _ hp hw]
  rfl

include hPW in
theorem extLin_mul (g h : W →ₗ[K] W) : extLin hPW (g * h) = extLin hPW g * extLin hPW h := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨p, hp, w, hw, rfl⟩ := exists_add_eq hPW v
  rw [Module.End.mul_apply, extLin_add hPW _ hp hw, extLin_add hPW _ hp hw]
  have hh : ((h ⟨w, hw⟩ : W) : V) ∈ W := (h ⟨w, hw⟩).2
  rw [extLin_add hPW g hp hh]
  rfl

@[expose] noncomputable def extHom : (W →ₗ[K] W) →* (V →ₗ[K] V) where
  toFun := extLin hPW
  map_one' := extLin_one hPW
  map_mul' := extLin_mul hPW

end Ext

end CFSG.ClassicalGroups
