module

public import CFSG.GH74.GLS.IVK.L2.FixedPGL
public import CFSG.GH74.GLS.IVK.L2.Lemma12fg

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

section Centralizer

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F) (σ : F ≃+* F)

theorem fieldAutHom_mul_innDiagHom (A : PGL2 F) :
    fieldAutHom e σ * innDiagHom e A = innDiagHom e (pgl2RingEquiv σ A) * fieldAutHom e σ := by
  ext x
  apply (toPSL e).injective
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [MulAut.mul_apply, MulAut.mul_apply]
  simp only [toPSL_fieldAutHom, psl2FieldAut_toPGL, toPGL_toPSL_innDiagHom]
  simp [map_mul, map_inv, pgl2FieldAut_apply]

theorem mem_centralizer_innDiagHom_iff (A : PGL2 F) :
    innDiagHom e A ∈ centralizer ({fieldAutHom e σ} : Set (MulAut K)) ↔
      pgl2RingEquiv σ A = A := by
  rw [Subgroup.mem_centralizer_singleton_iff, fieldAutHom_mul_innDiagHom e σ A]
  constructor
  · intro h
    exact (innDiagHom_injective e (mul_right_cancel h)).symm
  · intro h
    rw [h]

theorem centralizer_fieldAut_eq_map :
    centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e =
      (pgl2Incl σ).range.map (innDiagHom e) := by
  ext x
  constructor
  · rintro ⟨hx, A, rfl⟩
    exact ⟨A, (mem_range_pgl2Incl_iff σ A).mpr ((mem_centralizer_innDiagHom_iff e σ A).mp hx),
      rfl⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨(mem_centralizer_innDiagHom_iff e σ A).mpr ((mem_range_pgl2Incl_iff σ A).mp hA),
      A, rfl⟩

theorem card_centralizer_fieldAut :
    Nat.card ↥(centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e) =
      Nat.card (fixedField σ) * (Nat.card (fixedField σ) ^ 2 - 1) := by
  rw [centralizer_fieldAut_eq_map e σ, Subgroup.card_map_of_injective (innDiagHom_injective e)]
  exact card_range_pgl2Incl σ

theorem centralizer_fieldAut_le_innAut (h : Even (orderOf σ)) :
    centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e ≤ innAut K := by
  intro x hx
  rw [centralizer_fieldAut_eq_map e σ] at hx
  obtain ⟨_, ⟨A₀, rfl⟩, rfl⟩ := hx
  rw [innDiagHom_mem_innAut_iff e]
  induction A₀ using Matrix.ProjGenLinGroup.induction_on with
  | mk M =>
    rw [pgl2Incl_mk, pgl2_mk_mem_psl2_range_iff_det_isSquare, Matrix.GeneralLinearGroup.map_det,
      Units.coe_map]
    exact isSquare_of_mem_fixedField_of_even σ h
      (((M.det : (fixedField σ)ˣ) : fixedField σ)).2

@[expose] noncomputable def kToPGL : K →* PGL2 F :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp (toPSL e).toMonoidHom

omit [Finite F] in
theorem kToPGL_apply (k : K) :
    kToPGL e k = Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e k) := rfl

omit [Finite F] in
theorem kToPGL_injective : Function.Injective (kToPGL e) :=
  Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp (toPSL e).injective

omit [Finite F] in
theorem kToPGL_mem_range_pgl2Incl_iff (k : K) :
    kToPGL e k ∈ (pgl2Incl σ).range ↔ k ∈ fixedSubgroup K (fieldAutHom e σ) := by
  rw [mem_range_pgl2Incl_iff]
  show _ ↔ fieldAutHom e σ k = k
  constructor
  · intro h
    apply (toPSL e).injective
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [toPSL_fieldAutHom, psl2FieldAut_toPGL]
    exact h
  · intro h
    have h1 := psl2FieldAut_toPGL σ (toPSL e k)
    rw [← toPSL_fieldAutHom, h, pgl2FieldAut_apply] at h1
    exact h1.symm

end Centralizer

end CFSG.GH74.GLS.IVK
