module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Glue

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section Glue

variable {U Uc : Submodule (ZMod 2) V} (hc : IsCompl U Uc)
  (φ : (Fin 2 → F4) ≃ₗ[ZMod 2] U)

@[expose] noncomputable def TA (A : GL (Fin 2) F4) : U ≃ₗ[ZMod 2] U :=
  φ.symm.trans ((actZ A).trans φ)

@[expose] noncomputable def glueA (A : GL (Fin 2) F4) : V ≃ₗ[ZMod 2] V :=
  ((Submodule.prodEquivOfIsCompl U Uc hc).symm.trans
    ((TA φ A).prodCongr (LinearEquiv.refl (ZMod 2) Uc))).trans
    (Submodule.prodEquivOfIsCompl U Uc hc)

theorem TA_mul (A B : GL (Fin 2) F4) (u : U) : TA φ (A * B) u = TA φ A (TA φ B u) := by
  simp only [TA, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_mul,
    LinearEquiv.mul_apply]

theorem TA_one (u : U) : TA φ 1 u = u := by
  have h1 : actZ (1 : GL (Fin 2) F4) = 1 := map_one actZ
  show φ (actZ 1 (φ.symm u)) = u
  rw [h1]
  exact φ.apply_symm_apply u

theorem glueA_apply_left (A : GL (Fin 2) F4) (u : U) :
    glueA hc φ A (u : V) = ((TA φ A u : U) : V) := by
  simp only [glueA, LinearEquiv.trans_apply, Submodule.prodEquivOfIsCompl_symm_apply_left,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl',
    ZeroMemClass.coe_zero, add_zero]

theorem glueA_apply_right (A : GL (Fin 2) F4) (u : Uc) :
    glueA hc φ A (u : V) = (u : V) := by
  simp only [glueA, LinearEquiv.trans_apply, Submodule.prodEquivOfIsCompl_symm_apply_right,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, map_zero, Submodule.coe_prodEquivOfIsCompl',
    ZeroMemClass.coe_zero, zero_add]

theorem exists_decomp_glue (hc : IsCompl U Uc) (x : V) :
    ∃ (u : U) (u' : Uc), x = (u : V) + (u' : V) := by
  have hx : x ∈ U ⊔ Uc := by rw [hc.sup_eq_top]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hx
  exact ⟨⟨y, hy⟩, ⟨z, hz⟩, hyz.symm⟩

theorem glueA_mul (A B : GL (Fin 2) F4) :
    glueA hc φ (A * B) = glueA hc φ A * glueA hc φ B := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨u, u', rfl⟩ := exists_decomp_glue hc x
  simp only [LinearEquiv.mul_apply, map_add, glueA_apply_left, glueA_apply_right, TA_mul]

@[expose] noncomputable def glueHom : GL (Fin 2) F4 →* (V ≃ₗ[ZMod 2] V) :=
  MonoidHom.mk' (glueA hc φ) (fun A B => glueA_mul hc φ A B)

theorem actZ_of_glue (A : GL (Fin 2) F4) (hA : glueA hc φ A = 1) : actZ A = 1 := by
  apply LinearEquiv.ext
  intro c
  have h1 : glueA hc φ A ((φ c : U) : V) = ((φ c : U) : V) := by
    rw [hA]
    rfl
  rw [glueA_apply_left] at h1
  have h2 : TA φ A (φ c) = φ c := Subtype.ext h1
  have h3 : φ (actZ A (φ.symm (φ c))) = φ c := h2
  rw [LinearEquiv.symm_apply_apply] at h3
  exact φ.injective h3

theorem glueHom_injective : Function.Injective (glueHom hc φ) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  apply actZ_injective
  rw [map_one]
  exact actZ_of_glue hc φ A hA

@[expose] noncomputable def glueSL : Matrix.SpecialLinearGroup (Fin 2) F4 →* (V ≃ₗ[ZMod 2] V) :=
  (glueHom hc φ).comp Matrix.SpecialLinearGroup.toGL

theorem glueSL_injective : Function.Injective (glueSL hc φ) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hG : Matrix.SpecialLinearGroup.toGL A = 1 := by
    apply glueHom_injective hc φ
    rw [map_one]
    exact hA
  apply Subtype.ext
  have := congrArg Units.val hG
  simpa using this

end Glue

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Glue

end
