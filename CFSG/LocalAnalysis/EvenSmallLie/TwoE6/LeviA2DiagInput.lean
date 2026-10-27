module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.LeviA2Diag
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUniqueInput

public noncomputable section

namespace CFSG.EvenSmallLie.TwoE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Steinberg.Exceptional

local notation "𝔽" => GaloisField 2 (2 * 1)

@[expose] def diagOmegaGLF : GL (Fin 3) 𝔽 :=
  Units.map (RingHom.mapMatrix fieldEquiv.symm.toRingHom).toMonoidHom diagOmegaGL

theorem coe_diagOmegaGLF : (diagOmegaGLF : Matrix (Fin 3) (Fin 3) 𝔽) =
    fieldEquiv.symm.toRingHom.mapMatrix (diagOmegaGL : Matrix (Fin 3) (Fin 3) K) :=
  rfl

theorem coe_diagOmegaGLF_inv : ((diagOmegaGLF⁻¹ : GL (Fin 3) 𝔽) : Matrix (Fin 3) (Fin 3) 𝔽) =
    fieldEquiv.symm.toRingHom.mapMatrix ((diagOmegaGL⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) :=
  rfl

theorem det_diagOmegaGLF_ne_one : (diagOmegaGLF : Matrix (Fin 3) (Fin 3) 𝔽).det ≠ 1 := by
  rw [coe_diagOmegaGLF, ← RingHom.map_det, Ne, ← map_one fieldEquiv.symm.toRingHom,
    fieldEquiv.symm.toRingHom.injective.eq_iff]
  exact det_diagOmegaGL_ne_one

theorem leviA2DiagInput
    : LeviA2DiagInput := by
  refine ⟨levi34Hom, diagOmegaGLF, levi34Unit, levi34Hom_injective, range_levi34Hom,
    det_diagOmegaGLF_ne_one, fun A B hAB => ?_⟩
  set A' := Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom A with hA'
  have hA : slFieldEquivSymm A' = A :=
    Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp [hA']
  have hB : slFieldEquivSymm (conjSL3 diagOmegaGL A') = B := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_conjSL3, map_mul, map_mul,
      ← coe_diagOmegaGLF, ← coe_diagOmegaGLF_inv, ← Matrix.SpecialLinearGroup.map_apply_coe,
      hA, hAB]
  have e := DFunLike.congr_fun levi34Diag_comp_isogenyStd A'
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, levi34HomK] at e
  rw [hA, hB] at e
  exact e

end CFSG.EvenSmallLie.TwoE6
