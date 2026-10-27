module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Fam
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3OrthF

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open scoped MatrixGroups

section Ad

theorem exists_adFam_base {kF K : Type} [Field kF] [Finite kF] [Field K] (τ : kF →+* K)
    (hodd : Odd (Nat.card kF)) (h2K : (2 : K) ≠ 0) (e : Fin 3 → kF) (he : ∀ i, e i ≠ 0) :
    ∃ Y3 : SL(2, kF) →* Matrix (Fin 3) (Fin 3) K, AdFam (fun i => τ (e i)) Y3 ∧
      (∀ S, (Y3 S).det = 1) ∧ ∀ S, ∃ M : Matrix (Fin 3) (Fin 3) kF, Y3 S = M.map τ := by
  have hR : ((cls3Diag e he : GL (Fin 3) kF) : Matrix (Fin 3) (Fin 3) kF)ᵀ =
      (cls3Diag e he : GL (Fin 3) kF) := by
    simp [cls3Diag, Matrix.diagonal_transpose]
  obtain ⟨ι, P, P', hPP', hP'P, hiso, hι, -⟩ := ad_param hodd (cls3Diag e he) hR
  let Y3 : SL(2, kF) →* Matrix (Fin 3) (Fin 3) K :=
    { toFun := fun S => (ι S : Matrix (Fin 3) (Fin 3) kF).map τ
      map_one' := by
        rw [map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero τ) (map_one τ)]
      map_mul' := fun S T => by
        rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul] }
  have hY3 : ∀ S, Y3 S = (ι S : Matrix (Fin 3) (Fin 3) kF).map τ := fun S => rfl
  refine ⟨Y3, ⟨fun S => ?_, fun W hW => ?_, fun T hT => ?_⟩, fun S => ?_, fun S => ⟨_, rfl⟩⟩
  · rw [hY3]
    have h1 := (CatalogueBGraphForm.mem_isometryGroup 3 kF (cls3Diag e he) _).1 (hiso S)
    have h2 : (ι S : Matrix (Fin 3) (Fin 3) kF)ᵀ * Matrix.diagonal e *
        (ι S : Matrix (Fin 3) (Fin 3) kF) = Matrix.diagonal e := by
      simpa [cls3Diag] using h1
    have h3 := congrArg (fun X : Matrix (Fin 3) (Fin 3) kF => X.map τ) h2
    simp only [Matrix.map_mul, Matrix.transpose_map] at h3
    rw [Matrix.diagonal_map (map_zero _)] at h3
    exact h3
  · refine irreducible_of_param_F τ h2K hPP' hP'P hι 1 W (fun S v hv => ?_)
    have h1 := hW S v hv
    rw [hY3] at h1
    simpa [baseConj] using h1
  · refine commutant_of_param_F τ h2K hPP' hP'P hι 1 T (fun S => ?_)
    have h1 := hT S
    rw [hY3] at h1
    simpa [baseConj] using h1
  · rw [hY3]
    have := RingHom.map_det τ (ι S : Matrix (Fin 3) (Fin 3) kF)
    rw [(ι S).2, map_one] at this
    simpa [RingHom.mapMatrix_apply] using this.symm

end Ad

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
