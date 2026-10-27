module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12

public section

namespace CFSG.BenderSuzuki.Background

open CFSG.BenderSuzuki.External CFSG.BenderSuzuki.MatrixGroups
open scoped Matrix
open scoped commutatorElement

universe u

private theorem hermitianUnipotentPSU_injective1012
    {K : Type u} [Field K]
    (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Function.Injective (hermitianUnipotentPSU J hJstandard) := by
  apply (injective_iff_map_eq_one (hermitianUnipotentPSU J hJstandard)).2
  intro z hz
  have hmk : Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z) = 1 :=
    congrArg Subtype.val hz
  have hzcenter : hermitianUnipotentGL J z ∈
      Subgroup.center (GL (Fin 3) K) := by
    rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
    exact hmk
  rcases Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
    hzcenter with ⟨c, hc⟩
  have hc_one : c = 1 := by
    have h00 := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) hc
    rw [hermitianUnipotentGL_val] at h00
    simpa [hermitianUnipotentMatrix, Matrix.scalar_apply] using h00
  have hz1 : z.1.1 = 0 := by
    have h01 := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) K => M 0 1) hc
    rw [hermitianUnipotentGL_val, hc_one] at h01
    simpa [hermitianUnipotentMatrix, Matrix.scalar_apply] using h01.symm
  have hz2 : z.1.2 = 0 := by
    have h02 := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) hc
    rw [hermitianUnipotentGL_val, hc_one] at h02
    simpa [hermitianUnipotentMatrix, Matrix.scalar_apply] using h02.symm
  change z = hermitianUnipotentOne J
  apply Subtype.ext
  apply Prod.ext
  · exact hz1
  · exact hz2

theorem hermitianUnipotent_commutator_fst
    {K : Type u} [Field K] {n : ℕ} (J : HermitianForm n K)
    (z w : hermitianUnipotentCoord J) : (⁅z, w⁆).1.1 = 0 := by
  rw [hermitianUnipotent_commutator]

theorem hermitianUnipotentPSU_injective
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Function.Injective (hermitianUnipotentPSU J hJstandard) :=
  hermitianUnipotentPSU_injective1012 J hJstandard

end CFSG.BenderSuzuki.Background
