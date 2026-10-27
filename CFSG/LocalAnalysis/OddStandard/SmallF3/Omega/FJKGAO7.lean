module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAIso
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeHigh
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IAutStd
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IFaith

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.LieType.Universal.Spin (quadOdd nondegenerate_quadOdd)

theorem fjIsomInv_seven : FJIsomInv (nondegenerate_quadOdd 3 (ZMod 3)) := by
  have hQ₀ : (quadOdd 3 (ZMod 3)).Nondegenerate := nondegenerate_quadOdd 3 (ZMod 3)
  have h7 : Module.finrank (ZMod 3) (Fin 3 ⊕ Fin 3 ⊕ Unit → ZMod 3) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card]
    decide
  intro α hα
  obtain ⟨A, hA⟩ := sec4I_exists_conj_of_mulAut_std α
  have hαeq : α = projAut hQ₀ A := by
    ext p
    rw [coe_projAut]
    exact hA p
  have hαA : projAut hQ₀ A * projAut hQ₀ A = 1 := by
    rw [← hαeq]
    exact hα
  refine ⟨A, fj_mul_self_eq_one_of_odd hQ₀ (by rw [h7]; decide) ?_, hαeq⟩
  apply conjNormal_injective_seven hQ₀ h7 (quadSign_quadOdd 3)
  rw [map_mul, map_one]
  simpa [projAut] using hαA

theorem fjKGAAt_omegaProj_seven : FJKGAAt ↥(omegaProj (nondegenerate_quadOdd 3 (ZMod 3))) := by
  refine fjKGAAt_of_isomInv (nondegenerate_quadOdd 3 (ZMod 3)) ?_ fjIsomInv_seven
  rw [Module.finrank_fintype_fun_eq_card]
  decide

theorem fjKGAAt_of_lieModel_odd {Y : Type} [Group Y] (h : LieModel Y .POmegaOdd 3 3 1) :
    FJKGAAt Y := by
  obtain ⟨f⟩ := IsOmegaStar.nonempty_equiv (isOmegaStar_of_lieModel_odd h) (by norm_num)
    (nondegenerate_quadOdd 3 (ZMod 3))
    (by rw [Module.finrank_fintype_fun_eq_card]; decide) (quadSign_quadOdd 3)
  exact fjKGAAt_of_mulEquiv f.symm fjKGAAt_omegaProj_seven

end CFSG.OddStandard.SmallF3.Omega
