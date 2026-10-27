module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeHigh
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapesAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint
open CFSG.LieType.Universal.Spin (quadPlus nondegenerate_quadPlus)

theorem fk_center_omegaProj :
    Subgroup.center ↥(omegaProj (nondegenerate_quadPlus 4 (ZMod 3))) = ⊥ := by
  have hdim : Module.finrank (ZMod 3) (Fin 4 ⊕ Fin 4 → ZMod 3) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    decide
  have hmodel : LieModel ↥(omegaProj (nondegenerate_quadPlus 4 (ZMod 3))) .POmegaPlus 4 3 1 :=
    isOmegaStar_eight_plus_iff.mp
      ⟨Fin 4 ⊕ Fin 4 → ZMod 3, inferInstance, inferInstance, inferInstance, quadPlus 4 (ZMod 3),
        nondegenerate_quadPlus 4 (ZMod 3), hdim, quadSign_quadPlus 4, ⟨MulEquiv.refl _⟩⟩
  have hsimple : IsSimpleGroup ↥(omegaProj (nondegenerate_quadPlus 4 (ZMod 3))) :=
    (CFSG.LieType.Simplicity.fam_classical_converse
      ↥(omegaProj (nondegenerate_quadPlus 4 (ZMod 3)))
      ⟨.POmegaPlus, 4, 3, 1,
        hmodel.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)⟩).2.2
  have hcard : Nat.card ↥(omegaProj (nondegenerate_quadPlus 4 (ZMod 3))) = 4952179814400 := by
    rw [hmodel.card_eq_lieOrd (by norm_num : (4 : ℕ) ≠ 0)]
    decide +kernel
  haveI : Finite ↥(omegaProj (nondegenerate_quadPlus 4 (ZMod 3))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : IsSimpleGroup ↥(omegaProj (nondegenerate_quadPlus 4 (ZMod 3))) := hsimple
  have hnotprime : ¬ (4952179814400).Prime := by
    intro hp
    have hodd := hp.odd_of_ne_two (by norm_num)
    exact Nat.not_even_iff_odd.mpr hodd (by norm_num : Even 4952179814400)
  have hnc : ∃ a b : ↥(omegaProj (nondegenerate_quadPlus 4 (ZMod 3))), a * b ≠ b * a :=
    ff_noncomm_of_simple_card hsimple (by rw [hcard]; exact hnotprime)
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    (Q := ↥(omegaProj (nondegenerate_quadPlus 4 (ZMod 3)))) hnc).2

end CFSG.OddStandard.SmallF3.Omega
