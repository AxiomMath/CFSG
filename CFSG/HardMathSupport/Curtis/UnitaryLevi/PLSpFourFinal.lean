module

public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeDefs
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLSpFourTransfer
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLSp

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.OutcomeLocal
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Cooperstein.StructureLie
open scoped commutatorElement

theorem spFourTransvectionCent_holds : SpFourTransvectionCent := by
  intro W _ _ _ f h4 hnd halt t ht htv hn
  obtain ⟨Φ⟩ := nonempty_bilinIsometryGroup_mulEquiv_perm_six hnd halt h4
  obtain ⟨e1⟩ := CFSG.HardMathSupport.Curtis.UnitaryLevi.nonempty_commutator_inf_centralizer_equiv
    (bilinIsometryGroup f) Φ t ht
  have hsq : t * t = 1 := by
    obtain ⟨φ, a, h, -, -, rfl⟩ := (isF2Transvection_iff t).mp htv
    exact tv_mul_self φ a h
  have hsq' : Φ ⟨t, ht⟩ * Φ ⟨t, ht⟩ = 1 := by
    rw [← map_mul, ← map_one Φ]
    congr 1
    exact Subtype.ext hsq
  obtain ⟨e2⟩ := CFSG.HardMathSupport.Curtis.UnitaryLevi.nonempty_alt_inf_centralizer_of_odd_involution
    _ hsq' (CFSG.HardMathSupport.Curtis.UnitaryLevi.sign_eq_neg_one_of_notMem_commutator
      (bilinIsometryGroup f) Φ t ht hn)
  exact ⟨e1.trans e2⟩

end CFSG.HardMathSupport.Curtis.Coordinator.PLType
