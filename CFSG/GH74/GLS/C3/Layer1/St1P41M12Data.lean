module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFixedData
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpElim

open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

@[expose] def permJ : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 6] * List.formPerm [1, 11] * List.formPerm [2, 10] * List.formPerm [3, 5] *
    List.formPerm [4, 7] * List.formPerm [8, 9]

@[expose] def wordJ : List ℤ := [1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2]

@[expose] def Inner5152 : Prop :=
  evalCodes [m12gA, m12gB] wordJ = permJ ∧ permJ * permJ = 1 ∧ permJ * permZ = permZ * permJ ∧
    permJ ≠ permZ ∧ (Finset.univ.filter fun i : Fin 12 => permJ i = i).card = 0 ∧
    (Finset.univ.filter fun i : Fin 12 => (permZ * permJ) i = i).card = 0

end CFSG.GH74.GLS.C3.Layer1.PumpElim
