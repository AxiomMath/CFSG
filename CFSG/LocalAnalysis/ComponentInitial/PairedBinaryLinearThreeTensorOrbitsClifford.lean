module

public import CFSG.LocalAnalysis.ComponentInitial.PairedBinaryLinearThreeTensorOrbitsKSimple

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits

open Module CFSG.ProperTwoGeneratedCore.PairedTensor

instance finite_Efull : Finite Efull :=
  Finite.of_injective (fun e : Efull => (e.left, e.right)) fun _ _ h =>
    SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

instance free_T : Module.Free (ZMod 2) T := Module.Free.tensor

end CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits
