module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalLiftedTorus

public section

namespace CFSG.LocalAnalysis.ComponentInitial.NormTail

open Matrix

theorem diagHom_injective (F : Type) [Field F] : Function.Injective (diagHom F) := by
  intro s t hst
  refine Units.ext ?_
  have h := congrArg (fun A : SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 0) hst
  simpa [diagHom_apply, coe_diagSL] using h

end CFSG.LocalAnalysis.ComponentInitial.NormTail
