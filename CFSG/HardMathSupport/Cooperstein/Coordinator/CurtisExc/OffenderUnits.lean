module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt
public import CFSG.Quasithin.H13.NQTermTransvectionSaturation
public import CFSG.Sporadic.Schreier.J4SSylowBase

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor

section Units

variable {W : Type} [CommGroup W] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  (θ : W ≃* Multiplicative V)

@[expose] def binUnits : MulAut W ≃* (Module.End (ZMod 2) V)ˣ :=
  (Layer.binPsi θ).trans (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm

theorem binUnits_val (φ : MulAut W) (v : V) :
    (binUnits θ φ).val v =
      Multiplicative.toAdd (θ (φ (θ.symm (Multiplicative.ofAdd v)))) := rfl

theorem binUnits_val_eq (φ : MulAut W) (v : V) :
    (binUnits θ φ).val v = Layer.binPsi θ φ v := rfl

end Units

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
