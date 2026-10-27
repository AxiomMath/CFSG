module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X35 CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Layer CFSG.SectionRank

theorem no_A6_component_final
    {V : Type} [CommGroup V] [Finite V]
    {H T M E : Subgroup (MulAut V)} (hFF : Family.FFHyp V H T M E) (hns : ¬ Group.IsSolvable ↥H)
    (hsqtk : IsSQTKCat ↥H) {L : Subgroup (MulAut V)} (hL : Family.IsComp L H) :
    ¬ Nonempty (Family.CQ L ≃* alternatingGroup (Fin 6)) :=
  no_A6_component_unconditional oddKernelCentralization catalogStepHyp hFF hns hsqtk hL

end CFSG.QuasithinUnique.Setup.X3
