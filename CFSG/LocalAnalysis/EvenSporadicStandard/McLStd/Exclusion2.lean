module

public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.OuterCase
public import CFSG.LocalAnalysis.EvenSporadicStandard.LyStd.NoSwapped

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup CFSG CFSG.Blueprint.NativeSporadic CFSG.ComponentClassification.GSThmB

structure McLLyContainerInputs : Prop where
  solomon : Solomon2AnInput
  containerMcL : ContainerIsDoubleCover .McL
  containerLy : ContainerIsDoubleCover .Ly

theorem mcl_ly_not_standard_of_container
    (hI : McLLyContainerInputs) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (h : StdHyp G L) : ¬ IsSporadic L .McL ∧ ¬ IsSporadic L .Ly :=
  ⟨mcl_not_standard_of_container hI.solomon hI.containerMcL h,
    LyStd.ly_not_standard_of_container hI.solomon hI.containerLy h⟩

end CFSG.EvenSporadicStandard.McLStd
