module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.SuzRow

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.HypOne.Suz

theorem suz_autCenterCond_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .Suz) : AutCenterCond Y := by
  obtain ⟨e⟩ := h
  exact AutCenterCond.of_mulEquiv (e.trans suzEquivM).symm suz_autCenterCond_native

theorem suz_umovesCond_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .Suz) : UMovesCond Y := by
  obtain ⟨e⟩ := h
  exact UMovesCond.of_mulEquiv (e.trans suzEquivM).symm suz_umovesCond_native

end CFSG.EvenSporadicStandard.Solomon78
