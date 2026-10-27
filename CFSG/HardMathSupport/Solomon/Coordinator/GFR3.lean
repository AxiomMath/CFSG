module

public import CFSG.HardMathSupport.Solomon.Coordinator.GapFinalDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3M24
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3J2
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Ru

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem gapFinalBalance_holds :
    GapFinalBalance := by
  intro X _ _ hX
  rcases hX with h | h | h
  · obtain ⟨e⟩ := h
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
    exact IsLocallyBalancedAbs.of_mulEquiv (K := X) (K' := ↥NativeSporadic.M24)
      (e.trans b.symm) balance_M24_three
  · obtain ⟨e⟩ := h
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
    exact IsLocallyBalancedAbs.of_mulEquiv (K := X) (K' := NativeSporadic.J2)
      (e.trans b.symm) balance_J2_three
  · obtain ⟨e⟩ := h
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
    exact IsLocallyBalancedAbs.of_mulEquiv (K := X) (K' := NativeSporadic.Ru)
      (e.trans b.symm) balance_Ru_three

end CFSG.HardMathSupport.Solomon.Coordinator
