module

public import CFSG.HardMathSupport.Solomon.Coordinator.GapFinalDefs
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.Bridge.M24Surj
public import CFSG.Sporadic.Bridge.RuSurj
public import CFSG.Sporadic.J2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem card_of_isMJRType
    {X : Type*} [Group X]
    (h : IsMJRType X) :
    Nat.card X = 244823040 ∨ Nat.card X = 604800 ∨ Nat.card X = 145926144000 := by
  rcases h with h | h | h
  · left
    obtain ⟨e⟩ := h
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
    have b' : CFSG.Blueprint.NativeSporadic.M24 ≃* TauCeti.SporadicName.M24.Group := b
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M24
  · right; left
    obtain ⟨e⟩ := h
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
    have b' : CFSG.Blueprint.NativeSporadic.J2 ≃* TauCeti.SporadicName.J2.Group := b
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  · right; right
    obtain ⟨e⟩ := h
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
    have b' : CFSG.Blueprint.NativeSporadic.Ru ≃* TauCeti.SporadicName.Ru.Group := b
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.Ru.card_Ru

end CFSG.HardMathSupport.Solomon.Coordinator
