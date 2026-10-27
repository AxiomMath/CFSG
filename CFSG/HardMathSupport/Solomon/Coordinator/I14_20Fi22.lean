module

public import CFSG.Sporadic.Bridge.Fi22Surj
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

abbrev Fi22G : Type := (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group

theorem fi22_facts :
    IsSimpleGroup Fi22G ∧ Nat.card Fi22G = 64561751654400 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have e' : CFSG.Blueprint.NativeSporadic.Fi22 ≃* Fi22G := e
  refine ⟨@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 e'.symm, ?_⟩
  rw [← Nat.card_congr e'.toEquiv]
  exact CFSG.Sporadic.Fi22.card_Fi22

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
