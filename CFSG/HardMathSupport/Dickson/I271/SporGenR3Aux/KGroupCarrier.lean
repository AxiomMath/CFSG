module

public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Fam
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem isKGroup_sporadic_of_sporType {X : Type} [Group X] (hX : CFSG.Open.IsKGroup X)
    {K : Subgroup X} {name : TauCeti.SporadicName} (hS : I271SporType K name) :
    CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic name).Group := by
  obtain ⟨e⟩ := hS
  exact ((hX.subgroup K).quotient (Subgroup.center ↥K)).of_surjective e.toMonoidHom e.surjective

theorem isKGroup_carrier_of_sporType (hBr : SporadicBridges) {X : Type} [Group X]
    (hX : CFSG.Open.IsKGroup X) {K : Subgroup X} {name : TauCeti.SporadicName}
    (hS : I271SporType K name) : CFSG.Open.IsKGroup (NativeSporadic.Carrier name) := by
  have h := isKGroup_sporadic_of_sporType hX hS
  exact h.of_surjective (hBr name).some.symm.toMonoidHom (hBr name).some.symm.surjective

end CFSG.HardMathSupport.Dickson.I271
