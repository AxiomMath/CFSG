module

public import CFSG.CGT.PushingUpLit.SolKR2.Setup
public import CFSG.CGT.PushingUpLit.SolKR2.OfRankTwo
public import CFSG.CGT.PushingUpLit.SolKAb.Residue

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG.CGT.PushingUpLit.SolKAb

section Main


theorem solomonTimmesfeldMainRankTwo_of_facts (hF : R2First)
    (hfacts : ∀ (G : Type) [Group G] [Finite G] (M B : Subgroup G) (h : R2 M B), R2Facts h) :
    SolomonTimmesfeldMainRankTwo := by
  intro G _ _ _ hs hna K hK hM hFs R hc hne h4 hH
  have := hs
  have S : STSetting G K := ⟨hs, hna, hK, hM, hFs⟩
  have h := R2.of_rankTwo S R hc hne h4 hH
  exact (R2.false_of_facts hna hF h (hfacts G _ _ h)).elim

end Main

end CFSG.CGT.PushingUpLit.SolKR2
