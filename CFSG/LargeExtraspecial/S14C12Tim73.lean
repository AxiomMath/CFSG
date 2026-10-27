module

public import CFSG.LargeExtraspecial.S14C12THyp
public import CFSG.Timmesfeld.Assembly
public import CFSG.LargeExtraspecial.S14C12Lit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open CFSG.Open CFSG.Blueprint

theorem twistedE6_of_threeFourPlus {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6))
    (hD : ThreeFourPlusClass G {g | IsConj S.z g})
    (hnd : ∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4) :
    ChevalleyExceptionalModel G .twistedE6 2 1 := by
  obtain ⟨a, b, ha, hb, h4⟩ := hnd
  exact twistedE6_of_outcome S hw hU
    (Timmesfeld.outcome (hyp_of_threeFourPlusClass hD ⟨a, ha, b, hb, h4⟩))

theorem reifartSmithU62Input_of_smith (h : SmithU62ThreeFourInput) : ReifartSmithU62Input := by
  intro G _ _ _ S hw hU
  obtain ⟨hprod, hnd⟩ := h G S hw hU
  exact twistedE6_of_threeFourPlus S hw hU (threeFourPlusClass_of_products S hprod) hnd

end CFSG.LargeExtraspecial.S14
