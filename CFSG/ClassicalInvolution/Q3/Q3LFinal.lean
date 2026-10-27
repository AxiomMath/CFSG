module

public import CFSG.ClassicalInvolution.Q3.Q3LRes
public import CFSG.ClassicalInvolution.Q3.Q3LMain

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification

section TightDef

@[expose] def SolvableMemberInnerTight : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ (z : Y) (L : Subgroup Y), IsClassicalMember3 L z →
      ∀ T : Subgroup Y, IsComponentOf T ⊤ → T ⊔ L = ⊤ →
        L ≤ T ⊔ Subgroup.centralizer (T : Set Y)

theorem solvableMemberInnerTight_of_inner (h : SolvableMemberInner) : SolvableMemberInnerTight :=
  fun Y _ _ _ hO z L hz T hT _ => h Y hO z L hz T hT

theorem solvableMemberInnerTight_of_L2PrimeBalanceSolv (hb : L2PrimeBalanceSolv) :
    SolvableMemberInnerTight :=
  solvableMemberInnerTight_of_inner (solvableMemberInner_of_L2PrimeBalanceSolv hb)

end TightDef


theorem solvableMemberInnerBelow_of_tight (hM : M11Facts) (h : SolvableMemberInnerTight) :
    SolvableMemberInnerBelow := by
  intro Y _ _ hBelow hO z L hz T hT
  by_cases hTL : T ⊔ L = ⊤
  · exact h Y hBelow hO z L hz T hT hTL
  · exact le_sup_centralizer_of_sup_ne_top hM hBelow hO hz hT hTL

theorem quasisimpleConnected3Comp_of_tight (hM : M11Facts) (h : SolvableMemberInnerTight) :
    QuasisimpleConnected3Comp :=
  quasisimpleConnected3Comp_of_innerBelow (solvableMemberInnerBelow_of_tight hM h)

theorem quasisimpleConnected3_of_tight (hM : M11Facts) (h : SolvableMemberInnerTight) :
    QuasisimpleConnected3 :=
  quasisimpleConnected3_of_comp (quasisimpleConnected3Comp_of_tight hM h)

end CFSG.ClassicalInvolution.Q3
