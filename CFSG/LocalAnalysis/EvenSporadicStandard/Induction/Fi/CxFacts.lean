module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsC
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Coexist
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Final

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi.Cx

open Subgroup Cover CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.EvenSporadicStandard.Induction.Fi.Eng

section Facts

attribute [-instance] Subgroup.mul


theorem fiRowFactsCore_cx (pf : FiPinned) (hyp12 : Hyp12Fi) (lo : LieModelOrders)
    (atl : FiAtlas) :
    FiRowFactsCore (IsOddCentralExt Fi23D) [.Fi23, .Fi24Prime] [] [.Fi22] := by
  have hmult : OddMultTrivial .Fi23 := fun L _ _ hq _ hcq => pf.mult23 L hq hcq
  have hfix23 : Fi23FixesElem := fi23FixesElem_of_atlas hmult atl.fi22Covers
  have hfix24 : Fi24InFixesElem := fi24InFixesElem_of_atlas atl.fi22Covers
  have hD : Even (Nat.card (center Fi23D)) := by rw [fi23D_card_center]; exact even_two
  have hnc : ¬ IsMulCommutative Fi23D := not_isMulCommutative_of_quasisimple fi23D_isQuasisimple
  have hn : 2 * 64561751654400 ≤ Nat.card Fi23D := by have := fi23D_card; omega
  refine
    { reach := reach_fi22K pf hyp12 atl.fi22Covers atl.fi22Even [.Fi23, .Fi24Prime] []
        (fun s hs => by simpa using hs) (by simp) (by simp)
      evenOut := fun s hs => by
        rcases List.mem_cons.1 hs with rfl | hs
        · exact fiEvenOut_fi23 pf _
        · rcases List.mem_singleton.1 hs with rfl
          exact fiEvenOut_fi24 pf _
      thm24 := fun s hs => by
        rcases List.mem_cons.1 hs with rfl | hs
        · exact Or.inr ⟨by decide, pinThm24Hex23 lo⟩
        · rcases List.mem_singleton.1 hs with rfl
          exact Or.inr ⟨by decide, pinThm24Hex24 lo⟩
      std_row := fiStdRow_of_list (D := Fi23D) (n := 2 * 64561751654400) fi23D_card_center hnc
        hn (fun s hs G _ _ L K u hcov hQ => by
          rcases List.mem_cons.1 hs with rfl | hs
          · exact solomonLocalQ_fi23 hmult hcov hQ
          · rcases List.mem_singleton.1 hs with rfl
            exact solomonLocalQ_fi24 hcov hQ)
      four_a := fiFourA_of_list (D := Fi23D) (n := 2 * 64561751654400) hD fi23D_card_center hnc
        hn (fun s hs G _ _ L K u hcov hQ => by
          rcases List.mem_cons.1 hs with rfl | hs
          · obtain ⟨-, -, -, -, -, hsol, htwo, -⟩ := (lemma36DataQ_fi23 hmult hfix23).data G L K u
              hcov hQ
            exact ⟨hsol, htwo⟩
          · rcases List.mem_singleton.1 hs with rfl
            obtain ⟨-, -, -, -, -, hsol, htwo, -⟩ := (lemma36DataQ_fi24in hfix24).data G L K u
              hcov hQ
            exact ⟨hsol, htwo⟩)
        (fun K₂ _ _ hperf ⟨X, _, hX, ⟨e⟩⟩ => by
          obtain ⟨f⟩ := k3_cq_fi22 hX
          exact atl.fi22Covers K₂ hperf ⟨e.trans f⟩) }

theorem fi23_not_fi24 {X : Type} [Group X] (h23 : IsSporadic X .Fi23) :
    ¬ IsSporadic X .Fi24Prime :=
  not_isSporadic_of_card_ne (card_of_isSporadic pinCard23 h23) pinCard24 (by norm_num)

theorem fiHyp31Max_of_atlas (pf : FiPinned) (hyp12 : Hyp12Fi) (lo : LieModelOrders)
    (atl : FiAtlas) (lx : Hyp31LitX) :
    V3.FiHyp31Max (IsOddCentralExt Fi23D) := by
  have rf := fiRowFactsCore_cx pf hyp12 lo atl
  intro lit hrow H _ _ ih N hN hidx hkp hN22 hN23 hN24 hmax L hL hcov
  have ih' : BelowSec (Sol78PredS ([.Fi23, .Fi24Prime] ++ [] ++ [.Fi22])) H :=
    BelowSec.mono_types (fun s hs => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with (rfl | rfl) | rfl <;> simp [fiTypes]) ih
  have hjunc : JunctionStmtAt H := Junction.sol78JunctionAt_of_cor23SSec (lit.cor23.sec ih.uHered)
  refine fiHyp31_core rf lx lit hrow ih' hN hidx hkp
    ⟨noUp_nil, noLink5bOut_of_types ih' noUp_nil ?_ rf.evenOut hN hidx hkp⟩ ?_ hN22 hN23 hN24 hL
    hcov
  · intro s hs
    rcases List.mem_cons.1 hs with rfl | hs
    · exact Or.inr (Or.inr ⟨rfl, hmax, fun X _ h => fi23_not_fi24 h⟩)
    · rcases List.mem_singleton.1 hs with rfl
      exact Or.inl pinFi23Excl24
  · intro L₁ hL₁ s' hs' hsp
    rcases List.mem_cons.1 hs' with rfl | hs'
    · exact hmax L₁ hL₁ hsp
    · rcases List.mem_singleton.1 hs' with rfl
      exact fiMaximal_of_central_type fiLink5bSection hjunc ih' noUp_nil hN hidx hkp hL₁
        (by simp) hsp (Or.inl pinFi23Excl24) (fiEvenOut_fi24 pf []) pinNotExc24

end Facts

end CFSG.EvenSporadicStandard.Induction.Fi.Cx
