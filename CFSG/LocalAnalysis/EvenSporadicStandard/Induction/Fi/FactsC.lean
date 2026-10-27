module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.RowC
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsB

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup Cover CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.Sporadic CFSG.Sporadic.Fi24

section Facts

attribute [-instance] Subgroup.mul


theorem solomonLocalQ_fi24 {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hcov : OddCover .Fi24Prime L) (hQ : fiLoc (2 * 64561751654400) H L K u) :
    SolomonLocalQ L K u := by
  obtain ⟨huL, hbase, -⟩ := fi24in_data hcov hQ
  obtain ⟨-, hu2, hKL, hKu, hKq, -⟩ := id hQ
  exact fi24in_solomonLocalQ_of_base hcov.1 hcov.odd_center hKq huL
    (hcov.not_mem_centralizer_of_orderOf_two huL hu2) hu2 hKL hKu hbase

theorem fi24InFixesElem_of_atlas (hfix : Fi22CoversFixesElem) : Fi24InFixesElem := by
  intro H _ _ L K u hcov hQ
  have hK : IsOddCentralExt Fi23D ↥K :=
    fi24_rowIsK .Fi24Prime (List.mem_singleton_self _) H L K u hcov hQ
  have : Finite ↥K := oddCentralExt_finite hK
  exact hfix ↥K (oddCentralExt_perfect hK) (k3_cq_fi22 hK)

theorem fiRowFacts_fi24 (pf : FiPinned) (hyp12 : Hyp12Fi) (lo : LieModelOrders)
    (atl : FiAtlas) :
    Eng.FiRowFacts IsKFi24 [.Fi24Prime] [.Fi23] [.Fi22] := by
  have hfix24 : Fi24InFixesElem := fi24InFixesElem_of_atlas atl.fi22Covers
  refine
    { fi23 := fun s hs => Or.inl (by rcases List.mem_singleton.1 hs with rfl; exact pinFi23Excl24)
      reach := reach_fi22K pf hyp12 atl.fi22Covers atl.fi22Even [.Fi24Prime] [.Fi23]
        (fun s hs => by simpa [or_comm] using hs) (by simp) (by simp)
      evenOut := fun s hs => by
        rcases List.mem_singleton.1 hs with rfl
        exact fiEvenOut_fi24 pf _
      thm24 := fun s hs => by
        rcases List.mem_singleton.1 hs with rfl
        exact Or.inr ⟨by decide, pinThm24Hex24 lo⟩
      std_row := fiStdRow_of (D := Fi23D) fi23D_card_center
        (not_isMulCommutative_of_quasisimple fi23D_isQuasisimple)
        (by have := fi23D_card; omega) (fun G _ _ L K u hcov hQ => solomonLocalQ_fi24 hcov hQ)
      four_a := fiFourA_of (D := Fi23D) (s' := .Fi24Prime) (n := 2 * 64561751654400)
        (by rw [fi23D_card_center]; exact even_two) fi23D_card_center
        (not_isMulCommutative_of_quasisimple fi23D_isQuasisimple)
        (by have := fi23D_card; omega)
        (fun G _ _ L K u hcov hQ => by
          obtain ⟨-, -, -, -, -, hsol, htwo, -⟩ := (lemma36DataQ_fi24in hfix24).data G L K u
            hcov hQ
          exact ⟨hsol, htwo⟩)
        (fun K₂ _ _ hperf ⟨X, _, hX, ⟨e⟩⟩ => by
          obtain ⟨f⟩ := k3_cq_fi22 hX
          exact atl.fi22Covers K₂ hperf ⟨e.trans f⟩) }

end Facts

end CFSG.EvenSporadicStandard.Induction.Fi
