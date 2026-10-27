module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Hyp31D
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Hyp31C

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

section Co1Inputs


structure Co1Hyp31Inputs : Prop where
  g24_model : LieModel ↥twoBD .G2 0 2 2
  aut_centralizer : Co1AutCentralizerN0
  g24_fixed : G24FixedNonsolvable
  no_co1 : Co1NotInG2
  rank : Co1CoverRank
  even : EvenCoverExclHered .Co1

end Co1Inputs


theorem co1ReachRow (lit : Sol78Lit) (hmult : OddMultTrivial .Co1) (inp : Co1Hyp31Inputs) :
    ReachRow IsKCo1O [.Co1] [] [] Co1R where
  iso := co1R_iso
  fi23 := co1_fi23
  fi23_lo := fun _ hs => absurd hs List.not_mem_nil
  K_reach := fun _ _ h => co1_K_reach inp.g24_model h
  K_quot := fun _ _ h => co1_K_quot h
  K_not_sporadic := co1_K_not_sporadic
  K_odd_lo := fun _ _ _ _ _ hs => absurd hs List.not_mem_nil
  lo := Or.inl fun _ hs => absurd hs List.not_mem_nil
  K_iso := fun _ _ _ _ hX hY _ _ => co1_K_iso hX hY
  K_cq := fun _ _ _ _ hX hY => co1_K_cq hX hY
  not_exc := co1_not_exc
  sp_not_exc := co1_sp_not_exc
  rank := fun X _ _ hq hR hodd => co1_rank inp.rank X hq hR hodd
  up_reach := fun _ hs => absurd hs List.not_mem_nil
  closure := co1_closure lit.thm412
  notR := co1_notR hmult inp.no_co1
  pair_into := co1_pair_into lit.thm412 inp.g24_model

theorem hyp31RowFacts_co1 (lit : Sol78Lit) (hmult : OddMultTrivial .Co1) (lo : LieModelOrders)
    (inp : Co1Hyp31Inputs) : Hyp31RowFacts IsKCo1O [.Co1] [] [] where
  reach := ⟨Co1R, co1ReachRow lit hmult inp⟩
  evenOut := fun s hs => by
    rcases List.mem_singleton.1 hs with rfl
    exact inp.even
  up := co1_up
  thm24 := co1_thm24 lo
  std_row := fun _ _ _ L K₁ T s hL _ hdata hq hK => co1_std_row hmult L K₁ T s hL hdata hq hK
  four_a := co1_fourA hmult inp.aut_centralizer inp.g24_fixed

end CFSG.EvenSporadicStandard.Induction
