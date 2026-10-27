module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.RowC

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup Cover CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

theorem isLS_fi2324 {X : Type} [Group X] (h : IsLS [.Fi23, .Fi24Prime] X) :
    IsLS [.Fi23] X ∨ IsLS [.Fi24Prime] X := by
  obtain ⟨s, hs, hq, hodd, hsp⟩ := h
  rcases List.mem_cons.1 hs with rfl | hs
  · exact Or.inl ⟨_, List.mem_singleton_self _, hq, hodd, hsp⟩
  · rcases List.mem_singleton.1 hs with rfl
    exact Or.inr ⟨_, List.mem_singleton_self _, hq, hodd, hsp⟩

section Facts

@[expose] noncomputable def stage3Row_fi2324 (hmult : OddMultTrivial .Fi23)
    (hfix23 : Fi23FixesElem) (hfix24 : Fi24InFixesElem) :
    Stage3Row [.Fi23, .Fi24Prime] (fun _ => fiLoc (2 * 64561751654400)) where
  IsK := IsOddCentralExt Fi23D
  m := fun _ => 2
  rec36 := fun s hs => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact Rec36.old 16 (lemma36DataQ_fi23 hmult hfix23)
    · rcases List.mem_singleton.1 hs with rfl
      exact Rec36.old 16 (lemma36DataQ_fi24in hfix24)
  outTwo := fun s hs H _ M hM => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact outTwoCovers_fi23 hmult .Fi23 (List.mem_singleton_self _) H M hM
    · rcases List.mem_singleton.1 hs with rfl
      exact outTwoCovers_fi24 .Fi24Prime (List.mem_singleton_self _) H M hM
  hyp31Row :=
    { isK_inv := isKFi23_inv
      isL_inv := IsLS.isoInv _
      quasi_K := (stage3Row_fi23 hmult hfix23).hyp31Row.quasi_K
      quasi_L := fun X _ hX => (isLS_fi2324 hX).elim
        (fun h => (stage3Row_fi23 hmult hfix23).hyp31Row.quasi_L X h)
        (fun h => (stage3Row_fi24 hfix24).hyp31Row.quasi_L X h)
      K_not_exc := (stage3Row_fi23 hmult hfix23).hyp31Row.K_not_exc
      K_ne_L := fun X Y _ _ hX hY => (isLS_fi2324 hX).elim
        (fun h => (stage3Row_fi23 hmult hfix23).hyp31Row.K_ne_L X Y h hY)
        (fun h => (stage3Row_fi24 hfix24).hyp31Row.K_ne_L X Y h hY) }
  rowIsK := fun s hs H _ L K u hcov hQ => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact fi23_rowIsK hmult .Fi23 (List.mem_singleton_self _) H L K u hcov hQ
    · rcases List.mem_singleton.1 hs with rfl
      exact fi24_rowIsK .Fi24Prime (List.mem_singleton_self _) H L K u hcov hQ
  rowExists := fun s hs H _ _ L hcov => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact fi23_rowExists hmult .Fi23 (List.mem_singleton_self _) H L hcov
    · rcases List.mem_singleton.1 hs with rfl
      exact fi24_rowExists .Fi24Prime (List.mem_singleton_self _) H L hcov
  rowFit := fun s hs H _ _ L K hcov hKL hKq hK hstd haut => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact fi23_rowFit .Fi23 (List.mem_singleton_self _) H L K hcov hKL hKq hK hstd haut
    · rcases List.mem_singleton.1 hs with rfl
      exact fi24_rowFit .Fi24Prime (List.mem_singleton_self _) H L K hcov hKL hKq hK hstd haut
  inOrTwoSylow := Or.inl fun s hs H _ L K u hcov hQ => by
    rcases List.mem_cons.1 hs with rfl | hs
    · have := oddCover_finite fi23_finite hcov
      obtain ⟨-, huK, -⟩ := (lemma36DataQ_fi23 hmult hfix23).data ↥L ⊤ (K.subgroupOf L)
        ⟨u, hQ.1⟩ (oddCover_top_of_cover hcov) (fiLoc_restrict hQ)
      exact huK
    · rcases List.mem_singleton.1 hs with rfl
      have := oddCover_finite fi24_finite hcov
      obtain ⟨-, huK, -⟩ := (lemma36DataQ_fi24in hfix24).data ↥L ⊤ (K.subgroupOf L)
        ⟨u, hQ.1⟩ (oddCover_top_of_cover hcov) (fiLoc_restrict hQ)
      exact huK

end Facts

end CFSG.EvenSporadicStandard.Induction.Fi
