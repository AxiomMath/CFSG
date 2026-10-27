module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.RowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverE8Rank

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

structure HNHyp31Inputs : Prop where
  mult_odd : HNMultiplierOdd
  outer_cent : HNOuterInvCent
  hs_fix : HSFixedNonsolvable
  cat_hs : Balance.CatalogNoHSOdd
  two_hs : TwoHSHostHered

section HNRowFacts



abbrev HNKnown : GroupClass := fun X _ => IsSporadic X .HS ∨ IsSporadic X .HN

theorem hnReachRow (hmult : OddMultTrivial .HN) (inp : HNHyp31Inputs) :
    ReachRow IsKHN [.HN] [] [] HNKnown where
  iso := fun X Y _ _ e h => h.imp (fun ⟨f⟩ => ⟨e.symm.trans f⟩) (fun ⟨f⟩ => ⟨e.symm.trans f⟩)
  fi23 := fun s hs => by
    rcases List.mem_append.1 hs with h | h
    · rcases List.mem_singleton.1 h with rfl
      exact hn_fi23
    · exact absurd h List.not_mem_nil
  fi23_lo := fun s hs => absurd hs List.not_mem_nil
  K_reach := fun X _ h => Or.inl (isKHN_data h).2.2.1
  K_quot := fun X _ h => isKPinned_isoInv .HN _ X (X ⧸ CFSG.oddCore X)
    (quotientOddCoreEquiv (isKHN_oddCore h)).symm h
  K_not_sporadic := fun X _ h s hs => by
    rcases List.mem_append.1 hs with h' | h'
    · rcases List.mem_singleton.1 h' with rfl
      intro hX
      have h1 := hs_pinned_card _ (isKHN_data h).2.2.1
      have h2 := hn_pinned_card _ hX
      omega
    · exact absurd h' List.not_mem_nil
  K_odd_lo := fun X _ _ _ s hs => absurd hs List.not_mem_nil
  lo := Or.inl fun s hs => absurd hs List.not_mem_nil
  K_iso := fun X Y _ _ hX hY _ _ => isKHN_iso hX hY
  K_cq := fun X Y _ _ hX hY => by
    obtain ⟨eX⟩ := (isKHN_data hX).2.2.1
    obtain ⟨eY⟩ := (isKHN_data hY).2.2.1
    exact ⟨eX.trans eY.symm⟩
  not_exc := fun X _ h => h.elim (fun hs => hs_sp_not_exc X hs) (fun hn => hn_sp_not_exc X hn)
  sp_not_exc := fun s hs => by
    rcases List.mem_append.1 hs with h | h
    · rcases List.mem_singleton.1 h with rfl
      exact hn_sp_not_exc
    · exact absurd h List.not_mem_nil
  rank := fun X _ _ hq hR hodd => by
    rcases hR with hHS | hHN
    · obtain ⟨e⟩ := hHS
      exact three_le_pRank_hs_cover e
    · exact absurd (inp.mult_odd X hq hHN) (fun h => hodd h ⟨.HN, by simp, hHN⟩ |>.elim)
  up_reach := fun s hs => absurd hs List.not_mem_nil
  closure := fun Y _ _ hY N' hN hidx hkp P hP hPq hR hns _ _ hscope => by
    rcases hR with hHS | hHN
    · exact hn_closure inp.cat_hs (inp.two_hs Y hY) hN hidx hkp hP hPq hHS hscope
    · exact absurd ⟨.HN, by simp, hHN⟩ hns
  notR := fun Y _ _ N hN hidx _ ⟨L, hL, s, hs, hcov⟩ hR => by
    rcases List.mem_singleton.1 hs with rfl
    exact hn_notR hN hidx hL hcov hR
  pair_into := fun Y _ _ _ N' hN hidx _ P hP hPq hR hns _ _ ⟨s, hs, hN'⟩ => by
    rcases List.mem_singleton.1 hs with rfl
    rcases hR with hHS | hHN
    · exact hn_pair_into inp.cat_hs hN hidx hP hPq hHS hN'
    · exact absurd ⟨.HN, by simp, hHN⟩ hns

theorem hyp31RowFacts_hn (hmult : OddMultTrivial .HN) (lo : LieModelOrders)
    (inp : HNHyp31Inputs) : Hyp31RowFacts IsKHN [.HN] [] [] where
  reach := ⟨HNKnown, hnReachRow hmult inp⟩
  evenOut := fun s hs => by
    rcases List.mem_singleton.1 hs with rfl
    exact evenCoverExcl_of_odd inp.mult_odd
  up :=
    { fi23 := fun s hs => absurd hs List.not_mem_nil
      not_exc := fun s hs => absurd hs List.not_mem_nil
      odd := fun s hs => absurd hs List.not_mem_nil
      rank := fun s hs => absurd hs List.not_mem_nil }
  thm24 := fun s hs => by
    rcases List.mem_singleton.1 hs with rfl
    refine Or.inr ⟨by decide, fun X _ hq hodd hX => thm24Hex_of_card lo hn_pinned_card
      (by norm_num) (factorial_div_two_ne_of_between (n₀ := 17) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial])) X hq hodd hX⟩
  std_row := fun G _ _ L K₁ T s hL _ hdata hq hK =>
    hn_std_row hmult inp.outer_cent L K₁ T s hL hdata hq hK
  four_a := fourAFacts_of_lamProfile False 2 4 le_rfl
    (fun G _ _ L K₁ N₀ T s hL _ hdata hq hK hcan =>
      hn_hautC hmult inp.outer_cent L K₁ N₀ T s hL hdata hq hK hcan)
    (fun K₂ _ _ hperf ⟨X, _, hX, ⟨e⟩⟩ => by
      obtain ⟨e₀⟩ := (isKHN_data hX).2.2.1
      exact hs_cover_fixed inp.hs_fix False hperf ⟨e.trans e₀⟩)
    (fun G _ _ K₁ N₀ hq hK hcan => hn_hsec K₁ N₀ hq hK hcan)


end HNRowFacts

end CFSG.EvenSporadicStandard.Induction
