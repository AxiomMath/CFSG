module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Reach
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverE8Rank

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.Assembly.LowTwoRank

structure RuHyp31Inputs : Prop where
  thm54 : Sol78Thm54ReachHered
  suzuki : RuSuzukiModel
  family : RuFamilyFacts
  normalizer : RuNormalizerFacts
  szCover : SzCoverFacts
  even : EvenCoverExclHered .Ru

section RuRowFacts

theorem ruReachRow (hf : RuLocalFacts) (inp : RuHyp31Inputs) :
    ReachRow IsKRu [.Ru] [] [] RuKnown where
  iso := fun X Y _ _ e h => h.imp (fun ⟨f⟩ => ⟨e.symm.trans f⟩)
    (fun ⟨hT, h29⟩ => ⟨thm54Types_of_mulEquiv e hT,
      fun hd => h29 (by rw [Nat.card_congr e.toEquiv]; exact hd)⟩)
  fi23 := fun s hs => by
    rcases List.mem_append.1 hs with h | h
    · rcases List.mem_singleton.1 h with rfl
      exact ru_fi23
    · exact absurd h List.not_mem_nil
  fi23_lo := fun s hs => absurd hs List.not_mem_nil
  K_reach := fun X _ h => Or.inr ⟨(isKRu_known hf inp.suzuki h).1, by
    rw [(isKRu_known hf inp.suzuki h).2]
    norm_num⟩
  K_quot := fun X _ h => isKPinned_isoInv .Ru _ X (X ⧸ CFSG.oddCore X)
    (quotientOddCoreEquiv (isKRu_oddCore hf inp.suzuki h)).symm h
  K_not_sporadic := fun X _ h s hs => by
    rcases List.mem_append.1 hs with h' | h'
    · rcases List.mem_singleton.1 h' with rfl
      intro hX
      have h1 := (isKRu_known hf inp.suzuki h).2
      have h2 := ru_pinned_card _ hX
      omega
    · exact absurd h' List.not_mem_nil
  K_odd_lo := fun X _ _ _ s hs => absurd hs List.not_mem_nil
  lo := Or.inl fun s hs => absurd hs List.not_mem_nil
  K_iso := fun X Y _ _ hX hY _ _ => isKRu_iso hf inp.suzuki hX hY
  K_cq := fun X Y _ _ hX hY => by
    obtain ⟨e⟩ := isKRu_iso hf inp.suzuki hX hY
    exact ⟨quotientCenterEquiv' e⟩
  not_exc := fun X _ h => h.elim (fun hRu => ru_sp_not_exc X hRu)
    (fun ⟨hT, _⟩ => inp.family.not_exc X hT)
  sp_not_exc := fun s hs => by
    rcases List.mem_append.1 hs with h | h
    · rcases List.mem_singleton.1 h with rfl
      exact ru_sp_not_exc
    · exact absurd h List.not_mem_nil
  rank := fun X _ _ hq hR _ => by
    rcases hR with hRu | ⟨hT, _⟩
    · obtain ⟨e⟩ := hRu
      exact three_le_pRank_ru_cover e
    · exact inp.family.cover_rank X hq hT
  up_reach := fun s hs => absurd hs List.not_mem_nil
  closure := fun Y _ _ hY N' hN hidx hkp P hP hPq hR hns _ _ _ =>
    ru_closure (inp.thm54 Y hY) hN hidx hkp hP hPq hR (fun h => hns ⟨.Ru, by simp, h⟩)
  notR := fun Y _ _ N hN hidx _ ⟨L, hL, s, hs, hcov⟩ hR => by
    rcases List.mem_singleton.1 hs with rfl
    exact ru_notR hN hidx hL hcov hR
  pair_into := fun Y _ _ hY N' hN hidx hkp P hP hPq hR hns _ _ ⟨s, hs, hN'⟩ => by
    rcases List.mem_singleton.1 hs with rfl
    exact ru_pair_into (inp.thm54 Y hY) hf inp.suzuki hN hidx hkp hP hPq hR
      (fun h => hns ⟨.Ru, by simp, h⟩) hN'

end RuRowFacts

end CFSG.EvenSporadicStandard.Induction
