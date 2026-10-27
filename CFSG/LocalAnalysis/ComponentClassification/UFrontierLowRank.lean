module

public import CFSG.LocalAnalysis.ComponentClassification.UFrontierCoreBranches
public import CFSG.Walter.TwoRank
public import CFSG.Milestones.LR_rank_two_isomorphism_types

public section

namespace CFSG.ComponentClassification.UFrontier

open CFSG.Assembly CFSG.Blueprint

theorem lowTwoRankCatalogInput_of_rankTwo (h : type_of%
    @CFSG.Milestones.lr_rank_two_isomorphism_types) : LowTwoRankCatalogInput := by
  intro G _ _ _ hnonab heven hrank
  have h2 : Open.twoRank G = 2 :=
    le_antisymm hrank (CFSG.Walter.two_le_twoRank G hnonab heven)
  rcases h G hnonab h2 with ⟨p, f, -, -, -, hm⟩ | ⟨p, f, -, -, -, hm⟩ | ⟨p, f, -, -, -, hm⟩ | hm |
      he | hM
  · exact lieModel_catalog G .PSL 2 p f (.inl ⟨by decide, hm⟩)
  · exact lieModel_catalog G .PSL 3 p f (.inl ⟨by decide, hm⟩)
  · exact lieModel_catalog G .PSU 3 p f (.inl ⟨by decide, hm⟩)
  · exact lieModel_catalog G .PSU 3 2 2 (.inl ⟨by decide, hm⟩)
  · exact .inr (.inl ⟨7, by norm_num, he⟩)
  · obtain ⟨e⟩ := hM
    exact .inr (.inr (.inr (.inr ⟨.M11, ⟨e.trans (MulEquiv.subgroupCongr
      CFSG.Semidihedral.GL2Recognition.lowTwoRankStatedM11_eq_nativeM11)⟩⟩)))

theorem lowTwoRankCatalogInput : LowTwoRankCatalogInput :=
  lowTwoRankCatalogInput_of_rankTwo @CFSG.Milestones.lr_rank_two_isomorphism_types

end CFSG.ComponentClassification.UFrontier
