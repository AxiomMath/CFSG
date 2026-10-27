module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviResidualLattices
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviModels
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

set_option linter.unusedSectionVars false

@[expose] def ReeF4MinLevi : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid)
    (_ : Y ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.reeF4 m, hv⟩).Group), MinLevi Y


theorem residualLeviCase_of_reeF4 (hree : ReeF4MinLevi) : ResidualLeviCase := by
  intro Y _ _ L S₀ P hL hres hS hP
  refine leviAlt_of_minLevi hL hS hP ?_
  rcases hres with he | ⟨d, ⟨q, hq, hdq⟩, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · obtain ⟨e⟩ := he
    exact minLevi_alt_six e
  · obtain ⟨dd, hv⟩ := d
    simp only at hdq
    subst hdq
    obtain ⟨hp, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_three hq
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    rw [hp, hf] at h
    obtain ⟨e'⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, h⟩)
    exact minLevi_of_twoParSolv e' twoParSolv_u33
  · obtain ⟨dd, hv⟩ := d
    rcases hd with ⟨m, hm⟩ | ⟨m, hm⟩ | hm
    · simp only at hm
      subst hm
      exact minLevi_suzuki m hv e
    · simp only at hm
      subst hm
      exact hree _ m hv e
    · simp only at hm
      subst hm
      have hmodel := CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := ↥L ⧸ Subgroup.center ↥L)
        ⟨hv, ⟨e⟩⟩
      obtain ⟨e'⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hmodel
      exact minLevi_of_twoParSolv e' twoParSolv_tits

theorem kFactChevMinParabolicLevi_of_reeF4 (hree : ReeF4MinLevi) : KFactChevMinParabolicLevi :=
  kFactChevMinParabolicLevi_of_residual (residualLeviCase_of_reeF4 hree)

end CFSG.AGLEmbeddingD2.Tits.GN516
