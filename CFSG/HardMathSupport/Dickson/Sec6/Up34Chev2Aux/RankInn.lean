module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Rank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcThreeSplit
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ExcPlaneG2Three

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Solomon.Coordinator

theorem up34C2Inn_of_rank {F : TauCeti.LieTypeIndex → Prop}
    (hrank : ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), F d.1 →
      IsCharTwoLieIndex d.1 → Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → RankLE2 3 S) :
    Up34Chev2Inn F := by
  intro S _ _ hs hnab d hd hc he x hx
  haveI := hs
  obtain ⟨E, hE, hlt⟩ := hx.exists_elemAbelian_gt_nine (up34_center_eq_bot_of_simple hnab)
  have := hrank S d hd hc he E hE
  omega


theorem up34C2Inn_g2 : Up34Chev2Inn FamG2 := by
  refine up34C2Inn_of_rank fun S _ _ ⟨d, hv⟩ hF hc ⟨e⟩ => ?_
  cases d with
  | G2 q =>
    have h3 : 3 ≠ q.p := by
      have : q.p = 2 := hc
      omega
    exact RankLE2.of_mulEquiv e.symm (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_cat_G2 q hv h3)
  | _ => exact hF.elim

theorem up34C2Inn_triD4 : Up34Chev2Inn FamTriD4 := by
  refine up34C2Inn_of_rank fun S _ _ ⟨d, hv⟩ hF hc ⟨e⟩ => ?_
  cases d with
  | trialityD4 q =>
    have h3 : q.p ≠ 3 := by
      have : q.p = 2 := hc
      omega
    exact RankLE2.of_mulEquiv e.symm (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hv h3)
  | _ => exact hF.elim

theorem up34C2Inn_reeF4 : Up34Chev2Inn FamReeF4 := by
  refine up34C2Inn_of_rank fun S _ _ ⟨d, hv⟩ hF hc ⟨e⟩ => ?_
  cases d with
  | reeF4 m => exact RankLE2.of_mulEquiv e.symm (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_reeF4 hv)
  | _ => exact hF.elim

end CFSG.HardMathSupport.Dickson.Sec6
