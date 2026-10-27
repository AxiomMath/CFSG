module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarNotL227
public import CFSG.CGT.Foote82.T66.Proof511One
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixBridge
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarL227
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixNineTenOne
import CFSG.Blueprint.LieModelAPI
import CFSG.RankThree.PartTwo.Sec15.F153L3C2Quot

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private theorem center_eq_bot_of_kbar_psp43
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hCov : CFSG.CGT.Foote82.Proof511.PSp43Cover)
    (hS : LieModel (kbarQuot p M H) .PSp 2 3 1) :
    Subgroup.center (modTwoCore (kSub p M H)) = ⊥ := by
  have hO : CFSG.pCore 2 (modTwoCore (kSub p M H)) = ⊥ :=
    CFSG.RankThree.PartTwo.Sec15.F153L3C2.quot_pCore_two_eq_bot (kSub p M H)
  have hodd : Odd (Nat.card (Subgroup.center (modTwoCore (kSub p M H)))) :=
    CFSG.RankThree.PartTwo.Sec15.F153L3C2.odd_card_center_of_pCore_eq_bot hO
  exact hCov (modTwoCore (kSub p M H)) hK.2.2.1 hodd hS

theorem TwelveSixKCtx.kbar_type
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (hA : ¬ pLayerIn p H ≤ M)
    (hS : TwelveSixKbarSingle) (hList : TwelveSixKbarList)
    (hEx : TwelveSixKbarExclusion)
    (hCov : CFSG.CGT.Foote82.Proof511.PSp43Cover) :
    p = 3 ∧ IsTwoPrimeComponentIn (kSub p M H) H ∧
      (LieModel (modTwoCore (kSub p M H)) .PSp 2 3 1 ∨
        Nonempty (modTwoCore (kSub p M H) ≃* alternatingGroup (Fin 9))) := by
  obtain ⟨hXM, hHK, hKH⟩ := hc.nineTenOne_i D hA
  have hyp : TwelveSixKbarHyp G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ :=
    ⟨hc, ⟨D⟩, hsyl, hA, hXM, hHK, hKH⟩
  have hK : IsTwoPrimeComponentIn (kSub p M H) H :=
    hS G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ hyp
  rcases hList G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ hyp hK with ⟨hp, htypes⟩ | ⟨-, hA10⟩
  · refine ⟨hp, hK, ?_⟩
    rcases htypes with hL27 | hPSp | hSp6 | hA9 | hA10 | hA11
    · exact (hc.false_of_kbar_l227 D hKH hK kFactL227AutE27_holds hL27).elim
    · exact Or.inl (LieModel.of_quotient_center
        (center_eq_bot_of_kbar_psp43 hK hCov hPSp) hPSp)
    · exact (hEx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ hyp hK (Or.inl hSp6)).elim
    · exact Or.inr (nonempty_alt9_of_quot_center hK.2.2.1 hA9)
    · exact (hEx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ hyp hK (Or.inr (Or.inl hA10))).elim
    · exact (hEx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ hyp hK (Or.inr (Or.inr hA11))).elim
  · exact (hEx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ hyp hK (Or.inr (Or.inl hA10))).elim

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
