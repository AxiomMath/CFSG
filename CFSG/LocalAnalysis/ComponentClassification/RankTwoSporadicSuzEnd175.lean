module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEndK
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.SuzOddCore.SmallChain

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Suz

open Subgroup CFSG.Open CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.RankTwoSporadic

@[expose] def SuzCentralTwoGroupOrderBound : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Assembly.IsQuasisimple L →
    IsPGroup 2 (center L) → Blueprint.NativeSporadic.IsSporadic (L ⧸ center L) .Suz →
      Nat.card (center L) ≤ 2

@[expose] def SuzDoubleCoverTwoBLift : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Assembly.IsQuasisimple L → ∀ t : L, orderOf t = 2 →
    center L = zpowers t → ∀ π : L →* ↥suzM, Function.Surjective π → π.ker = zpowers t →
      ∀ v : L, orderOf (π v) = 2 → fix1782 ((π v : ↥suzM) : Equiv.Perm (Fin 1782)) = 42 →
        v ^ 2 = t

theorem odd_card_center (hM : SuzCentralTwoGroupOrderBound)
    (hW : SuzDoubleCoverTwoBLift) (h32 : AS76b.Lemma32) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (hA : AS76b.Hyp31 A)
    (e : ↥A ⧸ center ↥A ≃* Blueprint.NativeSporadic.Carrier .Suz)
    {ψ : normalizer (A : Set G) →* ↥suzT} (hψ : IsActionHom A (suzM.subgroupOf suzT) ψ)
    {t : normalizer (A : Set G)} (ht2 : (t : G) ^ 2 = 1) (htX : ψ t ∈ suzM.subgroupOf suzT)
    (hfix : fix1782 ((ψ t : ↥suzT) : Equiv.Perm (Fin 1782)) = 42) :
    Odd (Nat.card (center ↥A)) := by
  have hsimp : IsSimpleGroup (↥A ⧸ center ↥A) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Suz.isSimpleGroup_Suz e
  have hprime : ¬ (Nat.card (↥A ⧸ center ↥A)).Prime := by
    rw [Nat.card_congr e.toEquiv]
    change ¬ (Nat.card Blueprint.NativeSporadic.Suz).Prime
    rw [CFSG.Sporadic.Suz.card_Suz]
    norm_num
  refine Endgame.odd_card_center_of_lift h32 hA suzM_le_suzT hψ hsimp hprime ?_
    (Q := fun σ => fix1782 σ = 42) hW ?_ ht2 htX hfix
  · intro L _ _ hLq hL2 ⟨eL⟩
    exact hM L hLq hL2 ⟨eL.trans e⟩
  · have h1 : fix1782 (1 : Equiv.Perm (Fin 1782)) = 1782 := by simp [fix1782]
    omega

end CFSG.ComponentClassification.RankTwoSporadic.Suz
