module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicEndgame
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.RuIso

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Ru

open Subgroup CFSG.Open CFSG.Sporadic.RuSchreier CFSG.ComponentClassification.RankTwoSporadic

@[expose] def RuCentralTwoGroupOrderBound : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Assembly.IsQuasisimple L →
    IsPGroup 2 (center L) → Blueprint.NativeSporadic.IsSporadic (L ⧸ center L) .Ru →
      Nat.card (center L) ≤ 2

@[expose] def RuDoubleCoverTwoBLift : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Assembly.IsQuasisimple L → ∀ t : L, orderOf t = 2 →
    center L = zpowers t → ∀ π : L →* ↥ruP, Function.Surjective π → π.ker = zpowers t →
      ∀ v : L, orderOf (π v) = 2 → (∀ p, ((π v : ↥ruP) : Equiv.Perm (Fin 4060)) p ≠ p) →
        v ^ 2 = t

theorem odd_card_center
    (hM : RuCentralTwoGroupOrderBound)
    (hW : RuDoubleCoverTwoBLift) (h32 : AS76b.Lemma32) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (hA : AS76b.Hyp31 A)
    (e : ↥A ⧸ center ↥A ≃* Blueprint.NativeSporadic.Carrier .Ru)
    {ψ : normalizer (A : Set G) →* ↥ruP} (hψ : IsActionHom A (ruP.subgroupOf ruP) ψ)
    {t : normalizer (A : Set G)} (ht2 : (t : G) ^ 2 = 1) (htX : ψ t ∈ ruP.subgroupOf ruP)
    (hfpf : ∀ p, ((ψ t : ↥ruP) : Equiv.Perm (Fin 4060)) p ≠ p) :
    Odd (Nat.card (center ↥A)) := by
  have hsimp : IsSimpleGroup (↥A ⧸ center ↥A) :=
    @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_ruP (e.trans ruEquivP)
  have hprime : ¬ (Nat.card (↥A ⧸ center ↥A)).Prime := by
    rw [Nat.card_congr (e.trans ruEquivP).toEquiv, card_ruP']
    norm_num
  refine Endgame.odd_card_center_of_lift h32 hA le_rfl hψ hsimp hprime ?_
    (Q := fun σ => ∀ p, σ p ≠ p) hW ?_ ht2 htX hfpf
  · intro L _ _ hLq hL2 ⟨eL⟩
    exact hM L hLq hL2 ⟨eL.trans e⟩
  · intro h
    exact h 0 rfl

end CFSG.ComponentClassification.RankTwoSporadic.Ru
