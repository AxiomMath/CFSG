module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicEndgame
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverLift
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverDisplacement
public import CFSG.Sporadic.J2

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J2End

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.J2Cover

theorem odd_card_center
    (h32 : AS76b.Lemma32) {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : AS76b.Hyp31 A) (e : ↥A ⧸ center ↥A ≃* Blueprint.NativeSporadic.Carrier .J2)
    {ψ : normalizer (A : Set G) →* ↥R} (hψ : IsActionHom A (P.subgroupOf R) ψ)
    {t : normalizer (A : Set G)} (ht2 : (t : G) ^ 2 = 1) (htX : ψ t ∈ P.subgroupOf R)
    (hfix : Models.fixCount ((ψ t : ↥R) : Equiv.Perm (Fin 315)) = 15) :
    Odd (Nat.card (center ↥A)) := by
  have hsimp : IsSimpleGroup (↥A ⧸ center ↥A) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e
  have hprime : ¬ (Nat.card (↥A ⧸ center ↥A)).Prime := by
    rw [Nat.card_congr e.toEquiv]
    change ¬ (Nat.card Blueprint.NativeSporadic.J2).Prime
    rw [CFSG.Sporadic.J2.card_J2]
    norm_num
  refine Endgame.odd_card_center_of_lift h32 hA P_le_R hψ hsimp hprime ?_
    (Q := fun σ => Models.fixCount σ = 15) ?_ ?_ ht2 htX hfix
  · intro L _ _ hLq hL2 ⟨eL⟩
    exact StandardRecognition.m12J2CentralTwoGroupOrderBound L hLq hL2 (Or.inr ⟨eL.trans e⟩)
  · intro L _ _ hLq t₀ ht₀ hZ π hπ hker v hv hQ
    exact ((j2_double_cover_involution_lift_orders_fixCount hLq ht₀ hZ π hπ hker).2.2 v hv hQ).1
  · change ¬ Models.fixCount 1 = 15
    have h315 : Models.fixCount (1 : Equiv.Perm (Fin 315)) = 315 := by
      simp [Models.fixCount]
    omega

end CFSG.ComponentClassification.RankTwoSporadic.J2End
