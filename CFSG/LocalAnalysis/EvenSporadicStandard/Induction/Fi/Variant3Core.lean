module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.CanLoc
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Embed
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35HLambda

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.EvenSporadicStandard.Solomon78

structure CanLocSpec (H : Type) [Group H] (IsK : GroupClass)
    (CL : Subgroup H → Subgroup H → Prop) : Prop where
  le : ∀ K₁ N₀ : Subgroup H, CL K₁ N₀ → N₀ ≤ K₁
  isTwoLocalIn : ∀ K₁ N₀ : Subgroup H, CL K₁ N₀ → IsTwoLocalIn N₀ K₁
  map : ∀ (e : H ≃* H) (K₁ N₀ : Subgroup H), CL K₁ N₀ →
    CL (K₁.map e.toMonoidHom) (N₀.map e.toMonoidHom)
  exists_loc : ∀ K₁ : Subgroup H, CFSG.IsQuasisimple ↥K₁ → IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁) →
    ∃ N₀ : Subgroup H, CL K₁ N₀

structure Hyp31FourAL (H : Type) [Group H] [Finite H] (N : Subgroup H) (IsK IsL : GroupClass)
    (CL : Subgroup H → Subgroup H → Prop) : Prop where
  four_a : ∀ K₁ L₁ : Subgroup H, InL K₁ → Maximal L₁ → IsL ↥L₁ → Lt K₁ L₁ → K₁ ≤ L₁ →
    IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁) → ∀ N₀ : Subgroup H, CL K₁ N₀ →
      ¬ IsSectionOf ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))) ↥(lam L₁ N₀) ∧
      ∀ (K₂ : Type) [Group K₂] [Finite K₂], Group.IsPerfect K₂ →
        Nonempty ((K₂ ⧸ center K₂) ≃* (↥K₁ ⧸ center ↥K₁)) → NoFixedEmbeds K₂ ↥(lam L₁ N₀)

end CFSG.EvenSporadicStandard.Induction.Fi.V3
