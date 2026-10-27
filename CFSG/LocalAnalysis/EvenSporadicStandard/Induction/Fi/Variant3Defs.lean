module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.NoUp

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

structure Hyp31Core (H : Type) [Group H] [Finite H] (N : Subgroup H) (IsK IsL : GroupClass) :
    Prop where
  fstar : FStarSimple N
  index_le_two : N.index ≤ 2
  type_max : ∀ L₁ : Subgroup H, InL L₁ → IsL ↥L₁ →
    Maximal L₁ ∧ ∃ S : Sylow 2 (centralizer (L₁ : Set H)), IsCyclic ↥S
  not_max : ∀ K₁ : Subgroup H, InL K₁ → KLike IsK K₁ → ∀ G₁ : Subgroup H, N ≤ G₁ → G₁ ≠ ⊤ →
    ¬ (K₁ ≤ G₁ ∧ Maximal (K₁.subgroupOf G₁))
  desc : ∀ K₁ L₁ : Subgroup H, InL K₁ → KLike IsK K₁ → InL L₁ → ReflTransGen Lt K₁ L₁ →
    (∃ π : ↥L₁ →* ↥K₁, Function.Surjective π ∧ π.ker ≤ center ↥L₁) ∨
      (IsL ↥L₁ ∧ IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁))

structure Hyp31NS (H : Type) [Group H] [Finite H] (N : Subgroup H) (IsK IsL : GroupClass) :
    Prop extends Hyp31Row IsK IsL, Hyp31Core H N IsK IsL

@[expose] def CqEq (IsK : GroupClass) : Prop :=
  ∀ (X Y : Type) [Group X] [Group Y], IsK X → IsK Y →
    Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y))

@[expose] def IsKFi23 (X : Type) [Group X] : Prop :=
  Finite X ∧ CFSG.IsQuasisimple X ∧ IsSporadic (X ⧸ center X) .Fi23

@[expose] def Fi23SelfCentralizing : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G), OddCover .Fi24Prime L → K ≤ L →
    CFSG.IsQuasisimple ↥K → IsSporadic (↥K ⧸ center ↥K) .Fi23 →
      ∀ x ∈ L, (∀ k ∈ K, k * x = x * k) → ∀ l ∈ L, l * x = x * l

@[expose] def Fi23AutCentSolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G), OddCover .Fi24Prime L → K ≤ L →
    CFSG.IsQuasisimple ↥K → IsSporadic (↥K ⧸ center ↥K) .Fi23 →
      Group.IsSolvable ↥(autCentralizer L K)

@[expose] def Fi24OuterFixed : Prop :=
  ∀ (Y : Type) [Group Y], IsSporadic Y .Fi24Prime → ∀ ν : MulAut Y, ν * ν = 1 →
    (¬ ∃ g : Y, ν = MulAut.conj g) → ∀ B : Subgroup Y, B ≤ fixSubgroup ν → ⁅B, B⁆ = B →
      4089470473293004800 ≤ Nat.card B → B = fixSubgroup ν

@[expose] def Fi23Order : Prop :=
  Nat.card (Carrier .Fi23) = 4089470473293004800

@[expose] def FiOuterInvolution : Prop :=
  Sol78Lit → ∀ (H : Type) [Group H] [Finite H], BelowSec (Sol78PredS fiTypes) H →
    ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ¬ IsSporadic ↥N .Fi22 →
        ¬ IsSporadic ↥N .Fi23 → ¬ IsSporadic ↥N .Fi24Prime → NoBiggerFi H .Fi24Prime →
          (∃ L₀ : Subgroup H, SolStd L₀ ∧ OddCover .Fi24Prime L₀) →
            ∀ (K L T : Subgroup H) (s : H), K ≤ L → K ≠ L → CFSG.IsQuasisimple ↥K →
              IsSporadic (↥K ⧸ center ↥K) .Fi23 → OddCover .Fi24Prime L → SolStd L →
                Sol78Link5bData K L T s → T ≠ ⊥ → s ∉ L ⊔ centralizer (L : Set H) →
                  (∀ k ∈ K, k * s = s * k) → s ^ 2 ≠ 1 →
                    ∃ u t : H, orderOf u = 2 ∧ orderOf t = 2 ∧ t ∈ centralizer (L : Set H) ∧
                      u * t = t * u ∧ u ∈ normalizer (L : Set H) ∧
                      u ∉ L ⊔ centralizer (L : Set H) ∧ ∀ k ∈ K, k * u = u * k

structure FiV3Pinned : Prop where
  pinned : FiPinned
  order23 : Fi23Order
  selfCent : Fi23SelfCentralizing
  autSolv : Fi23AutCentSolvable
  outerFixed : Fi24OuterFixed

end CFSG.EvenSporadicStandard.Induction.Fi.V3
