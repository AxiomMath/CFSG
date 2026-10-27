module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LInputs

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

@[expose] def Fi23BalanceAt (H : Type) [Group H] [Finite H] : Prop :=
  ∀ (N L : Subgroup H), FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → SolStd L → OddCover .Fi23 L →
      (∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2) →
        ∀ t : H, t ∈ centralizer (L : Set H) → orderOf t = 2 →
          centralizer (L : Set H) ⊓ centralizer ({t} : Set H) = zpowers t

@[expose] def Fi23BalanceHered : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → Fi23BalanceAt H

@[expose] def Fi23Claim612EAt (H : Type) [Group H] [Finite H] : Prop :=
  ∀ (N L K : Subgroup H) (t u : H), FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover .Fi23 L →
      SolomonGlobalQ H L K t u → fiIn23 H L K u → Fi23Transposition L u → NoBiggerFi H .Fi23 →
        (∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2) →
          ∀ a : H, a ∈ L → orderOf a = 2 → (¬ ∃ l ∈ L, a = l * u * l⁻¹) → ¬ IsConj t (t * a)

@[expose] def Fi23Claim612EHered : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → Fi23Claim612EAt H

@[expose] def Fi23TailAt (H : Type) [Group H] [Finite H] : Prop :=
  ∀ (N L K : Subgroup H) (t u : H), FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover .Fi23 L →
      SolomonGlobalQ H L K t u → fiIn23 H L K u →
        (∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2) → t ∉ N →
          IsSporadic ↥N .Fi24Prime

@[expose] def Fi23TailHered : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → Fi23TailAt H

end CFSG.EvenSporadicStandard.Induction
