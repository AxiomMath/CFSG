module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Lemma39

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

@[expose] def Fi24InPair (Y : Type) [Group Y] (uY : Y) (KY : Subgroup Y) : Prop :=
  orderOf uY = 2 ∧ (∀ k ∈ KY, k * uY = uY * k) ∧ ⁅KY, KY⁆ = KY ∧
    2 * 64561751654400 ≤ Nat.card KY

@[expose] def Fi24InPairs : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSporadic Y .Fi24Prime → ∀ (uY : Y) (KY : Subgroup Y),
    Fi24InPair Y uY KY → (vPairs (⊤ : Subgroup Y) KY uY).Nonempty

@[expose] def Fi24InGenerate : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSporadic Y .Fi24Prime → ∀ (uY : Y) (KY : Subgroup Y),
    Fi24InPair Y uY KY → Sol78Generate (⊤ : Subgroup Y) KY uY

@[expose] def Fi24InFixesElem : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H), OddCover .Fi24Prime L →
    fiLoc (2 * 64561751654400) H L K u → InvolutionFixesElem ↥K 16

end CFSG.EvenSporadicStandard.Induction
