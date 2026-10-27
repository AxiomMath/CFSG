module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.RowA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.RowB

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def IsU62 : GroupClass := fun X _ => Nonempty (X ≃* (Fi22D ⧸ center Fi22D))

theorem isU62_isoInv : GroupClass.IsoInv IsU62 := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩

@[expose] def Fi22CoversFixesElem : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Group.IsPerfect K → IsSporadic (K ⧸ center K) .Fi22 →
    InvolutionFixesElem K 16

@[expose] def U62CoversFixesElem : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Group.IsPerfect K → IsU62 (K ⧸ center K) →
    InvolutionFixesElem K 16

section Even

@[expose] def Fi22EvenCover : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic (X ⧸ center X) .Fi22 →
    Even (Nat.card (center X)) → Nonempty ((X ⧸ CFSG.oddCore X) ≃* Fi23D)

end Even

@[expose] def Fi22U62Sub : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N' P : Subgroup Y), N'.Normal → centralizer (N' : Set Y) ≤ N' →
    IsSporadic ↥N' .Fi22 → P ≤ N' → (∃ t : Y, orderOf t = 2 ∧ P ≤ centralizer ({t} : Set Y)) →
    CFSG.IsQuasisimple ↥P → IsU62 (↥P ⧸ center ↥P) → Nonempty ((↥P ⧸ CFSG.oddCore ↥P) ≃* Fi22D)

@[expose] def U62OddExclAt (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ (N' : Subgroup Y), FStarSimple N' → N'.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y → ∀ P : Subgroup Y, SolStd P →
      CFSG.IsQuasisimple ↥P → IsU62 (↥P ⧸ center ↥P) → Odd (Nat.card ↥(center ↥P)) →
        (∃ (Q₀ : Type) (_ : Group Q₀), CFSG.IsQuasisimple Q₀ ∧ Even (Nat.card (center Q₀)) ∧
          Nonempty ((Q₀ ⧸ center Q₀) ≃* ↥N')) → False

@[expose] def U62OddExclHered : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Balance.UHered Y → U62OddExclAt Y

section Atlas

structure FiAtlas : Prop where
  fi22Covers : Fi22CoversFixesElem
  u62Covers : U62CoversFixesElem
  fi22Even : Fi22EvenCover
  fi22U62 : Fi22U62Sub
  u62Odd : U62OddExclHered

end Atlas

end CFSG.EvenSporadicStandard.Induction.Fi
