module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Inputs

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

@[expose] def IsGomiNatural (L : Subgroup (MulAut W)) (I Z : Subgroup W) : Prop :=
  (∃ a : ℕ, 1 ≤ a ∧ BinaryNaturalSL L I Z 3 a) ∨ (∃ a : ℕ, 2 ≤ a ∧ BinaryNaturalSp4 L I Z a) ∨
    AlternatingNatural L I Z 6 ∨ TripleA6Six L I Z

@[expose] def GomiFact36Identification : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (L A : Subgroup (MulAut W)) (I Z : Subgroup W), IsGomiChevTwo ↥L →
      (IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiSp4 (↥L ⧸ Subgroup.center ↥L)) →
      A ≤ Subgroup.normalizer (L : Set (MulAut W)) → A ≤ stabSub I → A ≤ stabSub Z →
      IsGomiNoncentralFactor L I Z → L ⊓ centSec I Z = ⊥ → ¬ A ≤ centSec I Z →
      IsElemAbelian2 (autSec A I Z) → IsQuadratic (autSec A I Z) →
      Nat.card (Sec I Z) ≤ Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)) →
      IsGomiNatural L I Z

@[expose] def GomiFact36Homogeneity : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (L A : Subgroup (MulAut W)) (I Z I' Z' : Subgroup W), IsGomiChevTwo ↥L →
      (IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiSp4 (↥L ⧸ Subgroup.center ↥L)) →
      A ≤ Subgroup.normalizer (L : Set (MulAut W)) →
      A ≤ stabSub I → A ≤ stabSub Z → A ≤ stabSub I' → A ≤ stabSub Z' →
      IsGomiNoncentralFactor L I Z → IsGomiNoncentralFactor L I' Z' →
      IsGomiNatural L I Z → IsGomiNatural L I' Z' →
      ¬ A ≤ centSec I Z → A ⊓ centSec I Z = A ⊓ centSec I' Z' →
      IsElemAbelian2 (autSec A I Z) → IsQuadratic (autSec A I Z) → IsQuadratic (autSec A I' Z') →
      Nat.card (Sec I Z) * Nat.card (Sec I' Z') ≤
        Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)) *
          Nat.card ↥(fixV (autSec A I' Z')) →
      SecIsoL L I Z I' Z'

@[expose] def GomiFact36Faithful : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y S L A : Subgroup (MulAut W), GomiFact36Hyp Y S L → A ≤ S →
      A ≤ Subgroup.normalizer (L : Set (MulAut W)) → IsElemAbelian2 A → IsQuadratic A →
      ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)) →
      (∀ U : Subgroup W,
        Nat.card U * Nat.card ↥(A ⊓ centSec U ⊥) ≤ Nat.card A * Nat.card ↥(fixV A ⊓ U)) →
      ∀ I Z : Subgroup W, I ≤ G6.submoduleClosure L (fixV S) → A ≤ stabSub I → A ≤ stabSub Z →
        IsGomiNoncentralFactor L I Z → L ⊓ centSec I Z = ⊥

end CFSG.GroupTheory
