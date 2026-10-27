module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Foote.Coordinator.SplitFrame


@[expose] def TwFrameClosing (τ : Tag) (K : Type) [Field K] (X : Subgroup (ModGL τ K)) : Prop :=
  ∀ H : Subgroup (ModGL τ K), H ≤ adjointGroup τ K → X ≤ H →
    ¬ H ≤ Subgroup.normalizer (X : Set (ModGL τ K)) → H = adjointGroup τ K

@[expose] def TwFrameNormalizerSolvable (τ : Tag) (K : Type) [Field K]
    (X : Subgroup (ModGL τ K)) : Prop :=
  ∀ P : Subgroup (ModGL τ K), P ≤ adjointGroup τ K →
    P ≤ Subgroup.normalizer (X : Set (ModGL τ K)) →
    Group.IsSolvable ↥(P ⊓ X) → Group.IsSolvable ↥P

theorem frameClosing_iff (τ : Tag) (K : Type) [Field K] (S : Set (Fin τ.rank → ℤ)) :
    FrameClosing τ K S ↔ TwFrameClosing τ K (rootSpan τ K S) :=
  Iff.rfl

theorem frameNormalizerSolvable_iff (τ : Tag) (K : Type) [Field K]
    (S : Set (Fin τ.rank → ℤ)) :
    FrameNormalizerSolvable τ K S ↔ TwFrameNormalizerSolvable τ K (rootSpan τ K S) :=
  Iff.rfl

@[expose] def TwThirdLine (τ : Tag) (K : Type) [Field K] (p : ℕ) : Prop :=
  ∀ E : Subgroup (adjointGroup τ K), Nat.card E = p ^ 2 → (∀ x ∈ E, x ^ p = 1) →
    ∀ a b : adjointGroup τ K, a ∈ E → b ∈ E → a ≠ 1 → b ≠ 1 →
      ∃ e ∈ E, e ∉ Subgroup.zpowers a ∧ e ∉ Subgroup.zpowers b ∧
        ∃ P : Subgroup (adjointGroup τ K),
          P ≤ Subgroup.centralizer ({e} : Set (adjointGroup τ K)) ∧ ¬ Group.IsSolvable ↥P

structure TwFramePlaneData (τ : Tag) (K : Type) [Field K] (X₁ X₂ : Subgroup (ModGL τ K))
    (p : ℕ) : Prop where
  inter : ¬ p ∣ Nat.card ↥(X₁ ⊓ X₂)
  card : (Nat.card ↥(adjointGroup τ K)).factorization p =
    (Nat.card ↥X₁).factorization p + (Nat.card ↥X₂).factorization p
  cyclic₁ : ∀ g : ↥X₁, orderOf g = p → IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥X₁))
  cyclic₂ : ∀ g : ↥X₂, orderOf g = p → IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥X₂))

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
