module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

@[expose] def GlaubermanSylowFixedSolvable : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → Even (Nat.card X) →
    ∀ (S : Sylow 2 X) (A : Subgroup (MulAut X)),
      (∀ α ∈ A, ∀ s ∈ (S : Subgroup X), α s = s) → Group.IsSolvable A

@[expose] def GlaubermanSimplePerfect : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → Even (Nat.card X) →
    ∀ (S : Sylow 2 X) (K : Subgroup (MulAut X)), Group.IsPerfect K →
      (∀ α ∈ K, ∀ s ∈ (S : Subgroup X), α s = s) → K = ⊥

theorem glaubermanSimplePerfect_of_sylowFixedSolvable (h : GlaubermanSylowFixedSolvable) :
    GlaubermanSimplePerfect := by
  intro X _ _ hX heven S K hK hfix
  have hsolv := h X hX heven S K hfix
  by_contra hne
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  exact Group.IsPerfect.not_isSolvable _ hsolv

end CFSG.ComponentClassification.AschbacherToolkit
