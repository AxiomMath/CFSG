module

public import CFSG.LargeExtraspecial.DW2AOutOrth
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.LargeExtraspecial.DW2AOutInput

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.OuterAutomorphisms

theorem dw2Out_clauseO :
    ∀ (X : Type) [Group X] [Finite X], NativeSporadic.IsSporadic X .J2 → IsPGroup 2 (Outer X) := by
  intro X _ _ h
  obtain ⟨e⟩ := h
  refine isPGroup_outer_of_mulEquiv e (isPGroup_of_card_dvd_two ?_)
  change Nat.card (Outer NativeSporadic.J2) ∣ 2
  have : Finite NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.1
  have : Finite (MulAut NativeSporadic.J2) :=
    Finite.of_injective (fun α : MulAut NativeSporadic.J2 => (α : NativeSporadic.J2 → _))
      DFunLike.coe_injective
  have : Finite (Outer NativeSporadic.J2) := Finite.of_surjective _ QuotientGroup.mk_surjective
  have hpos : 0 < Nat.card (Outer NativeSporadic.J2) := Nat.card_pos
  have hle := CFSG.Sporadic.Schreier.AT_J2_Schreier.1
  interval_cases Nat.card (Outer NativeSporadic.J2) <;> norm_num

@[expose] def DW2FieldInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ), 2 ≤ f →
    ((t = .PSL ∧ 3 ≤ n) ∨ (t = .PSp ∧ 3 ≤ n) ∨
      ((t = .POmegaPlus ∨ t = .POmegaMinus) ∧ 4 ≤ n) ∨
      (n = 0 ∧ t ∈ ({.G2, .trialityD4, .F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag))) →
    LieModel X t n 2 f → ∀ D : Set X, ¬ IsTransClass34 D

end CFSG.LargeExtraspecial.DW
