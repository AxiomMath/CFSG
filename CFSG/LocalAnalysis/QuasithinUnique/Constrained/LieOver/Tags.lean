module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Inputs

public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def SylowProps (X : Type) [Group X] : Prop :=
  Bridge.Over.Overgroups X ∧ Bridge.SylowAutTrivial X

@[expose] def AsLieTwoAt (t : StatedLieTag) : Prop :=
  ∀ (n f : ℕ) (X : Type) [Group X] [Finite X], IsSimpleGroup X →
    StatedLieAdmissible t n 2 f → LieModel X t n 2 f → SylowProps X

@[expose] def AsLieTwoPSU33 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → IsPSU 3 3 1 X → SylowProps X

theorem asLieTwo_of_tags (h : ∀ t, AsLieTwoAt t) (hU : AsLieTwoPSU33) :
    AsLieTwoOvergroups ∧ AsLieTwoSylowAut := by
  have key : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsLieTypeTwoSimple S →
      SylowProps S := by
    intro S _ _ hS hL
    rcases hL with ⟨t, n, f, hadm, hmod⟩ | hU33
    · exact h t n f S hS hadm hmod
    · exact hU S hS hU33
  exact ⟨fun S _ _ hS hL => (key S hS hL).1, fun S _ _ hS hL => (key S hS hL).2⟩

theorem asLieTwoAt_pOmegaOdd : AsLieTwoAt .POmegaOdd := by
  intro n f X _ _ _ hadm _
  exact absurd rfl hadm.2.2.2

theorem asLieTwoAt_twistedG2 : AsLieTwoAt .twistedG2 := by
  intro n f X _ _ _ hadm _
  exact absurd hadm.2.2.2.1 (by norm_num)

@[expose] def AsLieTwoPSLGe4 : Prop :=
  ∀ (n f : ℕ) (X : Type) [Group X] [Finite X], 4 ≤ n → IsSimpleGroup X →
    StatedLieAdmissible .PSL n 2 f → LieModel X .PSL n 2 f → SylowProps X

@[expose] def AsLieTwoPSUGe4 : Prop :=
  ∀ (n f : ℕ) (X : Type) [Group X] [Finite X], 4 ≤ n → IsSimpleGroup X →
    StatedLieAdmissible .PSU n 2 f → LieModel X .PSU n 2 f → SylowProps X

@[expose] def AsLieTwoPSpGe3 : Prop :=
  ∀ (n f : ℕ) (X : Type) [Group X] [Finite X], 3 ≤ n → IsSimpleGroup X →
    StatedLieAdmissible .PSp n 2 f → LieModel X .PSp n 2 f → SylowProps X

end CFSG.Quasithin.LieOver
