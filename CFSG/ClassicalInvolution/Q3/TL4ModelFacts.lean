module

public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint

structure EdgelessMember3 {X : Type} [Group X] (R : Subgroup X) (S : Sylow 2 R) (z : X) :
    Prop where
  datum : TightDatum R S z
  cls : TightClsR 3 X R S z
  edgeless : TightEdgeless R

@[expose] def MuZ2Member {X : Type} [Group X] (R : Subgroup X) : Prop :=
  ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
    MuIsoZ2 (CoreAssembly.conjClass (tightCore R)) W

@[expose] def MuS3Member {X : Type} [Group X] (R : Subgroup X) : Prop :=
  ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
    MuIsoS3 (CoreAssembly.conjClass (tightCore R)) W

@[expose] def Concl163 {X : Type} [Group X] (R : Subgroup X) (z : X) : Prop :=
  ∀ β : MulAut X, β * β = 1 → (∀ x ∈ tightCore R, β x = x) → β = 1 ∨ β = MulAut.conj z

@[expose] def Concl164 {X : Type} [Group X] (R : Subgroup X) (z : X) : Prop :=
  ∀ U : Subgroup X, U ≤ R → IsCyclic ↥U → Nat.card ↥U = 4 → ∀ β γ : MulAut X,
    (∀ x ∈ U, γ x = x) → β = γ * γ → β * β = 1 → β = 1 ∨ β = MulAut.conj z

@[expose] def Model163L2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → IsSimpleGroup ↥(genFittingFStar X) →
      (genFittingFStar X).index ≤ 2 → ∀ p f : ℕ, p.Prime → p ≠ 2 → Even f →
        LieModel (FStarQuot X) .PSL 2 p f → Concl163 R z

@[expose] def Model163L3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → IsSimpleGroup ↥(genFittingFStar X) →
      (genFittingFStar X).index ∣ 6 → MuS3Member R → ¬ TightActs3 R z →
        ∀ p f : ℕ, p.Prime → p ≠ 2 → LieModel (FStarQuot X) .PSL 3 p f → Concl163 R z

@[expose] def Model163U3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → IsSimpleGroup ↥(genFittingFStar X) →
      (genFittingFStar X).index ∣ 6 → MuS3Member R → ¬ TightActs3 R z →
        ∀ p f : ℕ, p.Prime → p ≠ 2 → LieModel (FStarQuot X) .PSU 3 p f → Concl163 R z

@[expose] def Model163M12 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → NativeSporadic.IsSporadic X .M12 → Concl163 R z

@[expose] def Model163 : Prop :=
  Model163L2 ∧ Model163L3 ∧ Model163U3 ∧ Model163M12

@[expose] def ModelM12Acts3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → IsSimpleGroup ↥(genFittingFStar X) →
      (genFittingFStar X).index ≤ 2 → NativeSporadic.IsSporadic (FStarQuot X) .M12 →
        TightActs3 R z

@[expose] def Model164L2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → MuZ2Member R → IsSimpleGroup ↥(genFittingFStar X) →
      (genFittingFStar X).index ≤ 2 → ∀ p f : ℕ, p.Prime → p ≠ 2 → Even f →
        LieModel (FStarQuot X) .PSL 2 p f → Concl164 R z

@[expose] def Model164M11 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → MuZ2Member R → NativeSporadic.IsSporadic X .M11 → Concl164 R z

@[expose] def Model164L3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → MuZ2Member R → IsSimpleGroup X →
      ∀ p f : ℕ, p.Prime → p ≠ 2 → LieModel X .PSL 3 p f → Concl164 R z

@[expose] def Model164U3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → MuZ2Member R → IsSimpleGroup X →
      ∀ p f : ℕ, p.Prime → p ≠ 2 → p ^ f % 4 = 1 → LieModel X .PSU 3 p f → Concl164 R z

@[expose] def Model164 : Prop :=
  Model164L2 ∧ Model164M11 ∧ Model164L3 ∧ Model164U3

@[expose] def MuZ2Table : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → MuZ2Member R → IsSimpleGroup ↥(genFittingFStar X) →
      (genFittingFStar X).index ∣ 6 →
        (∀ p f : ℕ, LieModel (FStarQuot X) .PSL 3 p f →
          IsSimpleGroup X ∧ LieModel X .PSL 3 p f) ∧
        (∀ p f : ℕ, LieModel (FStarQuot X) .PSU 3 p f →
          IsSimpleGroup X ∧ LieModel X .PSU 3 p f ∧ p ^ f % 4 = 1) ∧
        (∀ p f : ℕ, ¬ LieModel (FStarQuot X) .G2 0 p f) ∧
        (∀ p f : ℕ, ¬ LieModel (FStarQuot X) .trialityD4 0 p f) ∧
        ¬ NativeSporadic.IsSporadic (FStarQuot X) .M12

theorem concl163_of_e3a (h : Model163) (hM : ModelM12Acts3) {X : Type} [Group X] [Finite X]
    {R : Subgroup X} {S : Sylow 2 R} {z : X} (hm : EdgelessMember3 R S z)
    (hs : IsSimpleGroup ↥(genFittingFStar X)) (hμ : MuS3Member R) (h3 : ¬ TightActs3 R z)
    (hX : Thm6Exit X) : Concl163 R z := by
  obtain ⟨hL2, hL3, hU3, -⟩ := h
  obtain ⟨p, f, hp, hp2, ⟨hf, hl, hi⟩ | ⟨hl | hl, hi6⟩⟩ | ⟨hm12, hi⟩ := hX
  · exact hL2 X R S z hm hs hi p f hp hp2 hf hl
  · exact hL3 X R S z hm hs hi6 hμ h3 p f hp hp2 hl
  · exact hU3 X R S z hm hs hi6 hμ h3 p f hp hp2 hl
  · exact absurd (hM X R S z hm hs hi hm12) h3

end CFSG.ClassicalInvolution.Q3.TL4
