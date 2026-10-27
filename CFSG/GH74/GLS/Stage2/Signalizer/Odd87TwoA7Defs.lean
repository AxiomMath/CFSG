module

public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS Subgroup

@[expose] def TwoA7Witness {F : Type*} [Group F] (J : Subgroup F) : Prop :=
  CFSG.Open.IsQuasisimple (J ⧸ CFSG.Open.classicalInvolutionOddCore J) ∧
    Nat.card (Subgroup.center (J ⧸ CFSG.Open.classicalInvolutionOddCore J)) = 2 ∧
    Nonempty ((J ⧸ CFSG.Open.classicalInvolutionOddCore J) ⧸
        Subgroup.center (J ⧸ CFSG.Open.classicalInvolutionOddCore J) ≃*
      alternatingGroup (Fin 7))

theorem TwoA7Witness.classical {F : Type*} [Group F] {J : Subgroup F} (h : TwoA7Witness J) :
    CFSG.Open.classicalInvolutionWitness J :=
  Or.inr h

@[expose] def NoTwoA7ClassicalAt {F : Type*} [Group F] (z : F) : Prop :=
  orderOf z = 2 → ∀ J : Subgroup F, z ∈ J → CFSG.Open.IsSubnormal J (Subgroup.centralizer {z}) →
    TwoA7Witness J → ¬ Group.IsSolvable J → False

@[expose] def NoTwoA7Classical (F : Type*) [Group F] : Prop :=
  ∀ z : F, NoTwoA7ClassicalAt z

@[expose] def GHOddLie (X : Type) [Group X] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧
    ((p ≠ 2 ∧ (LieModel X .PSL 2 p f ∨ LieModel X .PSL 3 p f ∨ LieModel X .PSU 3 p f ∨
        LieModel X .PSp 2 p f ∨ LieModel X .G2 0 p f ∨ LieModel X .trialityD4 0 p f)) ∨
      (p ≠ 2 ∧ p ^ f % 8 ≠ 1 ∧ LieModel X .PSL 4 p f) ∨
      (p ≠ 2 ∧ p ^ f % 8 ≠ 7 ∧ LieModel X .PSU 4 p f) ∨
      (p ^ f % 4 = 3 ∧ LieModel X .PSL 5 p f) ∨
      (p ^ f % 4 = 1 ∧ LieModel X .PSU 5 p f) ∨
      LieModel X .twistedG2 0 3 f)

@[expose] def TwoA7OddLie : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Subgroup.center X = ⊥ → GHOddLie X → NoTwoA7Classical X

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
