module

public import CFSG.ClassicalInvolution.Q3.Basic
public import CFSG.ClassicalInvolution.Q3.Q3TLTDatum

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def HasDatum (X : Type) [Group X] : Prop :=
  ∃ (R : Subgroup X) (S : Sylow 2 R) (t : X), TightDatum R S t

@[expose] def HasMember3 (X : Type) [Group X] : Prop :=
  ∃ (z : X) (J : Subgroup X), IsClassicalMember3 J z

@[expose] def NoDatumL3U3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : StatedLieTag) (p f : ℕ),
    (t = .PSL ∨ t = .PSU) → p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    StatedClassicalModel X t 3 p f → TwoSubgroupsFourGenerated X → ¬ HasDatum X

@[expose] def NoDatumSp4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (p f : ℕ),
    p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    StatedClassicalModel X .PSp 2 p f → TwoSubgroupsFourGenerated X → ¬ HasDatum X

@[expose] def NoDatumL4U4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (p f : ℕ),
    p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ((p ^ f % 8 ≠ 1 ∧ StatedClassicalModel X .PSL 4 p f) ∨
      (p ^ f % 8 ≠ 7 ∧ StatedClassicalModel X .PSU 4 p f)) →
    TwoSubgroupsFourGenerated X → ¬ HasDatum X

@[expose] def NoDatumL5U5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (p f : ℕ),
    p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ((p ^ f % 4 = 3 ∧ StatedClassicalModel X .PSL 5 p f) ∨
      (p ^ f % 4 = 1 ∧ StatedClassicalModel X .PSU 5 p f)) →
    TwoSubgroupsFourGenerated X → ¬ HasDatum X

@[expose] def NoDatumL2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p ≠ 2 →
    StatedClassicalModel X .PSL 2 p f → ¬ HasDatum X

@[expose] def NoDatumRee : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), ReeTitsModel X .twistedG2 3 f → ¬ HasDatum X

@[expose] def NoDatumG2D4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : StatedLieTag) (p f : ℕ),
    (t = .G2 ∨ t = .trialityD4) → p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ChevalleyExceptionalModel X t p f → TwoSubgroupsFourGenerated X → ¬ HasDatum X

@[expose] def Member3Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : StatedLieTag) (n : ℕ),
    ((t = .PSL ∧ (n = 3 ∨ n = 4 ∨ n = 5)) ∨ (t = .PSU ∧ (n = 3 ∨ n = 4)) ∨
      (t = .PSp ∧ n = 2) ∨ ((t = .G2 ∨ t = .trialityD4) ∧ n = 0)) →
    LieModel X t n 3 1 → HasMember3 X

end CFSG.ClassicalInvolution.Q3.TA3
