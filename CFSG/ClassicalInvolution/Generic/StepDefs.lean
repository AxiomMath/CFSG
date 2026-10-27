module

public import CFSG.ClassicalInvolution.Generic.Induction

public section

namespace CFSG.ClassicalInvolution.Generic

open CFSG.Open CFSG.LieType.Universal

variable (p f : ℕ) [Fact p.Prime]

@[expose] def CoreStep : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
    CITBelowU p f (Nat.card G) → LieSystem p f G (Set.range fun g : G => conjSub g K)

@[expose] def CoreStepModel : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
    CITBelowU p f (Nat.card G) →
    ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ) (hp : p.Prime)
      (ψ : (modelUniv t n p e hp).K →* G),
      Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center _ ∧ IsFundTag t ∧
        CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p e ∧
        (e = f ∨ (t = .trialityD4 ∧ 3 * e = f))

@[expose] def ClassicalIsFundamental : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ) (hp : p.Prime), IsFundTag t →
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p e →
    (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n p e hp).K →* X),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center _ →
      ∀ (L : Subgroup X) (z : X), IsClassicalMember p f L z →
        ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, L = R.map ψ

variable {p}

@[expose] def CentralLift (p : ℕ) : Prop :=
  p ≠ 2 → ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ) (hp : p.Prime), IsFundTag t →
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p e →
    ∀ (Y G : Type) [Group Y] [Group G] [Finite Y] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) →
      ∀ (π : Y →* G) (ψ : (modelUniv t n p e hp).K →* G),
        Function.Surjective π → Function.Surjective ψ → Group.IsPerfect Y → IsPGroup 2 π.ker →
        π.ker ≤ Subgroup.center Y → ψ.ker = Subgroup.center _ →
        ∃ ψ' : (modelUniv t n p e hp).K →* Y, π.comp ψ' = ψ

end CFSG.ClassicalInvolution.Generic
