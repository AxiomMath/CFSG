module

public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternLayer
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6TwinFact

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.RouteD.NonClassical (F4Layer TwinPartnerFactTwin)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock)
open CFSG.ClassicalInvolution.WeakCT (diagConj2)
open scoped MatrixGroups


@[expose] def F4Row3 : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), IsFundTag t → t ≠ .G2 → t ≠ .trialityD4 →
    StatedLieAdmissible t n 3 1 →
    ∀ R₀ ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D,
      ∀ k ∈ R₀, (∀ r ∈ R₀, r * k = k * r) →
      ∀ φ : {R : Subgroup (modelUniv t n 3 1 Nat.prime_three).K //
          R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D ∧
            R ≤ Subgroup.centralizer ({k} : Set (modelUniv t n 3 1 Nat.prime_three).K)} ≃
          F4Layer 3 1,
        (∀ R R', Commutes R.1 R'.1 ↔ NonClassical.F4Layer.rel (φ R) (φ R')) →
        (∀ R, R.1 = R₀ → φ R = none) → t = .POmegaOdd ∧ n = 4

@[expose] def F4PartnerFact3 : Prop := TwinPartnerFactTwin 3 1 .POmegaOdd 4 1

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
