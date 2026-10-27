module

public import CFSG.HardMathSupport.Seitz.TrialityEven.FrameLiftEven
public import CFSG.HardMathSupport.Seitz.TrialityEven.RouteCModel

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityEven

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1

section Defs


@[expose] def PhiFramePlaneGenEvenThree (ε : ℤ) : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (2 ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (2 ^ f)) →
    (3 : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * ((2 ^ f : ℕ) : ℤ) + 1 →
    ∀ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
      (∃ F : D4PhiFrame K σ (2 ^ f) ε, F.Contains E) →
      Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
        ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤

end Defs


theorem phiFramePlaneGenEvenThree_pm {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    PhiFramePlaneGenEvenThree ε := by
  intro f hf K _ _ hK σ hσ hd E hE hEcard hF
  obtain ⟨r', hr', hr'5, hr'd, E', hE', hE'card, hsub⟩ :=
    phiThreeLiftEven hε hf K hK σ hσ hd E hE hEcard hF
  have htop := closure_cenGen_routeC_even (by omega) K hK σ hσ hε hr' hr'5 hr'd E' hE' hE'card
  rw [eq_top_iff, ← htop]
  exact (Subgroup.closure_le _).2 hsub

end CFSG.HardMathSupport.Seitz.TrialityEven
