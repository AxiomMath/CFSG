module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6RouteWStarProved

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open Subgroup TauCeti CFSG.LieType.SeitzGeneration CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.GH74.GLS.Stage2.Bender.Thm1


@[expose] def Phi6ThreeLift : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) → 3 ≠ ℓ →
    (3 : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 →
    ∀ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
      (∃ F : D4PhiFrame K σ (ℓ ^ f) (-1), F.Contains E) →
      ∃ r' : ℕ, r'.Prime ∧ 5 ≤ r' ∧ r' ≠ ℓ ∧
        (r' : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 ∧
        ∃ E' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
          CFSG.IsElementaryAbelian r' E' ∧ Nat.card E' = r' ^ 2 ∧
          {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom | ∃ y ∈ E', y ≠ 1 ∧ k * y = y * k} ⊆
            Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
              ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k}

theorem phiFramePlaneGenAt_three_of_lift (hL : Phi6ThreeLift)
    (h6 : ∀ r, 5 ≤ r → PhiPlaneGenAt (-1) r) : PhiFramePlaneGenAt (-1) 3 := by
  intro ℓ f hℓ hℓ2 hf K _ _ hK σ hσ _ h3ℓ hd E hE hEcard hF
  obtain ⟨r', hr', hr'5, hr'ℓ, hr'd, E', hE', hE'card, hsub⟩ :=
    hL ℓ f hℓ hℓ2 hf K hK σ hσ h3ℓ hd E hE hEcard hF
  have htop := h6 r' hr'5 ℓ f hℓ hℓ2 hf K hK σ hσ hr' hr'ℓ hr'd E' hE' hE'card
  rw [eq_top_iff, ← htop]
  exact (Subgroup.closure_le _).2 hsub


theorem seitzExcAnisotropicForAt_trialityOdd_handback_of_coreW_lift
    (h : ∀ r, 5 ≤ r → Phi6CoreW r) (hL : Phi6ThreeLift) :
    SeitzExcAnisotropicForAt IsTrialityIndex
      (fun d _ => ∃ q : PrimePower, d = .trialityD4 q ∧ q.p ≠ 2) :=
  seitzExcAnisotropicForAt_trialityOdd_handback_of_coreW h
    (phiFramePlaneGenAt_three_of_lift hL fun r hr5 => phiPlaneGenAt_neg_of_coreW hr5 (h r hr5))

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
