module

public import CFSG.LieType.HighestRoot.CentTrialityThree
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Count

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.ModelFacts

variable (p e : ℕ) [Fact p.Prime]

theorem highestRootCZ_trialityD4
    (hp2 : p ≠ 2) (he : 1 ≤ e) :
    HighestRootCZ (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e))
      (GaloisField p e) := by
  set K := GaloisField p (3 * e) with hKdef
  set σ := iterateFrobenius K p e with hσdef
  have hcardK : Nat.card K = (p ^ e) ^ 3 := by
    rw [hKdef, GaloisField.card p (3 * e) (by omega), pow_mul']
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hcardK]
    exact (pow_pos (pow_pos (Fact.out : p.Prime).pos e) _).ne')
  have hσ : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card hcardK (fun c => iterateFrobenius_def p e c)
  have hK : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have hgF : ∀ g : twistedGroup σ, td4Incl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ := fun g => by
    rw [← CFSG.ClassicalInvolution.RouteD.G2D4.map_twistedGroup_eq_graphFixedRootGroup p e hp2 he]
    exact Subgroup.mem_map_of_mem _ g.2
  refine ⟨Pi.single (ng 0) 1, (isLongest_single_G2 rfl _ (k := ng 0) rfl).1,
    (isLongest_single_G2 rfl _ (k := ng 0) rfl).2, fun z hz h2 =>
      ⟨centralizer_le_normalizer_td4 hK hσ hgF hz h2, fun hF3 L hLC hCL ⟨eL⟩ _ => ?_⟩⟩
  have hq : p ^ e = 3 := by
    rw [← hF3, GaloisField.card p e (by omega)]
  have hK27 : Nat.card K = 27 := by
    rw [hcardK, hq]
    norm_num
  have hσ3 : ∀ c, σ c = c ^ 3 := fun c => by
    rw [hσdef, iterateFrobenius_def, hq]
  exact eq_rankOne_long_of_card_eq_three hK27 hσ3 hF3 hz h2 hLC hCL eL

theorem highestRootCZ_modelUniv_trialityD4
    (n : ℕ) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    HighestRootCZ (CFSG.ClassicalInvolution.Generic.modelUniv .trialityD4 n p e Fact.out).D
      (GaloisField p e) :=
  highestRootCZ_trialityD4 p e hp2 he

end CFSG.LieType.HighestRoot
