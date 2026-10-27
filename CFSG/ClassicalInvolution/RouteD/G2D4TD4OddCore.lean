module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4OddCore
public import CFSG.ClassicalInvolution.ModelFacts.G2D4ThreeD4One
public import CFSG.ClassicalInvolution.RouteD.G2D4TD4NonToral
public import CFSG.LieType.HighestRoot.CentTrialityFixed

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Balance.Q27
open scoped MatrixGroups

theorem td4ThreeOddCoreOne_proved : TD4ThreeOddCoreOne := by
  intro n p e hp hadm hpe
  have hn : n = 0 := hadm.2.2
  subst hn
  have : Fact p.Prime := ⟨hp⟩
  have he : 1 ≤ e := hadm.2.1
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 3 := hpe ▸ dvd_pow_self 2 (by omega)
    omega
  have hfin := finite_galoisField_three (p := p) e he
  have hσ := sigma_three_td4 (p := p) e he
  have hK1 := neg_one_ne_one_galoisField_td4 hp2 (3 * e)
  have hrange := range_twistedIncl_eq hp2 e he
  have hC₀ : graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
      (iterateFrobenius (GaloisField p (3 * e)) p e) ≤
      (twistedIncl (iterateFrobenius (GaloisField p (3 * e)) p e)).range := hrange.ge
  have hgF : ∀ g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e),
      twistedIncl (iterateFrobenius (GaloisField p (3 * e)) p e) g ∈
        graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
          (iterateFrobenius (GaloisField p (3 * e)) p e) := fun g => hrange ▸ ⟨g, rfl⟩
  have hcardK : Nat.card (GaloisField p (3 * e)) = 27 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul', hpe]
    norm_num
  have hσ3 : ∀ c, iterateFrobenius (GaloisField p (3 * e)) p e c = c ^ 3 := fun c => by
    rw [iterateFrobenius_def, hpe]
  have hchar : ringChar (GaloisField p (3 * e)) ≠ 2 := by
    rw [ringChar.eq (GaloisField p (3 * e)) p]
    exact hp2
  have hF3 := CFSG.LieType.HighestRoot.card_fixedField_eq_three hchar hσ3
  set σ := iterateFrobenius (GaloisField p (3 * e)) p e with hσdef
  have hτ2 : slLong σ hσ (-1) * slLong σ hσ (-1) = 1 := by
    rw [← map_mul, neg_one_mul_neg_one_SL2, map_one]
  have hτ1 : slLong σ hσ (-1) ≠ 1 := by
    intro h
    have h' := twistedIncl_slLong_neg_one hσ
    rw [h, map_one, ← rootDiagUnit_one] at h'
    exact aLongTD4_ne_one hK1 (rootDiagUnit_injective h'.symm)
  refine ⟨slLong σ hσ (-1), hτ2, hτ1, ?_⟩
  intro N hNc hNnorm hNodd
  exact oddCore_td4 hσ hK1 (by omega) hF3 hC₀ hgF hNc hNnorm hNodd

theorem td4ThreeOddCore_proved : TD4ThreeOddCore :=
  td4ThreeOddCore_of_one td4ThreeOddCoreOne_proved

theorem d4ThreeCentralizerFacts_proved : D4ThreeCentralizerFacts :=
  d4ThreeCentralizerFacts_of_oddCore td4ThreeOddCore_proved

end CFSG.ClassicalInvolution.G2D4Models
