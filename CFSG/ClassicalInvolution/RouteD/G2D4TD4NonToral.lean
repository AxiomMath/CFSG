module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Sup
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Gen
public import CFSG.ClassicalInvolution.RouteD.G2D4TD4Edge

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Balance.Q27
open scoped MatrixGroups

section Model

variable {p : ℕ} [Fact p.Prime]

theorem sup_centralizer_eq_top_model_td4 (hp2 : p ≠ 2) {e : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 0 p e)
    {u v : (modelUniv .trialityD4 0 p e Fact.out).K} (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hcomm : u * v = v * u) :
    Subgroup.centralizer ({u} : Set (modelUniv .trialityD4 0 p e Fact.out).K) ⊔
      Subgroup.centralizer ({v} : Set (modelUniv .trialityD4 0 p e Fact.out).K) = ⊤ := by
  have he : 1 ≤ e := hadm.2.1
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
  have h7 : 7 ≤ Nat.card (GaloisField p (3 * e)) := by
    have hp3 : 3 ≤ p := by
      have h2 := (Fact.out : p.Prime).two_le
      omega
    have hq3 : 3 ≤ p ^ e := by
      calc 3 ≤ p := hp3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
    calc 7 ≤ 3 ^ 3 := by norm_num
      _ ≤ (p ^ e) ^ 3 := Nat.pow_le_pow_left hq3 3
  set σ := iterateFrobenius (GaloisField p (3 * e)) p e with hσdef
  have hτ2 : slLong σ hσ (-1) * slLong σ hσ (-1) = 1 := by
    rw [← map_mul, neg_one_mul_neg_one_SL2, map_one]
  have hτ1 : slLong σ hσ (-1) ≠ 1 := by
    intro h
    have h' := twistedIncl_slLong_neg_one hσ
    rw [h, map_one, ← rootDiagUnit_one] at h'
    exact aLongTD4_ne_one hK1 (rootDiagUnit_injective h'.symm)
  exact sup_centralizer_eq_top_td4 hσ hK1 h7 hC₀ hgF
    (fun x hx hx1 => CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hp2
      he hx hτ2 hx1 hτ1) hu2 hv2 hu1 hv1 huv hcomm

theorem involutionCentralizersGenerate_td4_proved (hp2 : p ≠ 2) {e : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 0 p e) :
    InvolutionCentralizersGenerate (modelUniv .trialityD4 0 p e Fact.out).K := by
  intro u₁ u₂ h₁ h₂ h₁1 h₂1 hne hcomm
  have h := sup_centralizer_eq_top_model_td4 hp2 hadm h₁ h₂ h₁1 h₂1 hne hcomm
  rw [eq_top_iff, ← h]
  exact le_sup_left

theorem td4NonToralGenerate_proved : TD4NonToralGenerate p := by
  intro e hadm hp2 u v hu hv hu1 hv1 huv hcomm _
  have h := sup_centralizer_eq_top_model_td4 hp2 hadm hu hv hu1 hv1 huv hcomm
  rw [eq_top_iff, ← h]
  exact le_sup_left

theorem d4ThreeCentralizerFacts_of_oddCore [Fact (Nat.Prime 3)] (hB : TD4ThreeOddCore) :
    D4ThreeCentralizerFacts :=
  d4ThreeCentralizerFacts_of_nonToral td4NonToralGenerate_proved hB

end Model

end CFSG.ClassicalInvolution.G2D4Models
