module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLE8Base
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenSplit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLE7Chains

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf
  (lieOrderNumerator lieOrderDivisor LieOrderFormulasInput)

set_option linter.unusedVariables false in
theorem twoLocalWhen_E7
    (hLie : LieOrderFormulasInput) : TwoLocalWhen .E7 (fun _ _ => True) := by
  intro K _ _ _ _ n f f₀ p _ hadm hmodel _ hp hp5 hpK _ hf
  have hf1 : 1 ≤ f := hadm.2.1
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpe : ¬ p ∣ 18 := by
    intro h
    have h' : p ∣ 2 * 3 * 3 := h
    rcases (Nat.Prime.dvd_mul hp).1 h' with h'' | h''
    · rcases (Nat.Prime.dvd_mul hp).1 h'' with h2 | h2
      · have := Nat.le_of_dvd (by norm_num) h2
        omega
      · have := Nat.le_of_dvd (by norm_num) h2
        omega
    · have := Nat.le_of_dvd (by norm_num) h''
      omega
  rcases hmodel with ⟨ht, -⟩ | ⟨hn, -, hE⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · subst hn
    obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := hE
    let θ : K ≃* adjointGroup Tag.E7 F := e.trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
    haveI : Fintype (WeylGroup .E7) := Fintype.ofFinite _
    obtain ⟨r, hr, hrdvd, hrq, hrN⟩ :=
      OLExc.exists_ppd_prime_not_dvd_normalizer .E7 hf hf₀ hFcard θ hp
      (by norm_num) (fun h => by omega) hpe
      (fun r hr h => hr.dvd_of_dvd_pow
        ((h.trans (Dvd.intro _ (card_torusGroup_E7 (K := F)))) : r ∣ (Nat.card F - 1) ^ 7))
      olE7Mask olE7Fac olE7Mask_cover olE7_parabolicSum_coat_eq
      (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
    refine ⟨r, hr, fun R hR2 hR1 => ?_⟩
    have hq2 : 1 < 2 ^ f₀ := Nat.one_lt_two_pow (by omega)
    have hsub : ∀ d : ℕ, d ≠ 0 → (2 ^ f₀) ^ d - 1 ≠ 0 := fun d hd => by
      have := Nat.one_lt_pow hd hq2
      omega
    have hdr : ¬ r ∣ lieOrderDivisor .E7 0 (2 ^ f₀) := fun h =>
      hrq (h.trans (Nat.gcd_dvd_right 2 (2 ^ f₀ - 1)))
    have hrn : r ∣ lieOrderNumerator .E7 0 (2 ^ f₀) := by
      show r ∣ (2 ^ f₀) ^ 63 * ((2 ^ f₀) ^ 18 - 1) * ((2 ^ f₀) ^ 14 - 1) * ((2 ^ f₀) ^ 12 - 1) *
        ((2 ^ f₀) ^ 10 - 1) * ((2 ^ f₀) ^ 8 - 1) * ((2 ^ f₀) ^ 6 - 1) * ((2 ^ f₀) ^ 2 - 1)
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left hrdvd _) _) _) _) _) _) _
    have hnum0 : lieOrderNumerator .E7 0 (2 ^ f₀) ≠ 0 := by
      show (2 ^ f₀) ^ 63 * ((2 ^ f₀) ^ 18 - 1) * ((2 ^ f₀) ^ 14 - 1) * ((2 ^ f₀) ^ 12 - 1) *
        ((2 ^ f₀) ^ 10 - 1) * ((2 ^ f₀) ^ 8 - 1) * ((2 ^ f₀) ^ 6 - 1) * ((2 ^ f₀) ^ 2 - 1) ≠ 0
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (pow_ne_zero _ (by positivity)) (hsub _ (by norm_num)))
          (hsub _ (by norm_num))) (hsub _ (by norm_num))) (hsub _ (by norm_num)))
          (hsub _ (by norm_num))) (hsub _ (by norm_num))) (hsub _ (by norm_num))
    exact padicValNat_add_lt_of_not_dvd hr (hrN R hR2 hR1) hdr hnum0 hrn
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
