module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLE8Base
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenSplit
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcChainsE8

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf
  (lieOrderNumerator lieOrderDivisor LieOrderFormulasInput)

theorem twoLocalWhen_E8
    (hLie : LieOrderFormulasInput) : TwoLocalWhen .E8 (fun _ _ => True) := by
  intro K _ _ _ _ n f f₀ p _ hadm hmodel _ hp hp5 hpK _ hf
  have hf1 : 1 ≤ f := hadm.2.1
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  have hp2 : p ≠ 2 := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hform, -⟩ := hLie K .E8 n 2 f hadm hmodel
  have hpe : ¬ p ∣ 30 := by
    intro h
    have h5 : p = 5 := by
      have h' : p ∣ 2 * 3 * 5 := h
      rcases (Nat.Prime.dvd_mul hp).1 h' with h'' | h''
      · rcases (Nat.Prime.dvd_mul hp).1 h'' with h3 | h3
        · have := Nat.le_of_dvd (by norm_num) h3
          omega
        · have := Nat.le_of_dvd (by norm_num) h3
          omega
      · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h''
    subst h5
    apply hpK
    have h5 : (5 : ℕ) ∣ (2 ^ f) ^ 20 - 1 := by
      rw [← pow_mul]
      exact (by norm_num : (5 : ℕ) ∣ 2 ^ 4 - 1).trans
        (Nat.pow_sub_one_dvd_pow_sub_one 2 (Dvd.intro (5 * f) (by ring)))
    have hnum : 5 ∣ lieOrderNumerator .E8 n (2 ^ f) := by
      show 5 ∣ (2 ^ f) ^ 120 * ((2 ^ f) ^ 30 - 1) * ((2 ^ f) ^ 24 - 1) * ((2 ^ f) ^ 20 - 1) *
        ((2 ^ f) ^ 18 - 1) * ((2 ^ f) ^ 14 - 1) * ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 8 - 1) *
        ((2 ^ f) ^ 2 - 1)
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (Dvd.dvd.mul_right (Dvd.dvd.mul_left h5 _) _) _) _) _) _
    have hdiv1 : lieOrderDivisor .E8 n (2 ^ f) = 1 := rfl
    rw [hdiv1, mul_one] at hform
    rw [hform]
    exact hnum
  rcases hmodel with ⟨ht, -⟩ | ⟨hn, -, hE⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · subst hn
    obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := hE
    let θ : K ≃* adjointGroup Tag.E8 F := e.trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
    haveI : Fintype (WeylGroup .E8) := Fintype.ofFinite _
    obtain ⟨r, hr, hrdvd, hrq, hrN⟩ :=
      OLExc.exists_ppd_prime_not_dvd_normalizer .E8 hf hf₀ hFcard θ hp
      (by norm_num) (fun h => by omega) hpe
      (fun r hr h => hr.dvd_of_dvd_pow ((card_torusGroup_E8 (K := F)) ▸ h))
      excE8Mask excE8Fac excE8Mask_cover parabolicSum_E8_coat_eq
      (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
    refine ⟨r, hr, fun R hR2 hR1 => ?_⟩
    have hq2 : 1 < 2 ^ f₀ := Nat.one_lt_two_pow (by omega)
    have hsub : ∀ d : ℕ, d ≠ 0 → (2 ^ f₀) ^ d - 1 ≠ 0 := fun d hd => by
      have := Nat.one_lt_pow hd hq2
      omega
    have hdr : ¬ r ∣ lieOrderDivisor .E8 0 (2 ^ f₀) := fun h => hr.one_lt.ne' (Nat.dvd_one.1 h)
    have hrn : r ∣ lieOrderNumerator .E8 0 (2 ^ f₀) := by
      show r ∣ (2 ^ f₀) ^ 120 * ((2 ^ f₀) ^ 30 - 1) * ((2 ^ f₀) ^ 24 - 1) * ((2 ^ f₀) ^ 20 - 1) *
        ((2 ^ f₀) ^ 18 - 1) * ((2 ^ f₀) ^ 14 - 1) * ((2 ^ f₀) ^ 12 - 1) * ((2 ^ f₀) ^ 8 - 1) *
        ((2 ^ f₀) ^ 2 - 1)
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left hrdvd _) _) _)
          _) _) _) _) _
    have hnum0 : lieOrderNumerator .E8 0 (2 ^ f₀) ≠ 0 := by
      show (2 ^ f₀) ^ 120 * ((2 ^ f₀) ^ 30 - 1) * ((2 ^ f₀) ^ 24 - 1) * ((2 ^ f₀) ^ 20 - 1) *
        ((2 ^ f₀) ^ 18 - 1) * ((2 ^ f₀) ^ 14 - 1) * ((2 ^ f₀) ^ 12 - 1) * ((2 ^ f₀) ^ 8 - 1) *
        ((2 ^ f₀) ^ 2 - 1) ≠ 0
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by positivity)) (hsub _ (by norm_num)))
          (hsub _ (by norm_num))) (hsub _ (by norm_num))) (hsub _ (by norm_num)))
          (hsub _ (by norm_num))) (hsub _ (by norm_num))) (hsub _ (by norm_num)))
          (hsub _ (by norm_num))
    exact padicValNat_add_lt_of_not_dvd hr (hrN R hR2 hR1) hdr hnum0 hrn
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
