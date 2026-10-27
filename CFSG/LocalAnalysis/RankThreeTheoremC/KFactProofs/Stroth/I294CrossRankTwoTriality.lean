module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossRankTwoRest
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

private theorem three_pow_four_dvd_ordTrialityD4 (Q : ℕ) (hQ : ¬ 3 ∣ Q) :
    3 ^ 4 ∣ CFSG.Open.ordTrialityD4 Q := by
  have hmod3 : Q % 3 = 1 ∨ Q % 3 = 2 := by omega
  have h2 : Q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    rcases hmod3 with h | h <;> simp [h]
  have h4 : Q ^ 4 % 3 = 1 := by
    rw [Nat.pow_mod]
    rcases hmod3 with h | h <;> simp [h]
  have h8 : Q ^ 8 % 3 = 1 := by
    rw [Nat.pow_mod]
    rcases hmod3 with h | h <;> simp [h]
  have hcop : Nat.Coprime Q 9 := by
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9]
    exact Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hQ).symm
  have h6 : Nat.totient 9 = 6 := by decide
  have hE : Q ^ 6 ≡ 1 [MOD 9] := by
    have := Nat.ModEq.pow_totient hcop
    rwa [h6] at this
  have h9 : 9 ∣ Q ^ 6 - 1 := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hE)
  have h3a : 3 ∣ Q ^ 2 - 1 := by omega
  have h3b : 3 ∣ Q ^ 8 + Q ^ 4 + 1 := by omega
  have hprod : 3 ^ 4 ∣ (Q ^ 8 + Q ^ 4 + 1) * (Q ^ 2 - 1) * (Q ^ 6 - 1) := by
    rw [show (3 : ℕ) ^ 4 = 3 * 3 * 9 by norm_num]
    exact mul_dvd_mul (mul_dvd_mul h3b h3a) h9
  unfold CFSG.Open.ordTrialityD4
  rw [show Q ^ 12 * (Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) =
      Q ^ 12 * ((Q ^ 8 + Q ^ 4 + 1) * (Q ^ 2 - 1) * (Q ^ 6 - 1)) by ring]
  exact Dvd.dvd.mul_left hprod _

theorem i294CrossThreeRankTwoTriality_holds :
    I294CrossThreeRankTwoTriality := by
  intro L _ _ _ _ d hT hc3 hLe _ _ _ h81
  obtain ⟨idx, hv⟩ := d
  obtain ⟨q, rfl⟩ : ∃ q : TauCeti.PrimePower, idx = .trialityD4 q := by
    cases idx
    case trialityD4 q => exact ⟨q, rfl⟩
    all_goals simp [I294CrossIsTriality] at hT
  obtain ⟨eL⟩ := hLe
  have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_trialityD4] using hc3
  have hord : Nat.card L = CFSG.Open.ordTrialityD4 q.card := by
    rw [Nat.card_congr eL.toEquiv,
      CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_trialityD4_carrier q hv]
  have hQ3 : ¬ 3 ∣ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hdiv : 3 ^ 4 ∣ Nat.card L := by
    rw [hord]
    exact three_pow_four_dvd_ordTrialityD4 q.card hQ3
  exact (h81 hdiv).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
