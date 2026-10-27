module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KC.Setup
public import CFSG.LocalAnalysis.AGLEmbedding.AltBeta

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.Open

theorem not_pow_three_dvd_factorial_of_le {p m : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hm : m ≤ 2 * p) :
    ¬ p ^ 3 ∣ Nat.factorial m := by
  intro h
  have hsq : 2 * p < p ^ 2 := by nlinarith
  have hlog : Nat.log p m < 2 := Nat.log_lt_of_lt_pow' (by norm_num) (lt_of_le_of_lt hm hsq)
  rw [Nat.Prime.pow_dvd_factorial_iff hp hlog] at h
  have hIco : Finset.Ico 1 2 = ({1} : Finset ℕ) := by decide
  rw [hIco, Finset.sum_singleton, pow_one] at h
  have hdiv : m / p ≤ 2 := Nat.div_le_of_le_mul (by linarith)
  exact absurd (h.trans hdiv) (by norm_num)

theorem kc_alt {K : Type} [Group K] [Finite K] {p n : ℕ} [Fact p.Prime] {S : Sylow p K}
    {L : Subgroup K} (h : KCData K p n S L) (m : ℕ) (e : K ≃* alternatingGroup (Fin m))
    (hΓ : GLBCore p 1 (S : Subgroup K) ≠ ⊤) : False := by
  have hp : p.Prime := h.prime
  have hp5 : 5 ≤ p := h.p5
  by_cases hm : 2 * p + 1 ≤ m
  · exact hΓ (CFSG.AGLEmbedding.glbCore_one_eq_top hp (by omega) hm e S)
  · have hdvd : Nat.card K ∣ Nat.factorial m := by
      rw [Nat.card_congr e.toEquiv]
      refine (Subgroup.card_subgroup_dvd_card _).trans ?_
      rw [Nat.card_perm]
      simp
    have h3 : p ^ 3 ∣ Nat.card K := (pow_dvd_pow p h.n3).trans h.dvd
    exact not_pow_three_dvd_factorial_of_le hp (by omega) (by omega) (h3.trans hdvd)

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
