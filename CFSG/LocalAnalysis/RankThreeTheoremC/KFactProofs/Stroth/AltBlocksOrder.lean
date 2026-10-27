module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocksModel
import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks

theorem card_Ω (k p m : ℕ) [NeZero p] : Nat.card (Ω k p m) = k * p + m := by
  show Nat.card ((Fin k × ZMod p) ⊕ Fin m) = k * p + m
  rw [Nat.card_sum, Nat.card_prod, Nat.card_fin, Nat.card_zmod, Nat.card_fin]

theorem factorization_factorial_of_lt_sq {p n : ℕ} (hp : p.Prime) (hn : n < p ^ 2) :
    (n.factorial).factorization p = n / p := by
  rw [Nat.factorization_factorial hp (Nat.log_lt_of_lt_pow' (by norm_num) hn)]
  rw [show Finset.Ico 1 2 = {1} from Nat.Ico_succ_singleton 1, Finset.sum_singleton, pow_one]

theorem factorization_card_alternatingGroup_fin {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn2 : 2 ≤ n) (hn : n < p ^ 2) :
    (Nat.card (alternatingGroup (Fin n))).factorization p = n / p := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
  have h2 : 2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
  have hA : Nat.card (alternatingGroup (Fin n)) ≠ 0 := by
    intro h0
    exact Nat.factorial_ne_zero n (by rw [← h2, h0, mul_zero])
  have h2p : (2 : ℕ).factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  rw [← factorization_factorial_of_lt_sq hp hn, ← h2, Nat.factorization_mul (by norm_num) hA,
    Finsupp.add_apply, h2p, zero_add]

theorem factorization_card_alternatingGroup_le_one_of_lt {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn2 : 2 ≤ n) (hn : n < 2 * p) :
    (Nat.card (alternatingGroup (Fin n))).factorization p ≤ 1 := by
  have hp2' : 2 ≤ p := hp.two_le
  have hsq : 2 * p ≤ p ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_right p hp2'
  rw [factorization_card_alternatingGroup_fin hp hp2 hn2 (lt_of_lt_of_le hn hsq)]
  have hdiv : n / p < 2 := (Nat.div_lt_iff_lt_mul hp.pos).2 hn
  exact Nat.lt_succ_iff.mp hdiv

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks
