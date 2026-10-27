module

public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Blueprint.MultiplierDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank

theorem u6_three_dvd_two_pow_add_one {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h4 : (2 : ℕ) ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]; ring
  have hm : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]; norm_num
  rw [h4]
  omega
theorem u6_two_dvd_two_pow_add_one_false {n : ℕ} (hn : Odd n) : ¬ 2 ∣ 2 ^ n + 1 := by
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn.pos.ne'
  omega
theorem u6_gcd_three {n : ℕ} (hn : Odd n) : Nat.gcd 3 (2 ^ n + 1) = 3 :=
  Nat.gcd_eq_left (u6_three_dvd_two_pow_add_one hn)
theorem u6_gcd_six {n : ℕ} (hn : Odd n) : Nat.gcd 6 (2 ^ n + 1) = 3 := by
  have hc : Nat.Coprime 2 (2 ^ n + 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (u6_two_dvd_two_pow_add_one_false hn)
  have h6 : (6 : ℕ) = 2 * 3 := rfl
  rw [h6, Nat.Coprime.gcd_mul_left_cancel 3 hc]
  exact u6_gcd_three hn
theorem u6_card_mult_zmod (n : ℕ) : Nat.card (Multiplicative (ZMod n)) = n := by
  rw [Nat.card_congr Multiplicative.toAdd]
  exact Nat.card_zmod n
theorem u6_exc_PSU_ne {f : ℕ} (hf : f ≠ 1) : exceptionalOrders .PSU 6 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all
theorem u6_exc_PSU_one : exceptionalOrders .PSU 6 2 1 = (2, 2) := rfl

theorem u6_exc_twE6_ne {f : ℕ} (hf : f ≠ 1) : exceptionalOrders .twistedE6 0 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all
theorem u6_exc_twE6_one : exceptionalOrders .twistedE6 0 2 1 = (2, 2) := rfl

section Labels

variable {K : Type} [Group K]

theorem u6_model_PSU {lab : GLALabel} (ht : lab.tag = .twA) (hr : lab.rank = 5)
    (h : CFSG.StandardType.MarkedModel lab K) : CFSG.Blueprint.LieModel K .PSU 6 2 lab.n := by
  obtain ⟨tg, rk, nn⟩ := lab
  dsimp only at ht hr
  subst ht; subst hr
  exact h
theorem u6_model_twE6 {lab : GLALabel} (ht : lab.tag = .twE6)
    (h : CFSG.StandardType.MarkedModel lab K) : CFSG.Blueprint.LieModel K .twistedE6 0 2 lab.n := by
  obtain ⟨tg, rk, nn⟩ := lab
  dsimp only at ht
  subst ht
  exact h
end Labels

theorem u6_iso_of_PSU {X Y : Type} [Group X] [Group Y] {n : ℕ}
    (hX : CFSG.Blueprint.LieModel X .PSU 6 2 n) (hY : CFSG.Blueprint.LieModel Y .PSU 6 2 n) :
    Nonempty (X ≃* Y) := by
  rcases hX with ⟨-, hX⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · rcases hY with ⟨-, hY⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hX hY
    all_goals exact absurd h0 (by norm_num)
  all_goals exact absurd h0 (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA