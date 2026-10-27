module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.SpecialCommutatorCenterEqCentralizerAndExponentPowerTwo
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeDivisorSubgroup

open CFSG.LinearAlgebra.CoprimeActions.FermatDivisorBinaryOrder

theorem exists_prime_subgroup {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G}
    {e : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) :
    ∃ q : ℕ, q.Prime ∧ q ∣ 2 ^ (e / 2) + 1 ∧ binaryMultiplicativeOrder q = e ∧
      ∃ A : Subgroup G, A ≤ B ∧ Nat.card A = q := by
  obtain ⟨k, hk⟩ := (special_commutator_center_eq_centralizer_and_exponent_power_two h).2
  have h51 := h.1
  have h2e := h51.two_lt
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp at hk; omega
    · exact hpos
  obtain ⟨q, hq, hdvd, -, hord⟩ := exists_prime hk1
  have he2 : e / 2 = 2 ^ (k - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [hk, pow_succ]; simp
  rw [he2]
  have hdvd' : q ∣ 2 ^ e - 1 := by
    have hpos : 1 ≤ 2 ^ (2 ^ (k - 1)) := Nat.one_le_two_pow
    have he : e = 2 ^ (k - 1) * 2 := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [hk]; simp [pow_succ]
    have hsq : 2 ^ e - 1 = (2 ^ (2 ^ (k - 1)) + 1) * (2 ^ (2 ^ (k - 1)) - 1) := by
      rw [he, pow_mul]
      generalize 2 ^ (2 ^ (k - 1)) = N at hpos ⊢
      have h1 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hpos
      zify [hpos, h1]
      ring
    rw [hsq]; exact Dvd.dvd.mul_right hdvd _
  have hmem : q ∈ piOf B := by
    rw [h51.pi_eq]; exact ⟨hq, hdvd'⟩
  have hqB : q ∣ Nat.card B := hmem.2
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := B) q hqB
  refine ⟨q, hq, hdvd, ?_, Subgroup.map B.subtype (Subgroup.zpowers x), ?_, ?_⟩
  · rw [binaryMultiplicativeOrder_eq_orderOf, hord, hk]
  · rintro _ ⟨y, _, rfl⟩; exact y.2
  · rw [Subgroup.card_map_of_injective B.subtype_injective, Nat.card_zpowers, hx]

end CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeDivisorSubgroup
