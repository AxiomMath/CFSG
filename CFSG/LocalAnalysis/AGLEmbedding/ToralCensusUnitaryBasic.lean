module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LinearAlgebra.LinearGroups.UnitaryFourOrder

public section

namespace CFSG.AGLEmbedding

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

@[expose] def IsTotallyIsotropicSU (q : ℕ) {K : Type} [Field K] {n : ℕ}
    (W : Submodule K (Fin n → K)) : Prop :=
  ∀ v ∈ W, ∀ w ∈ W, ∑ i, v i ^ q * w i = 0

namespace ToralCensus

theorem exists_eq_two_pow_of_card_eq_sq {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hq : Nat.card K = q ^ 2) : ∃ f : ℕ, 1 ≤ f ∧ q = 2 ^ f := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  rw [← Nat.card_eq_fintype_card, hq] at hm
  have hdvd : q ∣ 2 ^ (m : ℕ) := ⟨q, by rw [← hm, sq]⟩
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨f, ?_, rfl⟩
  rcases Nat.eq_zero_or_pos f with h0 | h0
  · subst h0
    have h1 : Nat.card K = 1 := by rw [hq]; norm_num
    exact absurd h1 (Finite.one_lt_card (α := K)).ne'
  · exact h0

theorem unitaryFieldData_of_card_eq_sq {K : Type} [Field K] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) : UnitaryFieldData 2 f K :=
  ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩

theorem isTotallyIsotropicSU_iff {K : Type} [Field K] {f n : ℕ} (h : UnitaryFieldData 2 f K)
    (W : Submodule K (Fin n → K)) :
    IsTotallyIsotropicSU (2 ^ f) W ↔ ∀ v ∈ W, ∀ w ∈ W, stdHermForm h n v w = 0 := by
  simp only [IsTotallyIsotropicSU, stdHermForm_apply, h.bar_apply]

end ToralCensus

end CFSG.AGLEmbedding
