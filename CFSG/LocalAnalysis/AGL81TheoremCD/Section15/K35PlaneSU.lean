module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.UniAut

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.HardMathSupport.Timmesfeld.Tables CFSG.HardMathSupport.Lang
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem exists_inner_or_conj_fieldAut_psu (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (h3 : 3 ∣ ℓ ^ f + 1)
    {A : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (hA : ∀ α ∈ A, α ^ 3 = 1) (hA9 : Nat.card A = 9) :
    (∃ α ∈ A, α ≠ 1 ∧ α ∈ (MulAut.conj : primeFormP h ((1 : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) →* MulAut (primeFormP h ((1 : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K))).range) ∨
      (9 ∣ Nat.gcd n (ℓ ^ f + 1) ∧ ∃ α ∈ A, ∃ (σ : K ≃+* K)
        (M : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
        orderOf σ = 3 ∧ α = primeFormConjHom h _ M * primeFormFieldHom h isPrimeFormGram_one σ *
          (primeFormConjHom h _ M)⁻¹) := by
  refine or_iff_not_imp_left.2 fun hinn => ?_
  have := T1b.finite_mulAut_primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hA9' : Nat.card A = 3 ^ 2 := by rw [hA9]; norm_num
  have hAe : CFSG.Open.IsElemAbelian 3 A :=
    ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hA9', hA⟩
  have h9 : 9 ∣ Nat.gcd n (ℓ ^ f + 1) := by
    by_contra h9
    obtain ⟨x, ⟨hxA, hxI⟩, hx1⟩ := T1b.meets_inner_unitary h hn hq Nat.prime_three
      (by norm_num) h3 (by norm_num [h9]) A hAe hA9'
    exact hinn ⟨x, hxA, hx1, hxI⟩
  have hAD : ¬ A ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := fun hle => by
    have := T1b.isCyclic_unitaryD_quotient h hn hq
    obtain ⟨x, ⟨hxA, hxI⟩, hx1⟩ := T1b.exists_ne_one_inf_of_cyclic _
      (inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) Nat.prime_three A
      hle hAe hA9'
    exact hinn ⟨x, hxA, hx1, hxI⟩
  have hFker := ker_primeFormFieldFactor h isPrimeFormGram_one hn hq
  set Φ := primeFormFieldFactor h isPrimeFormGram_one hn hq
  obtain ⟨α, hαA, hαD⟩ := SetLike.not_le_iff_exists.1 hAD
  have hΦ : Φ α ≠ 1 := fun h1 => hαD (hFker ▸ h1)
  have hα1 : α ≠ 1 := fun h1 => hΦ (by rw [h1, map_one])
  have hσ : orderOf (Φ α) = 3 := orderOf_eq_prime (by rw [← map_pow, hA α hαA, map_one]) hΦ
  obtain ⟨-, -, -, -, -, M, hM⟩ := Coordinator.unitary_prime_semilinear_field_descent' h hn hq
    Nat.prime_three (by norm_num) α (orderOf_eq_prime (hA α hαA) hα1) (Φ α) rfl hσ
  refine ⟨h9, α, hαA, Φ α, M, hσ, ?_⟩
  rw [← hM]
  group

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35
