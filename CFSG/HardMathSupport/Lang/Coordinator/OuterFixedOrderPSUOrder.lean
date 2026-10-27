module

public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.HardMathSupport.Lang.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)

theorem lieOrderNumerator_PSU_cast (n q : ℕ) (hq : 1 ≤ q) :
    ((lieOrderNumerator .PSU n q : ℕ) : ℤ) =
      (q : ℤ) ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i - (-1) ^ i) := by
  simp only [lieOrderNumerator]
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : Even i
  · simp only [hi, ↓reduceIte, Nat.cast_sub (Nat.one_le_pow _ _ hq), hi.neg_one_pow]
    push_cast
    rfl
  · simp only [hi, ↓reduceIte, (Nat.not_even_iff_odd.mp hi).neg_one_pow]
    ring

theorem card_primeFormP_one_mul_gcd {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hn : 1 ≤ n) :
    Nat.card (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
        Nat.gcd n (ℓ ^ f + 1) = lieOrderNumerator .PSU n (ℓ ^ f) := by
  have := h.finite
  have hB := gramForm_isSymm h (G := (1 : Matrix (Fin n) (Fin n) K)) (by
    rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one])
  have hBl := gramForm_separatingLeft h (G := (1 : Matrix (Fin n) (Fin n) K)) (by simp)
  have hdim : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hS := (CFSG.LinearGroups.unitary_full_group_order h hB hBl hdim hn).2.1
  have hS' : (Nat.card (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : ℤ) =
      ((lieOrderNumerator .PSU n (ℓ ^ f) : ℕ) : ℤ) := by
    rw [Units.val_one, card_gramSU, hS,
      lieOrderNumerator_PSU_cast n (ℓ ^ f) (Nat.one_le_pow _ _ h.prime.pos)]
  have hS'' : Nat.card (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      lieOrderNumerator .PSU n (ℓ ^ f) := by exact_mod_cast hS'
  have hZ := card_normOneScalars_one h hn
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n)
  rw [hS'', hZ] at h3
  exact h3.symm

end CFSG.HardMathSupport.Lang.Coordinator
