module

public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.HardMathSupport.Timmesfeld.LinearRank

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Open

variable {ℓ f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K) := by
  refine ⟨by rw [Units.val_one, transpose_one], fun i j => ?_⟩
  rw [Units.val_one, one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem dvd_card_units_of_dvd_add_one [Finite K] (h : UnitaryFieldData ℓ f K) {p : ℕ}
    (hpq : p ∣ ℓ ^ f + 1) : p ∣ Nat.card Kˣ := by
  rw [Nat.card_units, h.card_eq_sq]
  have hq : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  have : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, ℓ ^ f = m + 1 := ⟨ℓ ^ f - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [this]
  exact Dvd.dvd.mul_right hpq _

theorem primeFormConjHom_eq_one_iff_center (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    primeFormConjHom h _ A = 1 ↔
      (A : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) := by
  have key := (unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_one (K := K) (n := n)) hn hne).2.2.1 ⟨A, 1⟩
  rw [primeFormPsi_apply, map_one, mul_one] at key
  have hn1 : 1 ≤ n := by omega
  rw [key, mem_center_iff]
  constructor
  · rintro ⟨-, c, -, hA⟩
    exact ⟨c, hA⟩
  · rintro ⟨c, hA⟩
    refine ⟨rfl, c, norm_eq_one_of_scalar_mem_primeFormUnitary h hn1 1 ?_, hA⟩
    rw [← hA]
    exact A.2

theorem card_le_of_diagonal [Finite K] (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    (E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (hED : E ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ (n - 1) :=
  card_le_of_scalar_kernel hp hp2 (dvd_card_units_of_dvd_add_one h hpq) (by omega)
    (primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (primeFormConjHom h _) (primeFormConjHom_eq_one_iff_center h hn hne) E hED hE

end CFSG.HardMathSupport.Timmesfeld.LinearRank
