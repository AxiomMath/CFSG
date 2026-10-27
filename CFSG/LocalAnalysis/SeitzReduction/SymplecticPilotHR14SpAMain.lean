module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpALevi

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {n j : ℕ}

theorem card_centralizer_spARep (hjn : 2 * j ≤ n) :
    Nat.card (centralizer ({spARep n j} : Set (StatedSp n K))) =
      Nat.card (spARadical K n j hjn) * Nat.card (spALeviHom (K := K) hjn).range := by
  rw [(spALeviHom (K := K) hjn).ker.card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (spALeviHom (K := K) hjn)).toEquiv,
    mul_comm, spARadical, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

theorem factorization_two_card_statedSp [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (m : ℕ) :
    (Nat.card (StatedSp m K)).factorization 2 = f * m ^ 2 := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hodd : ¬ 2 ∣ ∏ i ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * i) - 1) :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.not_dvd_prod_pow_two_mul_sub_one
      Nat.prime_two (by rw [hK]; exact dvd_pow_self 2 (by
        rintro rfl
        rw [pow_zero] at hK
        have : 2 ≤ Nat.card K := by
          have := Finite.one_lt_card (α := K)
          exact this
        omega)) hq m
  have hne : ∏ i ∈ Finset.Icc 1 m, (Nat.card K ^ (2 * i) - 1) ≠ 0 := fun h => hodd (h ▸ dvd_zero 2)
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    Nat.factorization_mul (pow_ne_zero _ (by omega)) hne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd, add_zero, hK, ← pow_mul,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]

theorem spACentralizerTwoPartInput_holds : SpACentralizerTwoPartInput := by
  intro n j f K _ _ _ hKc hjn
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  rw [card_centralizer_spARep hjn, card_spARadical hjn, card_range_spALeviHom hjn,
    Nat.factorization_mul (pow_ne_zero _ (by omega)) (mul_ne_zero Nat.card_pos.ne'
      Nat.card_pos.ne'), Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Finsupp.add_apply, Finsupp.add_apply, factorization_two_card_statedSp hKc,
    factorization_two_card_statedSp hKc, hKc, ← pow_mul, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, spAExp]
  obtain ⟨d, rfl⟩ : ∃ d, n = 2 * j + d := ⟨n - 2 * j, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have h : j ^ 2 ≤ (2 * j + d) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  zify [h]
  ring

theorem spACentralizerPerfectInput_holds : SpACentralizerPerfectInput := by
  intro n j K _ _ _ hK _ hjn
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨κ, hκ⟩ : ∃ κ : Kˣ, (κ : K) ≠ 1 := by
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, 1} : Finset K)) (t := Finset.univ)
      (by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact lt_of_le_of_lt (Finset.card_le_two) (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    exact ⟨Units.mk0 a ha.1, ha.2⟩
  refine le_antisymm (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  · calc centralizer ({spARep n j} : Set (StatedSp n K)) ≤
          (spALeviHom hjn).range ⊔ spARadical K n j hjn := centralizer_spARep_le_sup hjn
      _ ≤ _ := sup_le (range_spALeviHom_le_commutator hjn hK) (spARadical_le_commutator hjn hκ)

end CFSG.SeitzReduction.SymplecticPilot
