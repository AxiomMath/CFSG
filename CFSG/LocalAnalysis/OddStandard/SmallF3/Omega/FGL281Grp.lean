module

public import Mathlib.GroupTheory.IsPerfect
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

namespace CFSG.OddStandard.SmallF3.Omega

open scoped commutatorElement

theorem fg_comm_mul_central {G : Type*} [Group G] {a b z₁ z₂ : G}
    (h₁ : z₁ ∈ Subgroup.center G) (h₂ : z₂ ∈ Subgroup.center G) :
    ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  rw [Subgroup.mem_center_iff] at h₁ h₂
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * z₁ * (b * z₂) * (z₁⁻¹ * a⁻¹) * (z₂⁻¹ * b⁻¹)
      = a * (b * z₂) * z₁ * (z₁⁻¹ * a⁻¹) * (z₂⁻¹ * b⁻¹) := by
        rw [mul_assoc a z₁, ← h₁ (b * z₂)]
        simp only [mul_assoc]
    _ = a * (b * z₂) * a⁻¹ * (z₂⁻¹ * b⁻¹) := by
        rw [mul_assoc _ z₁ _, mul_inv_cancel_left]
    _ = a * b * a⁻¹ * z₂ * (z₂⁻¹ * b⁻¹) := by
        rw [← mul_assoc a b z₂, mul_assoc (a * b) z₂ a⁻¹, ← h₂ a⁻¹]
        simp only [mul_assoc]
    _ = a * b * a⁻¹ * b⁻¹ := by rw [mul_assoc _ z₂ _, mul_inv_cancel_left]

theorem fg_eq_bot_of_pow_twelve {H : Type*} [Group H] [Finite H] {P : Subgroup H}
    (hP : ⁅P, P⁆ = P) (h : ∀ x ∈ P, x ^ 12 = 1) : P = ⊥ := by
  by_contra hne
  have hperf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  have hn : Nat.card ↥P ≠ 0 := Nat.card_pos.ne'
  have hprimes : (Nat.card ↥P).primeFactors ⊆ {2, 3} := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hpp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (Nat.dvd_of_mem_primeFactors hp)
    have hx12 : x ^ 12 = 1 := Subtype.ext (h x.1 x.2)
    have hdvd : p ∣ 12 := hx ▸ orderOf_dvd_of_pow_eq_one hx12
    have h12 : (12 : ℕ) = 2 * 2 * 3 := by norm_num
    rw [h12] at hdvd
    rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h2 | h2
    · rcases (Nat.Prime.dvd_mul hpp).mp h2 with h2 | h2 <;>
        exact Finset.mem_insert.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h2))
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr
        ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp h2))
  have h6 : (∏ p ∈ (Nat.card ↥P).primeFactors, p) ∣ 6 :=
    (Finset.prod_dvd_prod_of_subset _ _ _ hprimes).trans (by decide)
  have hdvd : Nat.card ↥P ∣ 2 ^ Nat.card ↥P * 3 ^ Nat.card ↥P := by
    rw [← mul_pow]
    exact (Nat.dvd_prod_primeFactors_pow_self hn).trans (pow_dvd_pow_of_dvd h6 _)
  have hsolv : Group.IsSolvable ↥P :=
    TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three hdvd
  exact Group.IsPerfect.not_isSolvable ↥P hsolv

end CFSG.OddStandard.SmallF3.Omega
