module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.ANineSylow

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open Equiv Finset

theorem cycleType_eq_replicate_iff_of_sq_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (h : σ ^ 2 = 1) (k : ℕ) :
    σ.cycleType = Multiset.replicate k 2 ↔ #σ.support = 2 * k := by
  constructor
  · intro hk
    rw [← Perm.sum_cycleType, hk, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  · intro hk
    have h1 := Perm.cycleType_of_pow_prime_eq_one h
    have h2 := Perm.sum_cycleType σ
    rw [h1, Multiset.sum_replicate, smul_eq_mul, hk] at h2
    rw [h1]
    congr 1
    omega

theorem multiset_replicate_two_two : Multiset.replicate 2 2 = ({2, 2} : Multiset ℕ) :=
  rfl

theorem multiset_replicate_four_two : Multiset.replicate 4 2 = ({2, 2, 2, 2} : Multiset ℕ) :=
  rfl

theorem isConj_of_commute_of_sign_eq_neg_one {α : Type*} [Fintype α] [DecidableEq α]
    {σ τ : alternatingGroup α} (hc : IsConj (σ : Perm α) (τ : Perm α)) {ρ : Perm α}
    (hρ : Perm.sign ρ = -1) (hρσ : Commute ρ (σ : Perm α)) : IsConj σ τ := by
  obtain ⟨π, hπ⟩ := isConj_iff.mp hc
  rcases Int.units_eq_one_or (Perm.sign π) with h | h
  · exact isConj_iff.mpr ⟨⟨π, Perm.mem_alternatingGroup.mpr h⟩, Subtype.ext (by simpa using hπ)⟩
  · refine isConj_iff.mpr ⟨⟨π * ρ, Perm.mem_alternatingGroup.mpr ?_⟩, Subtype.ext ?_⟩
    · rw [map_mul, h, hρ, Int.units_mul_self]
    · show π * ρ * (σ : Perm α) * (π * ρ)⁻¹ = τ
      rw [← hπ, mul_inv_rev, mul_assoc π ρ, hρσ.eq, ← mul_assoc π, mul_assoc _ ρ,
        mul_inv_cancel_left]

end CFSG.ProperTwoGeneratedCore.Lemma37
