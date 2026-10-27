module

public import CFSG.Certificates.Kernel.TwistDce2.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.Certificates.TwDce.TwistData

variable {G : Type*} [Group G] {H C : Subgroup G} {u : G} {r : ℕ}

theorem exists_pow_eq_one (D : TwistData H C u r) (huC : ∀ c ∈ C, u⁻¹ * c * u ∈ H) [Finite H] :
    ∃ n, 0 < n ∧ u ^ n = 1 := by
  let f : Fin r × H × H → G := fun p => (p.2.1 : G) * D.x p.1 * p.2.2
  have hmem : ∀ m : ℕ, u ^ m ∈ Set.range f := by
    intro m
    have h1 : ∃ i : Fin r, ∃ a ∈ H, ∃ b ∈ H, (1 : G) = a * D.x i * b :=
      ⟨D.base, (D.x D.base)⁻¹, H.inv_mem D.base_mem, 1, H.one_mem, by group⟩
    obtain ⟨i, a, ha, b, hb, he⟩ := D.mul_pow_mem huC m h1
    rw [one_mul] at he
    exact ⟨(i, ⟨a, ha⟩, ⟨b, hb⟩), he.symm⟩
  have : Finite (Set.range f) := (Set.finite_range f).to_subtype
  have hni := not_injective_infinite_finite (fun m : ℕ => (⟨u ^ m, hmem m⟩ : Set.range f))
  simp only [Function.Injective, not_forall] at hni
  obtain ⟨i, j, he, hij⟩ := hni
  have he' : u ^ i = u ^ j := congrArg Subtype.val he
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨j - i, by omega, ?_⟩
    have h2 : u ^ i * u ^ (j - i) = u ^ i * 1 := by
      rw [mul_one, ← pow_add, Nat.add_sub_cancel' h.le, he']
    exact mul_left_cancel h2
  · refine ⟨i - j, by omega, ?_⟩
    have h2 : u ^ j * u ^ (i - j) = u ^ j * 1 := by
      rw [mul_one, ← pow_add, Nat.add_sub_cancel' h.le, he']
    exact mul_left_cancel h2

theorem index_le_sum_of_finite (D : TwistData H C u r) (huC : ∀ c ∈ C, u⁻¹ * c * u ∈ H)
    (hgen : Subgroup.closure ((H : Set G) ∪ {u}) = ⊤) [Finite H] :
    H.FiniteIndex ∧ H.index ≤ ∑ i, (D.S i).relIndex H := by
  obtain ⟨n, hn, hu⟩ := D.exists_pow_eq_one huC
  exact D.index_le_sum_of_pow hn hu huC hgen

end CFSG.Certificates.TwDce.TwistData

end
