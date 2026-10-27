module

public import CFSG.GH74.Uniqueness.SU.SU13TA0

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA

open Subgroup

namespace TwoCover

variable {H : Type} [Group H] {n : ℕ} {π : H →* alternatingGroup (Fin n)}

theorem exists_z (hπ : TwoCover π) :
    ∃ z : H, z ∈ center H ∧ z ≠ 1 ∧ z ^ 2 = 1 ∧ ∀ k ∈ π.ker, k = 1 ∨ k = z := by
  have h2 : Nat.card π.ker = 2 := hπ.card_ker
  obtain ⟨z, hz1, hzu⟩ := (Nat.card_eq_two_iff' (1 : π.ker)).mp h2
  refine ⟨z.1, hπ.ker_le_center z.2, fun h => hz1 (Subtype.ext h), ?_, fun k hk => ?_⟩
  · have hmem : (z.1 ^ 2 : H) ∈ π.ker := π.ker.pow_mem z.2 2
    by_contra hne
    have h3 : (⟨z.1 ^ 2, hmem⟩ : π.ker) ≠ 1 := fun h => hne (congrArg Subtype.val h)
    have h4 : (⟨z.1 ^ 2, hmem⟩ : π.ker) = z := hzu _ h3
    have h5 : z.1 ^ 2 = z.1 := congrArg Subtype.val h4
    apply hz1
    apply Subtype.ext
    have : z.1 * z.1 = z.1 * 1 := by rw [← pow_two, h5, mul_one]
    exact mul_left_cancel this
  · by_cases hk1 : k = 1
    · exact Or.inl hk1
    · right
      have h3 : (⟨k, hk⟩ : π.ker) ≠ 1 := fun h => hk1 (congrArg Subtype.val h)
      exact congrArg Subtype.val (hzu _ h3)

theorem center_eq_ker (hπ : TwoCover π) (hn : 5 ≤ n) : center H = π.ker := by
  refine le_antisymm (fun x hx => ?_) hπ.ker_le_center
  have hc : π x ∈ center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hπ.surj g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  rw [alternatingGroup.center_eq_bot (by simp; omega)] at hc
  exact Subgroup.mem_bot.mp hc

theorem card (hπ : TwoCover π) : Nat.card H = 2 * Nat.card (alternatingGroup (Fin n)) := by
  have h := Subgroup.card_ker_mul_card_range π
  have hr : π.range = ⊤ := MonoidHom.range_eq_top.mpr hπ.surj
  rw [hr, Subgroup.card_top, hπ.card_ker] at h
  exact h.symm

end TwoCover

end CFSG.GH74.Uniqueness.SU.SU13.TA
