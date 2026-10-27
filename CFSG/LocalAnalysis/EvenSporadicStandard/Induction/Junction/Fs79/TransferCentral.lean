module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup

theorem mem_commutator_of_central_perfect {A : Type} [Group A] [Finite A] [Group.IsPerfect A]
    {H : Subgroup A} (hH : Odd H.index) {z : A} (hz : z ∈ center A) (hzH : z ∈ H)
    (hz2 : z ^ 2 = 1) : (⟨z, hzH⟩ : H) ∈ commutator H := by
  have key : ∀ (k : ℕ) (g₀ : A), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k :=
    fun k g₀ _ => by
      rw [mul_assoc, ← Subgroup.mem_center_iff.1 (pow_mem hz k) g₀, inv_mul_cancel_left]
  have h1 := MonoidHom.transfer_eq_pow (Abelianization.of : H →* Abelianization H) z key
  have hV : MonoidHom.transfer (Abelianization.of : H →* Abelianization H) z = 1 :=
    MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker _ Group.IsPerfect.mem_commutator)
  have hpow : z ^ H.index = z := by
    obtain ⟨m, hm⟩ := hH
    rw [hm, pow_succ, pow_mul, hz2, one_pow, one_mul]
  have h2 : (Abelianization.of : H →* Abelianization H) ⟨z, hzH⟩ = 1 := by
    rw [hV] at h1
    have : (⟨z ^ H.index, pow_mem hzH _⟩ : H) = ⟨z, hzH⟩ := Subtype.ext hpow
    rw [← this]
    exact h1.symm
  rw [← Abelianization.ker_of]
  exact h2

end CFSG.EvenSporadicStandard.Induction.Junction
