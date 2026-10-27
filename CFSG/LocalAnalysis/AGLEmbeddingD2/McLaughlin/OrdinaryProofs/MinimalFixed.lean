module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_ne_one_centralized_of_isPGroup_two [Finite G] {S N : Subgroup G}
    (hS : IsPGroup 2 S) (hSN : S ≤ Subgroup.normalizer N) (hN2 : IsPGroup 2 N)
    (hN1 : N ≠ ⊥) : ∃ x ∈ N, x ≠ 1 ∧ ∀ s ∈ S, s * x = x * s := by
  have hcl : ∀ s : S, ∀ n : N, (s : G) * (n : G) * (s : G)⁻¹ ∈ N := fun s n =>
    (Subgroup.mem_normalizer_iff.mp (hSN s.2) (n : G)).mp n.2
  let act : MulAction S N :=
    { smul := fun s n => ⟨(s : G) * (n : G) * (s : G)⁻¹, hcl s n⟩
      one_smul := fun n => Subtype.ext (by
        show (1 : G) * (n : G) * (1 : G)⁻¹ = (n : G)
        group)
      mul_smul := fun s t n => Subtype.ext (by
        show ((s : G) * (t : G)) * (n : G) * ((s : G) * (t : G))⁻¹
          = (s : G) * ((t : G) * (n : G) * (t : G)⁻¹) * (s : G)⁻¹
        group) }
  have hdvd : 2 ∣ Nat.card N := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := N)).mp hN2
    have hne : Nat.card N ≠ 1 := by
      intro h1
      exact hN1 ((Subgroup.card_eq_one).mp h1)
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hn)
    rw [hn]
    exact dvd_pow_self 2 hn0
  have h1fix : (1 : N) ∈ MulAction.fixedPoints S N := by
    rw [MulAction.mem_fixedPoints]
    intro s
    exact Subtype.ext (by
      show (s : G) * ((1 : N) : G) * (s : G)⁻¹ = ((1 : N) : G)
      simp)
  obtain ⟨b, hb, hb1⟩ :=
    hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := N) hdvd h1fix
  refine ⟨(b : G), b.2, fun h => hb1 (Subtype.ext (by simpa using h.symm)), ?_⟩
  intro s hs
  have hbs : (s : G) * (b : G) * (s : G)⁻¹ = (b : G) := congrArg Subtype.val
    ((MulAction.mem_fixedPoints.mp hb) ⟨s, hs⟩)
  exact mul_inv_eq_iff_eq_mul.mp hbs

end CFSG.AGLEmbeddingD2.McLaughlin

end
