module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {N G : Type*} [Group N] [Group G] (π : N →* G)

theorem sec4P4_isPGroup_ker (h2 : ∀ k ∈ π.ker, k ^ 2 = 1) : IsPGroup 2 π.ker := fun k =>
  ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, h2 k k.2])⟩

theorem sec4P4_sq_eq_of_map_eq (hC : π.ker ≤ Subgroup.center N) (h2 : ∀ k ∈ π.ker, k ^ 2 = 1)
    {x y : N} (h : π x = π y) : x ^ 2 = y ^ 2 := by
  have hk : x⁻¹ * y ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hc : Commute x (x⁻¹ * y) := Subgroup.mem_center_iff.mp (hC hk) x
  have hy : y = x * (x⁻¹ * y) := by rw [mul_inv_cancel_left]
  rw [hy, hc.mul_pow, h2 _ hk, mul_one]

theorem sec4P4_sq_eq_one_of_map_conj (hC : π.ker ≤ Subgroup.center N)
    (h2 : ∀ k ∈ π.ker, k ^ 2 = 1) {z w y : N} (hy : π y = π (w * z * w⁻¹)) (hy2 : y ^ 2 = 1) :
    z ^ 2 = 1 := by
  have h := sec4P4_sq_eq_of_map_eq π hC h2 hy
  rw [hy2, conj_pow] at h
  exact conj_eq_one_iff.mp h.symm

theorem sec4P4_compl_of_section {s : G →* N} (hs : ∀ x, π (s x) = x) :
    s.range ⊓ π.ker = ⊥ ∧ s.range ⊔ π.ker = ⊤ := by
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    rintro g ⟨⟨a, rfl⟩, hker⟩
    have ha : a = 1 := by
      rw [← hs a]
      exact hker
    rw [Subgroup.mem_bot, ha, map_one]
  · rw [eq_top_iff]
    intro g _
    have h1 : s (π g) ∈ s.range := ⟨π g, rfl⟩
    have h2 : (s (π g))⁻¹ * g ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
    have h3 := Subgroup.mul_mem_sup h1 h2
    rwa [mul_inv_cancel_left] at h3

end CFSG.OddStandard.SmallF3.Omega
