module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.HarrisEnd

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem dihedral_eq_r_of_sq_ne_one {n : ℕ} {g : DihedralGroup n} (hg : g ^ 2 ≠ 1) :
    ∃ k, g = DihedralGroup.r k := by
  rcases g with k | k
  · exact ⟨k, rfl⟩
  · exfalso
    apply hg
    rw [sq, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.one_def]

theorem commute_of_sq_ne_one {D A : Subgroup G} {n : ℕ} (eD : ↥D ≃* DihedralGroup n)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAD : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a)
    (hAA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {x y : G}
    (hx : x ∈ D ⊔ A) (hy : y ∈ D ⊔ A) (hx2 : x ^ 2 ≠ 1) (hy2 : y ^ 2 ≠ 1) : x * y = y * x := by
  have hAn : A ≤ normalizer (D : Set G) := fun a ha => by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => ?_)
    exact (hAD a ha y hy).symm
  have hdec : ∀ g ∈ D ⊔ A, ∃ d ∈ D, ∃ a ∈ A, g = d * a := by
    intro g hg
    have hg' : g ∈ ((D : Set G) * (A : Set G)) := by
      rw [← coe_mul_of_right_le_normalizer_left D A hAn]
      exact hg
    obtain ⟨d, hd, a, ha, rfl⟩ := hg'
    exact ⟨d, hd, a, ha, rfl⟩
  obtain ⟨d₁, hd₁, a₁, ha₁, rfl⟩ := hdec x hx
  obtain ⟨d₂, hd₂, a₂, ha₂, rfl⟩ := hdec y hy
  have hsq : ∀ d a, d ∈ D → a ∈ A → (d * a) ^ 2 = d ^ 2 := fun d a hd ha => by
    rw [(show Commute d a from (hAD a ha d hd).symm).mul_pow, hA2 a ha, mul_one]
  rw [hsq _ _ hd₁ ha₁] at hx2
  rw [hsq _ _ hd₂ ha₂] at hy2
  have hr : ∀ {d : G} (hd : d ∈ D), d ^ 2 ≠ 1 → ∃ k, eD ⟨d, hd⟩ = DihedralGroup.r k := by
    intro d hd h2
    refine dihedral_eq_r_of_sq_ne_one fun h => h2 ?_
    have : (⟨d, hd⟩ : ↥D) ^ 2 = 1 := eD.injective (by rw [map_pow, h, map_one])
    simpa using congrArg Subtype.val this
  obtain ⟨k₁, hk₁⟩ := hr hd₁ hx2
  obtain ⟨k₂, hk₂⟩ := hr hd₂ hy2
  have hcomm : d₁ * d₂ = d₂ * d₁ := by
    have : (⟨d₁, hd₁⟩ : ↥D) * ⟨d₂, hd₂⟩ = ⟨d₂, hd₂⟩ * ⟨d₁, hd₁⟩ := eD.injective (by
      rw [map_mul, map_mul, hk₁, hk₂, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm])
    simpa using congrArg Subtype.val this
  have c1 : Commute d₁ (d₂ * a₂) := (show Commute d₁ d₂ from hcomm).mul_right
    (show Commute d₁ a₂ from (hAD a₂ ha₂ d₁ hd₁).symm)
  have c2 : Commute a₁ (d₂ * a₂) := (show Commute a₁ d₂ from hAD a₁ ha₁ d₂ hd₂).mul_right
    (show Commute a₁ a₂ from hAA a₁ ha₁ a₂ ha₂)
  exact (c1.mul_left c2).eq

end CFSG.ComponentClassification.HarrisLit.HarrisEnd
