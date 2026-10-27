module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S118D2PDih

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11d2_isElemAbelianMod_of_isD8 {C : Subgroup G} (hC : IsD8 C) {z : G} (hzC : z ∈ C)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ x ∈ C, x * z = z * x) : IsElemAbelianMod z C := by
  obtain ⟨e⟩ := hC
  set z' : ↥C := ⟨z, hzC⟩ with hz'
  have h1 : e z' * e z' = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext hz2
  have h2 : e z' ≠ 1 := fun h =>
    hz1 (by simpa [hz'] using e.injective (h.trans (map_one e).symm))
  have h3 : ∀ x : DihedralGroup 4, x * e z' = e z' * x := by
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc y y.2)
  have key : ∀ Z : DihedralGroup 4, Z * Z = 1 → Z ≠ 1 → (∀ x : DihedralGroup 4, x * Z = Z * x) →
      ∀ x y : DihedralGroup 4, (x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = Z) ∧
        (x * x = 1 ∨ x * x = Z) := by
    decide +kernel
  intro a ha b hb
  obtain ⟨hk1, hk2⟩ := key (e z') h1 h2 h3 (e ⟨a, ha⟩) (e ⟨b, hb⟩)
  refine ⟨?_, ?_⟩
  · rcases hk1 with h | h
    · have h' : (⟨a, ha⟩ : ↥C) * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ = 1 := by
        apply e.injective
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_one]
        exact h
      have h'' : a * b * a⁻¹ * b⁻¹ = 1 := congrArg Subtype.val h'
      rw [h'']
      exact Subgroup.one_mem _
    · have h' : (⟨a, ha⟩ : ↥C) * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ = z' := by
        apply e.injective
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        exact h
      have h'' : a * b * a⁻¹ * b⁻¹ = z := congrArg Subtype.val h'
      rw [h'']
      exact Subgroup.mem_zpowers z
  · rcases hk2 with h | h
    · have h' : (⟨a, ha⟩ : ↥C) * ⟨a, ha⟩ = 1 := by
        apply e.injective
        rw [map_mul, map_one]
        exact h
      have h'' : a * a = 1 := congrArg Subtype.val h'
      rw [h'']
      exact Subgroup.one_mem _
    · have h' : (⟨a, ha⟩ : ↥C) * ⟨a, ha⟩ = z' := by
        apply e.injective
        rw [map_mul]
        exact h
      have h'' : a * a = z := congrArg Subtype.val h'
      rw [h'']
      exact Subgroup.mem_zpowers z

theorem sec11d2_exists_X_of_sq [Finite G] {C D Y : Subgroup G} {z c d : G} (hCD : C ≤ D)
    (hYD : Y ≤ D) (hY : IsCyclic Y) (hYi : Y.relIndex D = 2) (hC : IsD8 C) (hzC : z ∈ C)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hcC : c ∈ C) (hcY : c ∈ Y) (hc4 : orderOf c = 4)
    (hcc : c * c = z) (hdD : d ∈ D) (hd2 : d * d = z) (hzD : ∀ x ∈ D, x * z = z * x) :
    ∃ X : Subgroup G, X ≤ D ∧ d ∈ X ∧ z ∈ X ∧ IsElemAbelianMod z X ∧ 8 ≤ Nat.card X := by
  by_cases hdc : d ∈ zpowers c
  · refine ⟨C, hCD, zpowers_le.mpr hcC hdc, hzC,
      sec11d2_isElemAbelianMod_of_isD8 hC hzC hz2 hz1 (fun x hx => hzD x (hCD hx)), ?_⟩
    exact le_of_eq (sec11_isD8_card hC).symm
  · exact sec11d2_exists_X hYD hY hYi hz2 hcY hc4 hcc hdD hd2 hzD hdc

end CFSG.OddStandard.SmallF3.Omega
