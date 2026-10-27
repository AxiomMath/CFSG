module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S4CETool

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem commutatorElement_eq_one_of_inv {x y t : G} (hc : ⁅x, y⁆ ∈ center G)
    (htx : t * x * t⁻¹ = x) (hty : t * y * t⁻¹ = y⁻¹) (hy : y ^ 3 = 1) : ⁅x, y⁆ = 1 := by
  set c := ⁅x, y⁆ with hcdef
  have hcc := mem_center_iff.mp hc
  have hxy : x * y * x⁻¹ = c * y := by
    rw [hcdef, commutatorElement_def]
    group
  have h1 : t * c * t⁻¹ = c := by rw [hcc t, mul_inv_cancel_right]
  have h2 : t * c * t⁻¹ = c⁻¹ := by
    have e : t * c * t⁻¹ =
        (t * x * t⁻¹) * (t * y * t⁻¹) * (t * x * t⁻¹)⁻¹ * (t * y * t⁻¹)⁻¹ := by
      rw [hcdef, commutatorElement_def]
      group
    have e2 : x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
    rw [e, htx, hty, inv_inv, e2, hxy, mul_inv_rev, mul_assoc,
      ← mem_center_iff.mp (inv_mem hc) y, inv_mul_cancel_left]
  have h3 : c ^ 3 = 1 := by
    have e : (x * y * x⁻¹) ^ 3 = x * y ^ 3 * x⁻¹ := conj_pow
    have hcy : Commute c y := (show Commute y c from hcc y).symm
    rw [hy, mul_one, mul_inv_cancel, hxy, hcy.mul_pow, hy, mul_one] at e
    exact e
  have h4 : c * c = 1 := by
    have : c = c⁻¹ := h1.symm.trans h2
    calc c * c = c⁻¹ * c := by rw [← this]
      _ = 1 := inv_mul_cancel c
  calc c = c ^ 3 * (c * c)⁻¹ := by group
    _ = 1 := by rw [h3, h4, inv_one, mul_one]

theorem zpowers_le_normalizer_of_conj {x y : G} {k l : ℤ} (h1 : x * y * x⁻¹ = y ^ k)
    (h2 : x⁻¹ * y * x = y ^ l) : zpowers x ≤ normalizer (zpowers y : Set G) := by
  rw [zpowers_le]
  refine mem_normalizer_iff.mpr fun g => ⟨fun hg => ?_, fun hg => ?_⟩
  · obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
    rw [← conj_zpow, h1, ← zpow_mul]
    exact zpow_mem (mem_zpowers y) _
  · obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hg
    have e : g = x⁻¹ * y ^ n * x⁻¹⁻¹ := by
      rw [hn]
      group
    rw [e, ← conj_zpow, inv_inv, h2, ← zpow_mul]
    exact zpow_mem (mem_zpowers y) _

theorem zpowers_le_normalizer_of_commute {x y : G} (h : x * y = y * x) :
    zpowers x ≤ normalizer (zpowers y : Set G) :=
  zpowers_le_normalizer_of_conj (k := 1) (l := 1) (by rw [h, mul_inv_cancel_right, zpow_one])
    (by rw [mul_assoc, ← h, inv_mul_cancel_left, zpow_one])

theorem zpowers_le_normalizer_of_inv {t y : G} (ht : t * t = 1) (h : t * y * t⁻¹ = y⁻¹) :
    zpowers t ≤ normalizer (zpowers y : Set G) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  exact zpowers_le_normalizer_of_conj (k := -1) (l := -1) (by rw [h, zpow_neg_one])
    (by rw [show t⁻¹ * y * t = t * y * t⁻¹ by rw [hti], h, zpow_neg_one])

end Group

namespace CEHyp

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {K : Type*} [Group K]
  {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V} {X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
  (h : CEHyp π E a X E₀)
include h

theorem exists_lift_of_inv {t y : K} (ht : t * t = 1) (hy3 : π y ^ 3 = 1)
    (hinv : π t * π y * (π t)⁻¹ = (π y)⁻¹) :
    ∃ w : K, w ^ 3 = 1 ∧ t * w * t⁻¹ = w⁻¹ ∧ π w = π y ^ 2 := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set y₀ := y * (t * y * t⁻¹)⁻¹ with hy₀
  have hty₀ : t * y₀ * t⁻¹ = y₀⁻¹ := by
    have e1 : t * y₀ * t⁻¹ = (t * y * t⁻¹) * (t * (t * y * t⁻¹) * t⁻¹)⁻¹ := by
      rw [hy₀]
      group
    have e2 : t * (t * y * t⁻¹) * t⁻¹ = y := by
      calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
        _ = y := by rw [ht, one_mul, inv_one, mul_one]
    rw [e1, e2, hy₀, mul_inv_rev, inv_inv]
  have hπy₀ : π y₀ = π y ^ 2 := by
    rw [hy₀, map_mul, map_inv, map_mul, map_mul, map_inv, hinv, inv_inv, pow_two]
  have hz : y₀ ^ 3 ∈ center K := h.mem_center_of_mem_ker (by
    rw [map_pow, hπy₀, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hy3, one_pow])
  have h6 : y₀ ^ 6 = 1 := by
    have e1 : t * y₀ ^ 3 * t⁻¹ = (y₀ ^ 3)⁻¹ := by rw [← conj_pow, hty₀, inv_pow]
    have e2 : t * y₀ ^ 3 * t⁻¹ = y₀ ^ 3 := by
      rw [mem_center_iff.mp hz t, mul_inv_cancel_right]
    have e3 : y₀ ^ 3 = (y₀ ^ 3)⁻¹ := e2.symm.trans e1
    calc y₀ ^ 6 = y₀ ^ 3 * y₀ ^ 3 := by rw [← pow_add]
      _ = 1 := by
        nth_rw 2 [e3]
        exact mul_inv_cancel _
  refine ⟨y₀ ^ 4, ?_, ?_, ?_⟩
  · rw [← pow_mul, show 4 * 3 = 6 * 2 by rfl, pow_mul, h6, one_pow]
  · rw [← conj_pow, hty₀, inv_pow]
  · rw [map_pow, hπy₀, ← pow_mul, show 2 * 4 = 3 * 2 + 2 by rfl, pow_add, pow_mul, hy3,
      one_pow, one_mul]

end CEHyp

end CFSG.LargeExtraspecial.S4
