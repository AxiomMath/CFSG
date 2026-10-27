module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open DihedralGroup

theorem dihGen_zmod8_two : ∀ i : ZMod 8, i + i = 0 → i ≠ 0 → i = 4 := by
  decide

theorem dihGen_zmod8_sub : ∀ k : ZMod 8, k - 1 ≠ k + 1 := by
  decide

theorem dihGen_r_invol {i : ZMod 8} (h : r i * r i = 1) (h1 : r i ≠ 1) : r i = r 4 := by
  have hi : i + i = 0 := by
    rw [r_mul_r, ← r_zero] at h
    exact r.inj h
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact h1 r_zero
  rw [dihGen_zmod8_two i hi hi0]

theorem dihGen_central_invol {y : DihedralGroup 8} (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hyc : ∀ w : DihedralGroup 8, w * y = y * w) : y = r 4 := by
  cases y with
  | r i => exact dihGen_r_invol hy2 hy1
  | sr k =>
    exfalso
    have h : sr (k - 1) = sr (k + 1) := by
      have h0 := hyc (r 1)
      rwa [r_mul_sr, sr_mul_r] at h0
    exact dihGen_zmod8_sub k (sr.inj h)

theorem dihGen_refl {x : DihedralGroup 8} (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx4 : x ≠ r 4) :
    ∃ k : ZMod 8, x = sr k := by
  cases x with
  | r i => exact absurd (dihGen_r_invol hx2 hx1) hx4
  | sr k => exact ⟨k, rfl⟩

theorem dihGen_finite (x y : DihedralGroup 8) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hy2 : y * y = 1)
    (hy1 : y ≠ 1) (hyc : ∀ w : DihedralGroup 8, w * y = y * w) (hxy : x ≠ y) :
    ∃ g : DihedralGroup 8, orderOf g = 8 ∧ x * g * x⁻¹ = g⁻¹ ∧ g ^ 4 = y ∧
      ∀ w : DihedralGroup 8, ∃ i j : ℕ, w = g ^ i * x ^ j := by
  have hy : y = r 4 := dihGen_central_invol hy2 hy1 hyc
  subst hy
  obtain ⟨k, rfl⟩ := dihGen_refl hx2 hx1 hxy
  refine ⟨r 1, orderOf_r_one, ?_, ?_, ?_⟩
  · simp only [sr_mul_r, inv_sr, sr_mul_sr, inv_r]
    congr 1
    ring
  · rw [r_one_pow]
    norm_num
  · intro w
    cases w with
    | r m => exact ⟨m.val, 0, by rw [r_one_pow, pow_zero, mul_one, ZMod.natCast_zmod_val]⟩
    | sr m =>
      refine ⟨(k - m).val, 1, ?_⟩
      rw [r_one_pow, pow_one, ZMod.natCast_zmod_val, r_mul_sr]
      congr 1
      ring

theorem exists_dihedral_gen {G : Type} [Group G] {S : Subgroup G} (e : ↥S ≃* DihedralGroup 8)
    {z t : G} (hz : z ∈ S) (ht : t ∈ S) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzt : z ≠ t)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htc : ∀ y ∈ S, y * t = t * y) :
    ∃ s : G, s ∈ S ∧ orderOf s = 8 ∧ z * s * z⁻¹ = s⁻¹ ∧ s ^ 4 = t ∧
      ∀ y ∈ S, ∃ i j : ℕ, y = s ^ i * z ^ j := by
  obtain ⟨x, hx⟩ : ∃ x : DihedralGroup 8, x = e ⟨z, hz⟩ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : DihedralGroup 8, y = e ⟨t, ht⟩ := ⟨_, rfl⟩
  have hx2 : x * x = 1 := by
    have h : (⟨z, hz⟩ : ↥S) * ⟨z, hz⟩ = 1 := Subtype.ext (by simpa using hz2)
    rw [hx, ← map_mul, h, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    apply hz1
    have h' : e ⟨z, hz⟩ = e 1 := by rw [map_one, ← hx, h]
    simpa using congrArg Subtype.val (e.injective h')
  have hy2 : y * y = 1 := by
    have h : (⟨t, ht⟩ : ↥S) * ⟨t, ht⟩ = 1 := Subtype.ext (by simpa using ht2)
    rw [hy, ← map_mul, h, map_one]
  have hy1 : y ≠ 1 := by
    intro h
    apply ht1
    have h' : e ⟨t, ht⟩ = e 1 := by rw [map_one, ← hy, h]
    simpa using congrArg Subtype.val (e.injective h')
  have hxy : x ≠ y := by
    intro h
    apply hzt
    have h' : e ⟨z, hz⟩ = e ⟨t, ht⟩ := by rw [← hx, ← hy, h]
    simpa using congrArg Subtype.val (e.injective h')
  have hyc : ∀ w : DihedralGroup 8, w * y = y * w := by
    intro w
    obtain ⟨a, rfl⟩ := e.surjective w
    rw [hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using htc a.1 a.2)
  obtain ⟨g, hg8, hgx, hg4, hgen⟩ := dihGen_finite x y hx2 hx1 hy2 hy1 hyc hxy
  obtain ⟨a, rfl⟩ := e.surjective g
  refine ⟨(a : G), a.2, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e]
    exact hg8
  · have key : (⟨z, hz⟩ : ↥S) * a * (⟨z, hz⟩ : ↥S)⁻¹ = a⁻¹ := by
      refine e.injective ?_
      rw [map_mul, map_mul, map_inv, map_inv, ← hx]
      exact hgx
    simpa using congrArg Subtype.val key
  · have key : a ^ 4 = (⟨t, ht⟩ : ↥S) := by
      refine e.injective ?_
      rw [map_pow]
      exact hg4.trans hy
    simpa using congrArg Subtype.val key
  · intro c hc
    obtain ⟨i, j, hij⟩ := hgen (e ⟨c, hc⟩)
    have key : (⟨c, hc⟩ : ↥S) = a ^ i * (⟨z, hz⟩ : ↥S) ^ j := by
      refine e.injective ?_
      rw [hij, map_mul, map_pow, map_pow, hx]
    refine ⟨i, j, ?_⟩
    simpa using congrArg Subtype.val key

end CFSG.EvenSporadicStandard.Fin76b
