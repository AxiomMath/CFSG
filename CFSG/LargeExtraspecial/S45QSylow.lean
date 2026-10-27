module

public import CFSG.LargeExtraspecial.S5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S45Q

open Subgroup

section PGroup

variable {G : Type*} [Group G]

theorem isPGroup_closure_pair {x y : G} (hx : x * x = 1) (hy : y * y = 1) {k : ℕ}
    (hxy : (x * y) ^ 2 ^ k = 1) : IsPGroup 2 (closure {x, y}) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hC : IsPGroup 2 (zpowers (x * y)) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hxy, one_zpow]
  have hX : IsPGroup 2 (zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_one, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, sq, hx, one_zpow]
  have hconj : ∀ h ∈ zpowers (x * y), x * h * x⁻¹ ∈ zpowers (x * y) := by
    intro h hh
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hh
    have e : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
      rw [mul_inv_rev, hxi, hyi, ← mul_assoc, hx, one_mul]
    rw [← conj_zpow, e]
    exact zpow_mem (inv_mem (mem_zpowers _)) m
  have hN : zpowers x ≤ normalizer (zpowers (x * y) : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    refine ⟨hconj h, fun hh => ?_⟩
    have := hconj _ hh
    rwa [hxi, ← mul_assoc, ← mul_assoc, hx, one_mul, mul_assoc, hx, mul_one] at this
  refine (hX.to_sup_of_normal_right' hC hN).to_le ?_
  rw [closure_le]
  intro w hw
  rcases hw with h | h
  · rw [h]
    exact mem_sup_left (mem_zpowers x)
  · have h' : w = y := h
    have e : w = x * (x * y) := by rw [← mul_assoc, hx, one_mul, h']
    rw [e]
    exact mul_mem (mem_sup_left (mem_zpowers x)) (mem_sup_right (mem_zpowers _))

end PGroup

section Sylow

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem nonabelianSylowTwo_of_mem [Finite (V ≃ₗ[ZMod 2] V)] {X : Subgroup (V ≃ₗ[ZMod 2] V)}
    {x y : V ≃ₗ[ZMod 2] V} (hxX : x ∈ X) (hyX : y ∈ X) (hx : x * x = 1) (hy : y * y = 1)
    {k : ℕ} (hxy : (x * y) ^ 2 ^ k = 1) (hne : x * y ≠ y * x) : S5.NonabelianSylowTwo X := by
  intro P hPX hP hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf X) := hP.of_equiv (subgroupOfEquivOfLe hPX).symm
  have hDX : closure {x, y} ≤ X := by
    rw [closure_le]
    intro w hw
    rcases hw with h | h
    · rw [h]
      exact hxX
    · have h' : w = y := h
      rw [h']
      exact hyX
  have hD : IsPGroup 2 ((closure {x, y}).subgroupOf X) :=
    (isPGroup_closure_pair hx hy hxy).of_equiv (subgroupOfEquivOfLe hDX).symm
  obtain ⟨T, hDT⟩ := hD.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X T (hP'.toSylow hidx)
  have key : ∀ w : X, (w : V ≃ₗ[ZMod 2] V) ∈ closure {x, y} →
      ((g * w * g⁻¹ : X) : V ≃ₗ[ZMod 2] V) ∈ P := by
    intro w hw
    have hwT : w ∈ T := hDT (mem_subgroupOf.mpr hw)
    have h1 : g * w * g⁻¹ ∈ ((g • T : Sylow 2 X) : Subgroup X) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul w (MulAut.conj g) (T : Subgroup X) hwT
    rw [hg] at h1
    exact mem_subgroupOf.mp h1
  have hxD : ((⟨x, hxX⟩ : X) : V ≃ₗ[ZMod 2] V) ∈ closure {x, y} :=
    subset_closure (Set.mem_insert x {y})
  have hyD : ((⟨y, hyX⟩ : X) : V ≃ₗ[ZMod 2] V) ∈ closure {x, y} :=
    subset_closure (Set.mem_insert_of_mem x rfl)
  refine ⟨_, key _ hxD, _, key _ hyD, fun h => hne ?_⟩
  have h2 : (g * ⟨x, hxX⟩ * g⁻¹) * (g * ⟨y, hyX⟩ * g⁻¹) =
      (g * ⟨y, hyX⟩ * g⁻¹) * (g * ⟨x, hxX⟩ * g⁻¹) := Subtype.ext (by
    simpa only [Subgroup.coe_mul] using h)
  have h3 : (⟨x, hxX⟩ : X) * ⟨y, hyX⟩ = ⟨y, hyX⟩ * ⟨x, hxX⟩ := by
    have e1 : (g * ⟨x, hxX⟩ * g⁻¹) * (g * ⟨y, hyX⟩ * g⁻¹) =
        g * ((⟨x, hxX⟩ : X) * ⟨y, hyX⟩) * g⁻¹ := by group
    have e2 : (g * ⟨y, hyX⟩ * g⁻¹) * (g * ⟨x, hxX⟩ * g⁻¹) =
        g * ((⟨y, hyX⟩ : X) * ⟨x, hxX⟩) * g⁻¹ := by group
    rw [e1, e2] at h2
    simpa using h2
  exact congrArg Subtype.val h3

end Sylow

section Index

theorem card_dvd_factorial_index {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : H ≠ ⊤) : Nat.card G ∣ H.index.factorial := by
  have hcore : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ H.normalCore_le)) hH
  have h := H.index_normalCore_dvd_factorial_index
  rwa [hcore, index_bot] at h

end Index

end CFSG.LargeExtraspecial.S45Q
