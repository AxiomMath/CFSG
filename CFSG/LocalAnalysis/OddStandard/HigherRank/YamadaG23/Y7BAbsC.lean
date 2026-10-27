module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

private theorem mem_normalizer_of_forall_conj_mem' {H : Subgroup G} [Finite H] {x : G}
    (key : ∀ y ∈ H, x * y * x⁻¹ ∈ H) : x ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key y, fun hy => ?_⟩
  let f : H → H := fun z => ⟨x * z * x⁻¹, key z z.2⟩
  have hf : Function.Injective f := fun z z' hzz' => Subtype.ext (by
    have := congrArg Subtype.val hzz'
    simpa [f] using this)
  obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.mp hf) ⟨x * y * x⁻¹, hy⟩
  have hzy : (z : G) = y := by
    have hval : x * (z : G) * x⁻¹ = x * y * x⁻¹ := by
      have := congrArg Subtype.val hz
      simpa [f] using this
    exact mul_left_cancel (mul_right_cancel hval)
  exact hzy ▸ z.2

theorem comm_mem_of_relIndex_two [Finite G] {W M : Subgroup G} {x : G} (hMW : M ≤ W)
    (h2 : M.relIndex W = 2) (hxW : ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    (hxM : ∀ m ∈ M, x * m * x⁻¹ ∈ M) : ∀ w ∈ W, ⁅x, w⁆ ∈ M := by
  have hxM' : x ∈ normalizer (M : Set G) := mem_normalizer_of_forall_conj_mem' hxM
  have hidx : (M.subgroupOf W).index = 2 := h2
  intro w hw
  have hxw : x * w * x⁻¹ ∈ W := hxW w hw
  by_cases hwM : w ∈ M
  · rw [commutatorElement_def]
    exact M.mul_mem ((Subgroup.mem_normalizer_iff.mp hxM' w).mp hwM) (M.inv_mem hwM)
  · have hxwM : x * w * x⁻¹ ∉ M :=
      fun h1 => hwM ((Subgroup.mem_normalizer_iff.mp hxM' w).mpr h1)
    have hmem := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x * w * x⁻¹, hxw⟩)
      (b := ⟨w⁻¹, W.inv_mem hw⟩)).mpr
      ⟨fun h1 => absurd h1 hxwM, fun h1 => absurd (by simpa using M.inv_mem h1) hwM⟩
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa [commutatorElement_def] using hmem

theorem comm_mem_of_comm_mul_eq_one {A' B' M : Subgroup G} {x y t : G} (hMA : M ≤ A')
    (hMB : M ≤ B') (hAB : ∀ g ∈ A', g ∈ B' → g ∈ M) (hxB : ∀ b ∈ B', ⁅x, b⁆ ∈ M)
    (hxM : ∀ m ∈ M, x⁻¹ * m * x ∈ M) (hxt : ⁅x, t⁆ ∈ A') (hyt : ⁅y, t⁆ ∈ B')
    (h : ⁅x * y, t⁆ = 1) : ⁅x, t⁆ ∈ M ∧ ⁅y, t⁆ ∈ M := by
  have hcomm : ⁅x * y, t⁆ = x * ⁅y, t⁆ * x⁻¹ * ⁅x, t⁆ := by
    simp only [commutatorElement_def]; group
  have h1 : x * ⁅y, t⁆ * x⁻¹ * ⁅x, t⁆ = 1 := by
    rw [hcomm] at h
    exact h
  have hxt_eq : ⁅x, t⁆ = (x * ⁅y, t⁆ * x⁻¹)⁻¹ := by
    calc ⁅x, t⁆ = (x * ⁅y, t⁆ * x⁻¹)⁻¹ * (x * ⁅y, t⁆ * x⁻¹ * ⁅x, t⁆) := by group
      _ = (x * ⁅y, t⁆ * x⁻¹)⁻¹ * 1 := by rw [h1]
      _ = (x * ⁅y, t⁆ * x⁻¹)⁻¹ := by group
  have hxbb : x * ⁅y, t⁆ * x⁻¹ = ⁅x, ⁅y, t⁆⁆ * ⁅y, t⁆ := by
    simp only [commutatorElement_def]; group
  have hd_B : x * ⁅y, t⁆ * x⁻¹ ∈ B' := by
    rw [hxbb]
    exact B'.mul_mem (hMB (hxB _ hyt)) hyt
  have hxt_B : ⁅x, t⁆ ∈ B' := by
    rw [hxt_eq]
    exact B'.inv_mem hd_B
  have hxt_M : ⁅x, t⁆ ∈ M := hAB _ hxt hxt_B
  have hd_eq : x * ⁅y, t⁆ * x⁻¹ = ⁅x, t⁆⁻¹ := by
    rw [hxt_eq]; group
  have hd_M : x * ⁅y, t⁆ * x⁻¹ ∈ M := by
    rw [hd_eq]
    exact M.inv_mem hxt_M
  have hyt_M : ⁅y, t⁆ ∈ M := by
    have := hxM _ hd_M
    rwa [show x⁻¹ * (x * ⁅y, t⁆ * x⁻¹) * x = ⁅y, t⁆ by group] at this
  exact ⟨hxt_M, hyt_M⟩

theorem inf_sup_sup_eq_of_normalizes {A B M : Subgroup G}
    (hA : ∀ a ∈ A, ∀ m ∈ M, a * m * a⁻¹ ∈ M) (hB : ∀ b ∈ B, ∀ m ∈ M, b * m * b⁻¹ ∈ M)
    (h : ∀ a ∈ A, a ∈ B ⊔ M → a ∈ M) : (A ⊔ M) ⊓ (B ⊔ M) = M := by
  have hA' : A ≤ normalizer (M : Set G) := Subgroup.le_normalizer_iff.mpr hA
  have hB' : B ≤ normalizer (M : Set G) := Subgroup.le_normalizer_iff.mpr hB
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxA, hxB⟩ := hx
    have hxA' : x ∈ (A : Set G) * (M : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A M hA']; exact hxA
    have hxB' : x ∈ (B : Set G) * (M : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right B M hB']; exact hxB
    rw [Set.mem_mul] at hxA' hxB'
    obtain ⟨a, haA, m, hmM, hx1⟩ := hxA'
    obtain ⟨b, hbB, m', hm'M, hx2⟩ := hxB'
    have ha_eq : a = b * m' * m⁻¹ := by
      have h1 : a * m = b * m' := hx1.trans hx2.symm
      calc a = a * m * m⁻¹ := by group
        _ = b * m' * m⁻¹ := by rw [h1]
    have haBM : a ∈ B ⊔ M := by
      have hmem : a ∈ (B : Set G) * (M : Set G) :=
        ⟨b, hbB, m' * m⁻¹, M.mul_mem hm'M (M.inv_mem hmM), by rw [ha_eq]; group⟩
      rwa [← Subgroup.coe_mul_of_left_le_normalizer_right B M hB'] at hmem
    exact hx1 ▸ M.mul_mem (h a haA haBM) hmM
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hx, Subgroup.mem_sup_right hx⟩

end CFSG.OddStandard.HigherRank.YamadaG23
