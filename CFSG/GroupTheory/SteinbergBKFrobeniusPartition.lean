module

public import CFSG.GroupTheory.SteinbergBKCosetConjugacy
public import Mathlib.GroupTheory.Complement
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory.SteinbergBK

variable {G : Type*} [Group G]

theorem frobenius_complement_partition [Finite G] {K R : Subgroup G} [K.Normal]
    (hKR : K.IsComplement' R) (hfix : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k * r = r * k → k = 1) :
    (K : Set G) ∪ ⋃ a ∈ K, (fun r => a⁻¹ * r * a) '' ((R : Set G) \ {1}) = Set.univ ∧
      (∀ a ∈ K, Disjoint (K : Set G) ((fun r => a⁻¹ * r * a) '' ((R : Set G) \ {1}))) ∧
      (K : Set G).PairwiseDisjoint (fun a => (fun r => a⁻¹ * r * a) '' ((R : Set G) \ {1})) := by
  have hKRd : ∀ x ∈ K, x ∈ R → x = 1 := fun x hxK hxR =>
    Subgroup.disjoint_def.mp hKR.disjoint hxK hxR
  refine ⟨Set.eq_univ_of_forall fun g => ?_, fun a ha => ?_, fun a ha b hb hab => ?_⟩
  · obtain ⟨⟨⟨k, hk⟩, ⟨r, hr⟩⟩, hkr⟩ := hKR.2 g
    simp only at hkr
    by_cases hr1 : r = 1
    · left
      rw [← hkr, hr1, mul_one]
      exact hk
    · right
      have hcc := (fixed_point_free_coset_conjugacy (H := K) (e := r)
        (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top r) (hfix r hr hr1)).2
      have hg : g ∈ {x | ∃ h ∈ K, h * r = x} := ⟨k, hk, hkr⟩
      rw [← hcc] at hg
      obtain ⟨a, ha, hag⟩ := hg
      exact Set.mem_biUnion ha ⟨r, ⟨hr, hr1⟩, hag⟩
  · rw [Set.disjoint_right]
    rintro _ ⟨r, ⟨hr, hr1⟩, rfl⟩ hK
    have hrK : r ∈ K := by
      have h := Subgroup.Normal.conj_mem inferInstance _ hK a
      rwa [show a * (a⁻¹ * r * a) * a⁻¹ = r by group] at h
    exact hr1 (hKRd r hrK hr)
  · rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨r, ⟨hr, hr1⟩, rfl⟩ ⟨s, ⟨hs, -⟩, hsr⟩
    have hr1' : r ≠ 1 := hr1
    have hsr : b⁻¹ * s * b = a⁻¹ * r * a := hsr
    have hc : b * a⁻¹ ∈ K := mul_mem (SetLike.mem_coe.mp hb) (inv_mem (SetLike.mem_coe.mp ha))
    have hs' : s = (b * a⁻¹) * r * (b * a⁻¹)⁻¹ := by
      calc s = b * (b⁻¹ * s * b) * b⁻¹ := by group
        _ = b * (a⁻¹ * r * a) * b⁻¹ := by rw [hsr]
        _ = (b * a⁻¹) * r * (b * a⁻¹)⁻¹ := by group
    have hsr1 : s * r⁻¹ = 1 := by
      refine hKRd _ ?_ (mul_mem hs (inv_mem hr))
      rw [hs', show (b * a⁻¹) * r * (b * a⁻¹)⁻¹ * r⁻¹ =
        (b * a⁻¹) * (r * (b * a⁻¹)⁻¹ * r⁻¹) by group]
      exact mul_mem hc (Subgroup.Normal.conj_mem inferInstance _ (inv_mem hc) r)
    have hsr2 : s = r := mul_inv_eq_one.mp hsr1
    have hcomm : (b * a⁻¹) * r = r * (b * a⁻¹) := by
      calc (b * a⁻¹) * r = (b * a⁻¹) * r * (b * a⁻¹)⁻¹ * (b * a⁻¹) := by group
        _ = r * (b * a⁻¹) := by rw [← hs', hsr2]
    apply hab
    have h1 := hfix r hr hr1' _ hc hcomm
    rw [mul_inv_eq_one] at h1
    exact h1.symm

end CFSG.GroupTheory.SteinbergBK
