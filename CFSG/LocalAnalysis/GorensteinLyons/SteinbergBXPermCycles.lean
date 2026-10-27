module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Order.SupIndep

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Equiv Equiv.Perm Subgroup

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_conj_pow_support {c : Perm α} (hc : c.IsCycle) {m : ℕ}
    (hm : m.Coprime (orderOf c)) :
    ∃ h : Perm α, h * c * h⁻¹ = c ^ m ∧ ∀ x ∉ c.support, h x = x := by
  have hcm : (c ^ m).IsCycle := hc.pow_iff.mpr hm
  have hsupp : (c ^ m).support = c.support := support_pow_coprime hm
  obtain ⟨h₀, hh₀⟩ := isConj_iff.mp (hc.isConj hcm (by rw [hsupp]))
  have hmap : c.support.map h₀.toEmbedding = c.support := by
    rw [← support_conj, hh₀, hsupp]
  have hmem : ∀ x, h₀ x ∈ c.support ↔ x ∈ c.support := by
    intro x
    conv_lhs => rw [← hmap]
    exact Finset.mem_map' h₀.toEmbedding
  set h : Perm α := ofSubtype (h₀.subtypePerm hmem) with hh
  have happ : ∀ x, h x = if x ∈ c.support then h₀ x else x := by
    intro x
    split_ifs with hx
    · rw [hh, ofSubtype_apply_of_mem _ hx, subtypePerm_apply]
    · rw [hh, ofSubtype_apply_of_not_mem _ hx]
  have hhi : ∀ y, h₀ (h₀⁻¹ y) = y := fun y => Equiv.apply_symm_apply h₀ y
  refine ⟨h, ?_, fun x hx => by rw [happ, ite_eq_right hx]⟩
  ext x
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hx : x ∈ c.support
  ·
    have hy : h₀⁻¹ x ∈ c.support := by
      rw [← hmem, hhi]; exact hx
    have hinv : h⁻¹ x = h₀⁻¹ x := by
      rw [Perm.inv_eq_iff_eq, happ, ite_eq_left hy, hhi]
    have hcy : c (h₀⁻¹ x) ∈ c.support := apply_mem_support.mpr hy
    rw [hinv, happ, ite_eq_left hcy, ← hh₀, Perm.mul_apply, Perm.mul_apply]
  · have hinv : h⁻¹ x = x := by rw [Perm.inv_eq_iff_eq, happ, ite_eq_right hx]
    have hcx : c x = x := notMem_support.mp hx
    have hcmx : (c ^ m) x = x := by rw [← notMem_support, hsupp]; exact hx
    rw [hinv, hcx, happ, ite_eq_right hx, hcmx]

omit [Fintype α] in
theorem commute_of_apply_eq_self {σ τ : Perm α} {s t : Finset α} (hst : Disjoint s t)
    (hσ : ∀ x ∉ s, σ x = x) (hτ : ∀ x ∉ t, τ x = x) : Commute σ τ := by
  refine Disjoint.commute fun x => ?_
  by_cases hx : x ∈ s
  · exact Or.inr (hτ x (Finset.disjoint_left.mp hst hx))
  · exact Or.inl (hσ x hx)

omit [Fintype α] in
theorem iSupIndep_zpowers_of_apply_eq_self {G : Type*} [Group G] {ι : Type*} (ρ : G →* Perm α)
    (hρ : Function.Injective ρ) (c : ι → G) (Ω : ι → Finset α)
    (hdisj : Pairwise fun i j => Disjoint (Ω i) (Ω j)) (hsupp : ∀ i, ∀ x ∉ Ω i, ρ (c i) x = x) :
    iSupIndep fun i => zpowers (c i) := by
  rw [iSupIndep_def]
  intro i
  rw [disjoint_def]
  intro x hx hx'
  let F : Subgroup G := (fixingSubgroup (Perm α) ((Ω i : Finset α) : Set α)).comap ρ
  have hF : ∀ {y : G}, y ∈ F ↔ ∀ z ∈ Ω i, ρ y z = z := by
    intro y
    simp only [F, mem_comap, mem_fixingSubgroup_iff, Finset.mem_coe, Perm.smul_def]
  have hle : (⨆ (j) (_ : j ≠ i), zpowers (c j)) ≤ F := by
    refine iSup₂_le fun j hj => ?_
    rw [zpowers_le, hF]
    intro z hz
    exact hsupp j z (Finset.disjoint_left.mp (hdisj hj.symm) hz)
  have hxF := hF.mp (hle hx')
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
  apply hρ
  rw [map_one]
  ext z
  rw [Perm.one_apply, map_zpow]
  by_cases hz : z ∈ Ω i
  · rw [← map_zpow]; exact hxF z hz
  · exact zpow_apply_eq_self_of_apply_eq_self (hsupp i z hz) m

end CFSG.LocalAnalysis.GorensteinLyons
