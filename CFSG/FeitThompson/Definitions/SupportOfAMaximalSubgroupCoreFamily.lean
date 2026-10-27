module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Lattice.Bounded

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G]

def coreFamilySupport (𝓜 : Set (Subgroup G)) (S : Subgroup G → Subgroup G) : Set G :=
  ⋃ M ∈ 𝓜, ((S M : Set G) \ {1})

variable {𝓜 𝓝 : Set (Subgroup G)} {S T : Subgroup G → Subgroup G}

theorem coreFamilySupport_eq_iUnion (𝓜 : Set (Subgroup G)) (S : Subgroup G → Subgroup G) :
    coreFamilySupport 𝓜 S = ⋃ M ∈ 𝓜, ((S M : Set G) \ {1}) := (rfl)

@[simp]
theorem mem_coreFamilySupport_iff {x : G} :
    x ∈ coreFamilySupport 𝓜 S ↔ ∃ M ∈ 𝓜, x ∈ S M ∧ x ≠ 1 := by
  rw [coreFamilySupport_eq_iUnion]
  simp only [Set.mem_iUnion, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff, exists_prop]

@[simp]
theorem one_notMem_coreFamilySupport : (1 : G) ∉ coreFamilySupport 𝓜 S := by
  simp

theorem sdiff_subset_coreFamilySupport {M : Subgroup G} (hM : M ∈ 𝓜) :
    (S M : Set G) \ {1} ⊆ coreFamilySupport 𝓜 S := by
  rw [coreFamilySupport_eq_iUnion]
  exact Set.subset_biUnion_of_mem (u := fun M => (S M : Set G) \ {1}) hM

@[simp]
theorem coreFamilySupport_empty (S : Subgroup G → Subgroup G) :
    coreFamilySupport (∅ : Set (Subgroup G)) S = ∅ := by
  rw [coreFamilySupport_eq_iUnion]; simp

theorem coreFamilySupport_mono (h : 𝓜 ⊆ 𝓝) :
    coreFamilySupport 𝓜 S ⊆ coreFamilySupport 𝓝 S := by
  intro x hx
  rw [mem_coreFamilySupport_iff] at hx ⊢
  obtain ⟨M, hM, hxS, hx1⟩ := hx
  exact ⟨M, h hM, hxS, hx1⟩

theorem coreFamilySupport_mono_family (h : ∀ M ∈ 𝓜, S M ≤ T M) :
    coreFamilySupport 𝓜 S ⊆ coreFamilySupport 𝓜 T := by
  intro x hx
  rw [mem_coreFamilySupport_iff] at hx ⊢
  obtain ⟨M, hM, hxS, hx1⟩ := hx
  exact ⟨M, hM, h M hM hxS, hx1⟩

theorem coreFamilySupport_subset_biUnion (h : ∀ M ∈ 𝓜, S M ≤ M) :
    coreFamilySupport 𝓜 S ⊆ ⋃ M ∈ 𝓜, (M : Set G) := by
  intro x hx
  rw [mem_coreFamilySupport_iff] at hx
  obtain ⟨M, hM, hxS, -⟩ := hx
  exact Set.mem_biUnion hM (h M hM hxS)

theorem coreFamilySupport_finite [Finite G] (𝓜 : Set (Subgroup G))
    (S : Subgroup G → Subgroup G) : (coreFamilySupport 𝓜 S).Finite :=
  Set.toFinite _

end

end CFSG.FeitThompson
