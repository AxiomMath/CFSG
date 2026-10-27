module

public import Mathlib.Algebra.Group.Subgroup.Map

public section

namespace CFSG

variable {G : Type*} [Group G]

theorem map_codRestrict_eq_subgroupOf {H K : Type*} [Group H] [Group K] {X : Subgroup K}
    (Φ : H →* K) (h : ∀ x, Φ x ∈ X) (Y : Subgroup H) :
    Y.map (Φ.codRestrict X h) = (Y.map Φ).subgroupOf X := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, hx, Subtype.ext hxy⟩

theorem subgroupOf_le_iff_le_map_subtype {H M : Subgroup G} (hH : H ≤ M) {T : Subgroup ↥M} :
    H.subgroupOf M ≤ T ↔ H ≤ T.map M.subtype := by
  constructor
  · intro h x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hH hx⟩, h (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · intro h x hx
    have hx' : (x : G) ∈ H := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨y : ↥M, hyT, hyx⟩ := Subgroup.mem_map.mp (h hx')
    have hyx' : (y : G) = (x : G) := hyx
    have : y = x := Subtype.ext hyx'
    rwa [this] at hyT

theorem subgroupOf_iSup {ι : Sort*} {M : Subgroup G} (S : ι → Subgroup G)
    (hS : ∀ i, S i ≤ M) : (⨆ i, S i).subgroupOf M = ⨆ i, (S i).subgroupOf M := by
  refine le_antisymm ?_ (iSup_le fun i => Subgroup.subgroupOf_mono M (le_iSup S i))
  rw [subgroupOf_le_iff_le_map_subtype (iSup_le hS)]
  refine iSup_le fun i => ?_
  exact (subgroupOf_le_iff_le_map_subtype (hS i)).mp (le_iSup (fun i => (S i).subgroupOf M) i)

end CFSG
