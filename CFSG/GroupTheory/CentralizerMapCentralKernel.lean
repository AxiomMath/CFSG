module

public import CFSG.GroupTheory.InnerCentralizerProjection

public section

namespace CFSG.GroupTheory

theorem centralizer_map_eq_map_centralizer_of_perfect
    {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f)
    {K : Subgroup G} [K.Normal] (hK : Group.IsPerfect ↥K)
    (hker : f.ker ≤ (Subgroup.center ↥K).map K.subtype) :
    Subgroup.centralizer (K.map f : Set H) = (Subgroup.centralizer (K : Set G)).map f := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨g, rfl⟩ := hf x
    have hgN : g ∈ Subgroup.normalizer (K : Set G) := by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top g
    have hg : g ∈ Subgroup.centralizer (K : Set G) := by
      refine CFSG.mem_centralizer_of_commutator_mem_center hK hgN ?_
      intro k hk
      apply hker
      rw [MonoidHom.mem_ker]
      have hxk := (Subgroup.mem_centralizer_iff.mp hx) (f k) (Subgroup.mem_map_of_mem f hk)
      calc
        f (g * k * g⁻¹ * k⁻¹) = f g * f k * (f g)⁻¹ * (f k)⁻¹ := by
          simp only [map_mul, map_inv]
        _ = f k * f g * (f g)⁻¹ * (f k)⁻¹ := by rw [← hxk]
        _ = 1 := by group
    exact ⟨g, hg, rfl⟩
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hg) k hk]

end CFSG.GroupTheory
