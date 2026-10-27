module

public import CFSG.Milestones.ASVolI.I3

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup

theorem le_of_le_conjClosure_zpowers {H : Type} [Group H] [Finite H] {K₁ L : Subgroup H}
    (hK₁ : CFSG.ASVolI.ChIJK.IsComponentIn K₁ ⊤) {u : H} (hu : u ∈ L)
    (hL : L ≤ CFSG.ASVolI.ChIJK.conjClosure K₁ (zpowers u)) : L ≤ K₁ := by
  have hK₁c : CFSG.IsComponent K₁ := by
    refine ⟨hK₁.2.1, ?_⟩
    have h := (hK₁.2.2).map (f := (⊤ : Subgroup H).subtype)
      (fun x => ⟨⟨x, trivial⟩, rfl⟩)
    rwa [Subgroup.map_subgroupOf_eq_of_le le_top] at h
  have hconj_component : ∀ y : H, CFSG.IsComponent (CFSG.conjugate K₁ y) := fun y =>
    CFSG.LocalCores.isComponent_map_mulEquiv (f := MulAut.conj y⁻¹) hK₁c
  have hconj_le_normalizer : ∀ y : H,
      CFSG.conjugate K₁ y ≤ Subgroup.normalizer (K₁ : Set H) := by
    intro y
    rcases CFSG.LocalCores.distinct_components_commute hK₁c (hconj_component y) with hEq | hcomm
    · rw [← hEq]
      exact K₁.le_normalizer
    · have hcent : CFSG.conjugate K₁ y ≤ Subgroup.centralizer (K₁ : Set H) := by
        rw [Subgroup.commutator_comm] at hcomm
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      exact hcent.trans (Subgroup.centralizer_le_normalizer (K₁ : Set H))
  have hclosure_le_normalizer :
      CFSG.ASVolI.ChIJK.conjClosure K₁ (zpowers u) ≤ Subgroup.normalizer (K₁ : Set H) := by
    rw [CFSG.ASVolI.ChIJK.conjClosure]
    exact iSup₂_le fun y _ => hconj_le_normalizer y
  have huN : u ∈ Subgroup.normalizer (K₁ : Set H) := hclosure_le_normalizer (hL hu)
  have hzpow_le : zpowers u ≤ Subgroup.normalizer (K₁ : Set H) := Subgroup.zpowers_le.mpr huN
  have hconj_eq : ∀ y ∈ zpowers u, CFSG.conjugate K₁ y = K₁ := by
    intro y hy
    have hyinv : y⁻¹ ∈ Subgroup.normalizer (K₁ : Set H) := inv_mem (hzpow_le hy)
    exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := K₁)).mp hyinv
  have hclosure_eq : CFSG.ASVolI.ChIJK.conjClosure K₁ (zpowers u) ≤ K₁ := by
    rw [CFSG.ASVolI.ChIJK.conjClosure]
    exact iSup₂_le fun y hy => (hconj_eq y hy).le
  exact hL.trans hclosure_eq

end CFSG.OddStandard.HigherRank.G2Three
