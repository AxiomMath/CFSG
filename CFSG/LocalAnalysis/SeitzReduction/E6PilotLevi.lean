module

public import CFSG.Timmesfeld.LieEmbed.A5Roots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInnerRoots
public import CFSG.Blueprint.ChevalleyRootGroups

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.Timmesfeld.LieEmbed

@[expose] def a5LeviRoots : Set (Fin (Tag.rank .E6) → ℤ) :=
  {γ | IsRoot .E6 γ ∧ γ (highNode .E6) = 0}

theorem mem_a5LeviRoots {γ : Fin (Tag.rank .E6) → ℤ} :
    γ ∈ a5LeviRoots ↔ IsRoot .E6 γ ∧ γ (highNode .E6) = 0 :=
  Iff.rfl

theorem a5Root_highNode (i j : Fin 6) : a5Root i j (highNode .E6) = 0 := by
  simp [a5Root, highNode]

set_option maxRecDepth 100000 in
theorem a5LeviRoots_check : ∀ γ ∈ rootFinset .E6, γ (highNode .E6) = 0 →
    ∃ i : Fin 6, ∃ j : Fin 6, i ≠ j ∧ a5Root i j = γ := by
  decide +kernel


theorem a5Root_mem_a5LeviRoots {i j : Fin 6} (hij : i ≠ j) : a5Root i j ∈ a5LeviRoots :=
  ⟨isRoot_a5Root hij, a5Root_highNode i j⟩

theorem exists_a5Root_eq_of_mem_a5LeviRoots {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : γ ∈ a5LeviRoots) : ∃ i j : Fin 6, i ≠ j ∧ a5Root i j = γ :=
  a5LeviRoots_check γ (mem_rootFinset.2 hγ.1) hγ.2

theorem a5LeviRoots_eq : a5LeviRoots = {γ | ∃ i j : Fin 6, i ≠ j ∧ a5Root i j = γ} := by
  ext γ
  exact ⟨exists_a5Root_eq_of_mem_a5LeviRoots, fun ⟨i, j, hij, h⟩ => h ▸ a5Root_mem_a5LeviRoots hij⟩

variable (K : Type) [Field K]

@[expose] noncomputable def a5Levi : Subgroup ↥(adjointGroup .E6 K) :=
  (rootSpan .E6 K a5LeviRoots).subgroupOf (adjointGroup .E6 K)

variable {K}

theorem mem_a5Levi_iff {g : adjointGroup .E6 K} :
    g ∈ a5Levi K ↔ (g : ModGL .E6 K) ∈ rootSpan .E6 K a5LeviRoots :=
  mem_subgroupOf

theorem rootSpan_le_adjointGroup_E6 (S : Set (Fin (Tag.rank .E6) → ℤ)) :
    rootSpan .E6 K S ≤ adjointGroup .E6 K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem map_subtype_a5Levi :
    (a5Levi K).map (adjointGroup .E6 K).subtype = rootSpan .E6 K a5LeviRoots := by
  rw [a5Levi, subgroupOf_map_subtype, inf_of_le_left (rootSpan_le_adjointGroup_E6 _)]

theorem pinnedX_mem_rootSpan_a5LeviRoots {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ a5LeviRoots)
    (c : K) : pinnedX .E6 K γ c ∈ rootSpan .E6 K a5LeviRoots :=
  le_iSup₂ (f := fun γ (_ : γ ∈ a5LeviRoots) => rootSubgroup .E6 K γ) γ hγ
    (subset_closure ⟨c, rfl⟩)

theorem pinnedX_mem_a5Levi {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ a5LeviRoots) (c : K) :
    (⟨pinnedX .E6 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .E6 K) ∈ a5Levi K :=
  mem_a5Levi_iff.2 (pinnedX_mem_rootSpan_a5LeviRoots hγ c)

theorem pinnedX_a5Root_mem_a5Levi {i j : Fin 6} (hij : i ≠ j) (c : K) :
    (⟨pinnedX .E6 K (a5Root i j) c, pinnedX_mem_adjointGroup _ c⟩ : adjointGroup .E6 K) ∈
      a5Levi K :=
  pinnedX_mem_a5Levi (a5Root_mem_a5LeviRoots hij) c

theorem rootSpan_a5LeviRoots_eq_closure :
    rootSpan .E6 K a5LeviRoots =
      closure {g | ∃ i j : Fin 6, i ≠ j ∧ ∃ c : K, pinnedX .E6 K (a5Root i j) c = g} := by
  refine le_antisymm (iSup₂_le fun γ hγ => ?_) ((closure_le _).2 ?_)
  · obtain ⟨i, j, hij, rfl⟩ := exists_a5Root_eq_of_mem_a5LeviRoots hγ
    refine (closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact subset_closure ⟨i, j, hij, c, rfl⟩
  · rintro _ ⟨i, j, hij, c, rfl⟩
    exact pinnedX_mem_rootSpan_a5LeviRoots (a5Root_mem_a5LeviRoots hij) c

theorem a5Levi_eq_closure :
    a5Levi K = closure {g : adjointGroup .E6 K |
      ∃ i j : Fin 6, i ≠ j ∧ ∃ c : K, pinnedX .E6 K (a5Root i j) c = (g : ModGL .E6 K)} := by
  apply map_injective (adjointGroup .E6 K).subtype_injective
  rw [map_subtype_a5Levi, rootSpan_a5LeviRoots_eq_closure, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨i, j, hij, c, rfl⟩
    exact ⟨⟨_, pinnedX_mem_adjointGroup _ c⟩, ⟨i, j, hij, c, rfl⟩, rfl⟩
  · rintro ⟨g, ⟨i, j, hij, c, hc⟩, rfl⟩
    exact ⟨i, j, hij, c, hc⟩

end CFSG.SeitzReduction.E6Pilot
