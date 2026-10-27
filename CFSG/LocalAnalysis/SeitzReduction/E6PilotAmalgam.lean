module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLevi

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

local instance e6PilotAmalgamNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def amalgamRoots (J : Finset (Fin (Tag.rank .E6))) : Set (Fin (Tag.rank .E6) → ℤ) :=
  {γ | ∃ j ∈ J, γ = Pi.single j 1 ∨ γ = -Pi.single j 1}

@[expose] def orthRoots (θ : Fin (Tag.rank .E6) → ℤ) : Set (Fin (Tag.rank .E6) → ℤ) :=
  {γ | IsRoot .E6 γ ∧ iform θ γ = 0}

theorem isRoot_of_mem_amalgamRoots {J : Finset (Fin (Tag.rank .E6))}
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ amalgamRoots J) : IsRoot .E6 γ := by
  obtain ⟨j, -, rfl | rfl⟩ := hγ
  exacts [isRoot_single _ j, isRoot_neg_single _ j]

theorem apply_eq_zero_of_mem_amalgamRoots {J : Finset (Fin (Tag.rank .E6))}
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ amalgamRoots J) {i : Fin (Tag.rank .E6)}
    (hi : i ∉ J) : γ i = 0 := by
  obtain ⟨j, hj, rfl | rfl⟩ := hγ <;> have hij : i ≠ j := fun h => hi (h ▸ hj)
  · exact Pi.single_eq_of_ne hij _
  · rw [Pi.neg_apply, Pi.single_eq_of_ne hij, neg_zero]

theorem amalgamRoots_mono {I J : Finset (Fin (Tag.rank .E6))} (h : I ⊆ J) :
    amalgamRoots I ⊆ amalgamRoots J := by
  rintro γ ⟨j, hj, hγ⟩
  exact ⟨j, h hj, hγ⟩

theorem iform_neg_right_E6 (θ v : Fin (Tag.rank .E6) → ℤ) : iform θ (-v) = -iform θ v := by
  simp only [iform, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem amalgamRoots_subset_orthRoots_iff {J : Finset (Fin (Tag.rank .E6))}
    {θ : Fin (Tag.rank .E6) → ℤ} :
    amalgamRoots J ⊆ orthRoots θ ↔ ∀ j ∈ J, iform θ (Pi.single j 1) = 0 := by
  constructor
  · intro h j hj
    exact (h ⟨j, hj, Or.inl rfl⟩).2
  · rintro h γ ⟨j, hj, rfl | rfl⟩
    · exact ⟨isRoot_single _ j, h j hj⟩
    · refine ⟨isRoot_neg_single _ j, ?_⟩
      rw [iform_neg_right_E6, h j hj, neg_zero]

theorem a5LeviRoots_eq_orthRoots : a5LeviRoots = orthRoots (highRoot .E6) := by
  ext γ
  rw [mem_a5LeviRoots]
  change _ ↔ IsRoot .E6 γ ∧ iform (highRoot .E6) γ = 0
  rw [EPilot.iform_highRoot (Or.inl rfl)]

theorem perpRoots_eq_orthRoots : EPilot.perpRoots .E6 = orthRoots (highRoot .E6) := by
  rw [← a5LeviRoots_eq_orthRoots]
  rfl

inductive E6Neighbour
  | high
  | six
  | three
  deriving DecidableEq

namespace E6Neighbour

@[expose] def root : E6Neighbour → Fin (Tag.rank .E6) → ℤ
  | high => highRoot .E6
  | six => Pi.single 5 1
  | three => Pi.single 2 1

@[expose] def nodes : E6Neighbour → Finset (Fin (Tag.rank .E6))
  | high => {0, 2, 3, 4, 5}
  | six => {0, 1, 2, 3}
  | three => {1, 4, 5}

theorem iform_root_single_eq_zero_iff (N : E6Neighbour) (j : Fin (Tag.rank .E6)) :
    iform N.root (Pi.single j 1) = 0 ↔ j ∈ N.nodes := by
  revert j
  cases N <;> decide +kernel

theorem iform_root_root_eq_zero {N N' : E6Neighbour} (h : N ≠ N') : iform N.root N'.root = 0 := by
  revert h
  cases N <;> cases N' <;> decide +kernel

theorem iform_root_self (N : E6Neighbour) : iform N.root N.root = 2 := by
  cases N <;> decide +kernel

theorem isRoot_root (N : E6Neighbour) : IsRoot .E6 N.root := by
  cases N
  exacts [isRoot_highRoot _, isRoot_single _ _, isRoot_single _ _]

theorem root_mem_coverRoots (N : E6Neighbour) : N.root ∈ EPilot.coverRoots .E6 := by
  cases N <;> decide +kernel


@[expose] noncomputable def levi (K : Type) [Field K] (N : E6Neighbour) :
    Subgroup (adjointGroup .E6 K) :=
  (rootSpan .E6 K (orthRoots N.root)).subgroupOf (adjointGroup .E6 K)

theorem levi_high (K : Type) [Field K] : high.levi K = a5Levi K := by
  rw [levi, a5Levi, a5LeviRoots_eq_orthRoots]
  rfl

end E6Neighbour

open E6Neighbour

theorem amalgamRoots_subset_orthRoots_iff_subset_nodes {J : Finset (Fin (Tag.rank .E6))}
    {N : E6Neighbour} : amalgamRoots J ⊆ orthRoots N.root ↔ J ⊆ N.nodes := by
  rw [amalgamRoots_subset_orthRoots_iff]
  exact forall₂_congr fun j _ => N.iform_root_single_eq_zero_iff j

@[expose] def amalgamPlacement (J : Finset (Fin (Tag.rank .E6))) : E6Neighbour :=
  if (1 : Fin (Tag.rank .E6)) ∈ J then
    (if (4 : Fin (Tag.rank .E6)) ∈ J ∨ (5 : Fin (Tag.rank .E6)) ∈ J then .three else .six)
  else .high

theorem amalgamPlacement_of_one_not_mem {J : Finset (Fin (Tag.rank .E6))}
    (h1 : (1 : Fin (Tag.rank .E6)) ∉ J) : amalgamPlacement J = .high := by
  rw [amalgamPlacement, ite_eq_right h1]

theorem amalgamPlacement_of_four_or_five_mem {J : Finset (Fin (Tag.rank .E6))}
    (h1 : (1 : Fin (Tag.rank .E6)) ∈ J)
    (h45 : (4 : Fin (Tag.rank .E6)) ∈ J ∨ (5 : Fin (Tag.rank .E6)) ∈ J) :
    amalgamPlacement J = .three := by
  rw [amalgamPlacement, ite_eq_left h1, ite_eq_left h45]

theorem amalgamPlacement_of_not_four_five {J : Finset (Fin (Tag.rank .E6))}
    (h1 : (1 : Fin (Tag.rank .E6)) ∈ J) (h4 : (4 : Fin (Tag.rank .E6)) ∉ J)
    (h5 : (5 : Fin (Tag.rank .E6)) ∉ J) : amalgamPlacement J = .six := by
  rw [amalgamPlacement, ite_eq_left h1, ite_eq_right (not_or.2 ⟨h4, h5⟩)]

theorem mem_nodes_high_of_ne {j : Fin (Tag.rank .E6)} (h : j ≠ 1) : j ∈ high.nodes := by
  revert j
  decide

theorem mem_nodes_six_of_ne {j : Fin (Tag.rank .E6)} (h4 : j ≠ 4) (h5 : j ≠ 5) :
    j ∈ six.nodes := by
  revert j
  decide

theorem eq_pair_of_card_le_two {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2)
    {a b : Fin (Tag.rank .E6)} (hab : a ≠ b) (ha : a ∈ J) (hb : b ∈ J) : J = {a, b} := by
  have hsub : ({a, b} : Finset (Fin (Tag.rank .E6))) ⊆ J := by
    intro j hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    exacts [ha, hb]
  have h2 : ({a, b} : Finset (Fin (Tag.rank .E6))).card = 2 := Finset.card_pair hab
  exact (Finset.eq_of_subset_of_card_le hsub (h2 ▸ hJ)).symm

theorem subset_nodes_amalgamPlacement {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2) :
    J ⊆ (amalgamPlacement J).nodes := by
  by_cases h1 : (1 : Fin (Tag.rank .E6)) ∈ J
  · by_cases h45 : (4 : Fin (Tag.rank .E6)) ∈ J ∨ (5 : Fin (Tag.rank .E6)) ∈ J
    · rw [amalgamPlacement_of_four_or_five_mem h1 h45]
      rcases h45 with h4 | h5
      · rw [eq_pair_of_card_le_two hJ (by decide) h1 h4]
        decide
      · rw [eq_pair_of_card_le_two hJ (by decide) h1 h5]
        decide
    · rw [not_or] at h45
      rw [amalgamPlacement_of_not_four_five h1 h45.1 h45.2]
      exact fun j hj => mem_nodes_six_of_ne (fun h => h45.1 (h ▸ hj)) fun h => h45.2 (h ▸ hj)
  · rw [amalgamPlacement_of_one_not_mem h1]
    exact fun j hj => mem_nodes_high_of_ne fun h => h1 (h ▸ hj)

theorem amalgamRoots_subset_orthRoots_placement {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J.card ≤ 2) : amalgamRoots J ⊆ orthRoots (amalgamPlacement J).root :=
  amalgamRoots_subset_orthRoots_iff_subset_nodes.2 (subset_nodes_amalgamPlacement hJ)

theorem amalgamRoots_subset_high_or_six_iff {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2) :
    amalgamRoots J ⊆ orthRoots high.root ∨ amalgamRoots J ⊆ orthRoots six.root ↔
      J ≠ {1, 4} ∧ J ≠ {1, 5} := by
  rw [amalgamRoots_subset_orthRoots_iff_subset_nodes,
    amalgamRoots_subset_orthRoots_iff_subset_nodes]
  constructor
  · rintro (h | h) <;> refine ⟨?_, ?_⟩ <;> rintro rfl <;> revert h <;> decide
  · rintro ⟨h14, h15⟩
    by_cases h1 : (1 : Fin (Tag.rank .E6)) ∈ J
    · right
      refine fun j hj => mem_nodes_six_of_ne ?_ ?_
      · rintro rfl
        exact h14 (eq_pair_of_card_le_two hJ (by decide) h1 hj)
      · rintro rfl
        exact h15 (eq_pair_of_card_le_two hJ (by decide) h1 hj)
    · left
      exact fun j hj => mem_nodes_high_of_ne fun h => h1 (h ▸ hj)

section Placement


variable {K : Type} [Field K]

theorem rootSpan_mono_E6 {S T : Set (Fin (Tag.rank .E6) → ℤ)} (h : S ⊆ T) :
    rootSpan .E6 K S ≤ rootSpan .E6 K T :=
  iSup₂_le fun α hα => le_iSup₂_of_le (f := fun α (_ : α ∈ T) => rootSubgroup .E6 K α) α (h hα)
    le_rfl


variable (K) in
noncomputable abbrev adjDatumE6 :
    CFSG.LieType.Universal.UniversalRootDatum ↥(adjointGroup .E6 K) :=
  adjDatum (rootOperatorFamily .E6) K

theorem map_subtype_rootGroup_E6 {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) :
    ((adjDatumE6 K).rootGroup γ).map (adjointGroup .E6 K).subtype = rootSubgroup .E6 K γ := by
  change (CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily .E6) K γ).map _ = _
  rw [CFSG.LieType.Steinberg.Adjoint.rootGroup_of_isRoot hγ,
    ← RootOperatorFamily.subgroupOf_rootSubgroup_eq (rootOperatorFamily .E6) K ⟨γ, hγ⟩,
    subgroupOf_map_subtype, inf_of_le_left (rootSubgroup_le_adjointGroup γ)]

theorem map_subtype_levi_adjDatumE6 (J : Finset (Fin (Tag.rank .E6))) :
    (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J).map (adjointGroup .E6 K).subtype =
      rootSpan .E6 K (amalgamRoots J) := by
  have hj : ∀ j : Fin (Tag.rank .E6),
      (CFSG.LieType.CurtisTits.rankOne (adjDatumE6 K).rootGroup j).map
          (adjointGroup .E6 K).subtype =
        rootSubgroup .E6 K (Pi.single j 1) ⊔ rootSubgroup .E6 K (-Pi.single j 1) := fun j => by
    rw [CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup,
      map_subtype_rootGroup_E6 (isRoot_single _ j),
      map_subtype_rootGroup_E6 (isRoot_neg_single _ j)]
  rw [CFSG.LieType.CurtisTits.levi, Subgroup.map_iSup]
  simp_rw [Subgroup.map_iSup, hj]
  apply le_antisymm
  · refine iSup₂_le fun j hj => sup_le ?_ ?_
    · exact le_iSup₂_of_le (f := fun α (_ : α ∈ amalgamRoots J) => rootSubgroup .E6 K α)
        (Pi.single j 1) ⟨j, hj, Or.inl rfl⟩ le_rfl
    · exact le_iSup₂_of_le (f := fun α (_ : α ∈ amalgamRoots J) => rootSubgroup .E6 K α)
        (-Pi.single j 1) ⟨j, hj, Or.inr rfl⟩ le_rfl
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨j, hj, rfl | rfl⟩ := hγ
    · exact le_iSup₂_of_le (f := fun j (_ : j ∈ J) =>
        rootSubgroup .E6 K (Pi.single j 1) ⊔ rootSubgroup .E6 K (-Pi.single j 1)) j hj le_sup_left
    · exact le_iSup₂_of_le (f := fun j (_ : j ∈ J) =>
        rootSubgroup .E6 K (Pi.single j 1) ⊔ rootSubgroup .E6 K (-Pi.single j 1)) j hj le_sup_right

theorem levi_adjDatumE6_eq (J : Finset (Fin (Tag.rank .E6))) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J =
      (rootSpan .E6 K (amalgamRoots J)).subgroupOf (adjointGroup .E6 K) := by
  rw [← map_subtype_levi_adjDatumE6]
  exact (Subgroup.comap_map_eq_self_of_injective (adjointGroup .E6 K).subtype_injective _).symm

theorem levi_le_orthRoots {J : Finset (Fin (Tag.rank .E6))} {θ : Fin (Tag.rank .E6) → ℤ}
    (h : ∀ j ∈ J, iform θ (Pi.single j 1) = 0) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J ≤
      (rootSpan .E6 K (orthRoots θ)).subgroupOf (adjointGroup .E6 K) := by
  rw [levi_adjDatumE6_eq]
  exact Subgroup.subgroupOf_mono _ (rootSpan_mono_E6 (amalgamRoots_subset_orthRoots_iff.2 h))

theorem levi_le_neighbourLevi {J : Finset (Fin (Tag.rank .E6))} {N : E6Neighbour}
    (h : J ⊆ N.nodes) : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J ≤ N.levi K :=
  levi_le_orthRoots fun j hj => (N.iform_root_single_eq_zero_iff j).2 (h hj)

theorem levi_le_a5Levi {J : Finset (Fin (Tag.rank .E6))} (h : (1 : Fin (Tag.rank .E6)) ∉ J) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J ≤ a5Levi K := by
  rw [← levi_high]
  exact levi_le_neighbourLevi fun j hj => mem_nodes_high_of_ne fun h' => h (h' ▸ hj)

theorem leviAmalgam_le_placementLevi (J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}) :
    (adjDatumE6 K).leviAmalgam J ≤ (amalgamPlacement J.1).levi K :=
  levi_le_neighbourLevi (subset_nodes_amalgamPlacement J.2)

theorem leviAmalgam_le_a5Levi_or_six_or_three
    (J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2}) :
    ((1 : Fin (Tag.rank .E6)) ∉ J.1 → (adjDatumE6 K).leviAmalgam J ≤ a5Levi K) ∧
    ((4 : Fin (Tag.rank .E6)) ∉ J.1 → (5 : Fin (Tag.rank .E6)) ∉ J.1 →
      (adjDatumE6 K).leviAmalgam J ≤ six.levi K) ∧
    (J.1 ⊆ three.nodes → (adjDatumE6 K).leviAmalgam J ≤ three.levi K) ∧
    ((adjDatumE6 K).leviAmalgam J ≤ a5Levi K ∨ (adjDatumE6 K).leviAmalgam J ≤ six.levi K ∨
      (adjDatumE6 K).leviAmalgam J ≤ three.levi K) := by
  refine ⟨levi_le_a5Levi, fun h4 h5 => levi_le_neighbourLevi fun j hj =>
    mem_nodes_six_of_ne (fun h => h4 (h ▸ hj)) fun h => h5 (h ▸ hj),
    fun h => levi_le_neighbourLevi h, ?_⟩
  have h := leviAmalgam_le_placementLevi J
  unfold amalgamPlacement at h
  split_ifs at h with h1 h45
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · rw [levi_high] at h
    exact Or.inl h

end Placement

end CFSG.SeitzReduction.E6Pilot
