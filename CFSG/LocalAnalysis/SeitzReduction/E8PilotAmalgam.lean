module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviHom

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

local instance e8PilotAmalgamNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

@[expose] def amalgamRoots (J : Finset (Fin (Tag.rank .E8))) : Set (Fin (Tag.rank .E8) → ℤ) :=
  {γ | ∃ j ∈ J, γ = Pi.single j 1 ∨ γ = -Pi.single j 1}

@[expose] def orthRoots (θ : Fin (Tag.rank .E8) → ℤ) : Set (Fin (Tag.rank .E8) → ℤ) :=
  {γ | IsRoot .E8 γ ∧ iform θ γ = 0}

theorem isRoot_of_mem_amalgamRoots {J : Finset (Fin (Tag.rank .E8))}
    {γ : Fin (Tag.rank .E8) → ℤ} (hγ : γ ∈ amalgamRoots J) : IsRoot .E8 γ := by
  obtain ⟨j, -, rfl | rfl⟩ := hγ
  exacts [isRoot_single _ j, isRoot_neg_single _ j]

theorem apply_eq_zero_of_mem_amalgamRoots {J : Finset (Fin (Tag.rank .E8))}
    {γ : Fin (Tag.rank .E8) → ℤ} (hγ : γ ∈ amalgamRoots J) {i : Fin (Tag.rank .E8)}
    (hi : i ∉ J) : γ i = 0 := by
  obtain ⟨j, hj, rfl | rfl⟩ := hγ <;> have hij : i ≠ j := fun h => hi (h ▸ hj)
  · exact Pi.single_eq_of_ne hij _
  · rw [Pi.neg_apply, Pi.single_eq_of_ne hij, neg_zero]

theorem amalgamRoots_mono {I J : Finset (Fin (Tag.rank .E8))} (h : I ⊆ J) :
    amalgamRoots I ⊆ amalgamRoots J := by
  rintro γ ⟨j, hj, hγ⟩
  exact ⟨j, h hj, hγ⟩

theorem iform_neg_right_E8 (θ v : Fin (Tag.rank .E8) → ℤ) : iform θ (-v) = -iform θ v := by
  simp only [iform, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem amalgamRoots_subset_orthRoots_iff {J : Finset (Fin (Tag.rank .E8))}
    {θ : Fin (Tag.rank .E8) → ℤ} :
    amalgamRoots J ⊆ orthRoots θ ↔ ∀ j ∈ J, iform θ (Pi.single j 1) = 0 := by
  constructor
  · intro h j hj
    exact (h ⟨j, hj, Or.inl rfl⟩).2
  · rintro h γ ⟨j, hj, rfl | rfl⟩
    · exact ⟨isRoot_single _ j, h j hj⟩
    · refine ⟨isRoot_neg_single _ j, ?_⟩
      rw [iform_neg_right_E8, h j hj, neg_zero]

theorem perpRoots_eq_orthRoots : EPilot.perpRoots .E8 = orthRoots (highRoot .E8) := by
  ext γ
  exact EPilot.mem_perpRoots_iff_iform (Or.inr (Or.inr rfl))

inductive E8Neighbour
  | high
  | two
  | six
  deriving DecidableEq

namespace E8Neighbour

@[expose] def root : E8Neighbour → Fin (Tag.rank .E8) → ℤ
  | high => highRoot .E8
  | two => Pi.single 1 1
  | six => Pi.single 5 1

@[expose] def nodes : E8Neighbour → Finset (Fin (Tag.rank .E8))
  | high => {0, 1, 2, 3, 4, 5, 6}
  | two => {0, 2, 4, 5, 6, 7}
  | six => {0, 1, 2, 3, 7}

theorem iform_root_single_eq_zero_iff (N : E8Neighbour) (j : Fin (Tag.rank .E8)) :
    iform N.root (Pi.single j 1) = 0 ↔ j ∈ N.nodes := by
  revert j
  cases N <;> decide +kernel

theorem iform_root_root_eq_zero {N N' : E8Neighbour} (h : N ≠ N') : iform N.root N'.root = 0 := by
  revert h
  cases N <;> cases N' <;> decide +kernel

theorem iform_root_self (N : E8Neighbour) : iform N.root N.root = 2 := by
  cases N <;> decide +kernel

theorem isRoot_root (N : E8Neighbour) : IsRoot .E8 N.root := by
  cases N
  exacts [isRoot_highRoot _, isRoot_single _ _, isRoot_single _ _]

theorem root_mem_coverRoots (N : E8Neighbour) : N.root ∈ EPilot.coverRoots .E8 := by
  cases N <;> decide +kernel


@[expose] noncomputable def levi (K : Type) [Field K] (N : E8Neighbour) :
    Subgroup (adjointGroup .E8 K) :=
  (rootSpan .E8 K (orthRoots N.root)).subgroupOf (adjointGroup .E8 K)

theorem levi_high (K : Type) [Field K] : high.levi K = e7Levi K := by
  rw [levi, e7Levi, perpRoots_eq_orthRoots]
  rfl

end E8Neighbour

open E8Neighbour

theorem amalgamRoots_subset_orthRoots_iff_subset_nodes {J : Finset (Fin (Tag.rank .E8))}
    {N : E8Neighbour} : amalgamRoots J ⊆ orthRoots N.root ↔ J ⊆ N.nodes := by
  rw [amalgamRoots_subset_orthRoots_iff]
  exact forall₂_congr fun j _ => N.iform_root_single_eq_zero_iff j

@[expose] def amalgamPlacement (J : Finset (Fin (Tag.rank .E8))) : E8Neighbour :=
  if (7 : Fin (Tag.rank .E8)) ∈ J then
    (if (1 : Fin (Tag.rank .E8)) ∈ J ∨ (3 : Fin (Tag.rank .E8)) ∈ J then .six else .two)
  else .high

theorem amalgamPlacement_of_seven_not_mem {J : Finset (Fin (Tag.rank .E8))}
    (h7 : (7 : Fin (Tag.rank .E8)) ∉ J) : amalgamPlacement J = .high := by
  rw [amalgamPlacement, ite_eq_right h7]

theorem amalgamPlacement_of_one_or_three_mem {J : Finset (Fin (Tag.rank .E8))}
    (h7 : (7 : Fin (Tag.rank .E8)) ∈ J)
    (h13 : (1 : Fin (Tag.rank .E8)) ∈ J ∨ (3 : Fin (Tag.rank .E8)) ∈ J) :
    amalgamPlacement J = .six := by
  rw [amalgamPlacement, ite_eq_left h7, ite_eq_left h13]

theorem amalgamPlacement_of_not_one_three {J : Finset (Fin (Tag.rank .E8))}
    (h7 : (7 : Fin (Tag.rank .E8)) ∈ J) (h1 : (1 : Fin (Tag.rank .E8)) ∉ J)
    (h3 : (3 : Fin (Tag.rank .E8)) ∉ J) : amalgamPlacement J = .two := by
  rw [amalgamPlacement, ite_eq_left h7, ite_eq_right (not_or.2 ⟨h1, h3⟩)]

theorem mem_nodes_high_of_ne {j : Fin (Tag.rank .E8)} (h : j ≠ 7) : j ∈ high.nodes := by
  revert j
  decide

theorem mem_nodes_two_of_ne {j : Fin (Tag.rank .E8)} (h1 : j ≠ 1) (h3 : j ≠ 3) :
    j ∈ two.nodes := by
  revert j
  decide

theorem eq_pair_of_card_le_two {J : Finset (Fin (Tag.rank .E8))} (hJ : J.card ≤ 2)
    {a b : Fin (Tag.rank .E8)} (hab : a ≠ b) (ha : a ∈ J) (hb : b ∈ J) : J = {a, b} := by
  have hsub : ({a, b} : Finset (Fin (Tag.rank .E8))) ⊆ J := by
    intro j hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    exacts [ha, hb]
  have h2 : ({a, b} : Finset (Fin (Tag.rank .E8))).card = 2 := Finset.card_pair hab
  exact (Finset.eq_of_subset_of_card_le hsub (h2 ▸ hJ)).symm

theorem subset_nodes_amalgamPlacement {J : Finset (Fin (Tag.rank .E8))} (hJ : J.card ≤ 2) :
    J ⊆ (amalgamPlacement J).nodes := by
  by_cases h7 : (7 : Fin (Tag.rank .E8)) ∈ J
  · by_cases h13 : (1 : Fin (Tag.rank .E8)) ∈ J ∨ (3 : Fin (Tag.rank .E8)) ∈ J
    · rw [amalgamPlacement_of_one_or_three_mem h7 h13]
      rcases h13 with h1 | h3
      · rw [eq_pair_of_card_le_two hJ (by decide) h1 h7]
        decide
      · rw [eq_pair_of_card_le_two hJ (by decide) h3 h7]
        decide
    · rw [not_or] at h13
      rw [amalgamPlacement_of_not_one_three h7 h13.1 h13.2]
      exact fun j hj => mem_nodes_two_of_ne (fun h => h13.1 (h ▸ hj)) fun h => h13.2 (h ▸ hj)
  · rw [amalgamPlacement_of_seven_not_mem h7]
    exact fun j hj => mem_nodes_high_of_ne fun h => h7 (h ▸ hj)

theorem amalgamRoots_subset_orthRoots_placement {J : Finset (Fin (Tag.rank .E8))}
    (hJ : J.card ≤ 2) : amalgamRoots J ⊆ orthRoots (amalgamPlacement J).root :=
  amalgamRoots_subset_orthRoots_iff_subset_nodes.2 (subset_nodes_amalgamPlacement hJ)

theorem amalgamRoots_subset_high_or_two_iff {J : Finset (Fin (Tag.rank .E8))} (hJ : J.card ≤ 2) :
    amalgamRoots J ⊆ orthRoots high.root ∨ amalgamRoots J ⊆ orthRoots two.root ↔
      J ≠ {1, 7} ∧ J ≠ {3, 7} := by
  rw [amalgamRoots_subset_orthRoots_iff_subset_nodes,
    amalgamRoots_subset_orthRoots_iff_subset_nodes]
  constructor
  · rintro (h | h) <;> refine ⟨?_, ?_⟩ <;> rintro rfl <;> revert h <;> decide
  · rintro ⟨h17, h37⟩
    by_cases h7 : (7 : Fin (Tag.rank .E8)) ∈ J
    · right
      refine fun j hj => mem_nodes_two_of_ne ?_ ?_
      · rintro rfl
        exact h17 (eq_pair_of_card_le_two hJ (by decide) hj h7)
      · rintro rfl
        exact h37 (eq_pair_of_card_le_two hJ (by decide) hj h7)
    · left
      exact fun j hj => mem_nodes_high_of_ne fun h => h7 (h ▸ hj)

theorem mem_nodes_six_of_ne {j : Fin (Tag.rank .E8)} (h4 : j ≠ 4) (h5 : j ≠ 5) (h6 : j ≠ 6) :
    j ∈ six.nodes := by
  revert j
  decide

theorem amalgamRoots_subset_high_or_six_iff {J : Finset (Fin (Tag.rank .E8))} (hJ : J.card ≤ 2) :
    amalgamRoots J ⊆ orthRoots high.root ∨ amalgamRoots J ⊆ orthRoots six.root ↔
      J ≠ {4, 7} ∧ J ≠ {5, 7} ∧ J ≠ {6, 7} := by
  rw [amalgamRoots_subset_orthRoots_iff_subset_nodes,
    amalgamRoots_subset_orthRoots_iff_subset_nodes]
  constructor
  · rintro (h | h) <;> refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> revert h <;> decide
  · rintro ⟨h47, h57, h67⟩
    by_cases h7 : (7 : Fin (Tag.rank .E8)) ∈ J
    · right
      refine fun j hj => mem_nodes_six_of_ne ?_ ?_ ?_
      · rintro rfl
        exact h47 (eq_pair_of_card_le_two hJ (by decide) hj h7)
      · rintro rfl
        exact h57 (eq_pair_of_card_le_two hJ (by decide) hj h7)
      · rintro rfl
        exact h67 (eq_pair_of_card_le_two hJ (by decide) hj h7)
    · left
      exact fun j hj => mem_nodes_high_of_ne fun h => h7 (h ▸ hj)

section Placement


variable {K : Type} [Field K]

theorem rootSpan_mono_E8 {S T : Set (Fin (Tag.rank .E8) → ℤ)} (h : S ⊆ T) :
    rootSpan .E8 K S ≤ rootSpan .E8 K T :=
  iSup₂_le fun α hα => le_iSup₂_of_le (f := fun α (_ : α ∈ T) => rootSubgroup .E8 K α) α (h hα)
    le_rfl


variable (K) in
noncomputable abbrev adjDatumE8 :
    CFSG.LieType.Universal.UniversalRootDatum ↥(adjointGroup .E8 K) :=
  adjDatum (rootOperatorFamily .E8) K

theorem map_subtype_rootGroup_E8 {γ : Fin (Tag.rank .E8) → ℤ} (hγ : IsRoot .E8 γ) :
    ((adjDatumE8 K).rootGroup γ).map (adjointGroup .E8 K).subtype = rootSubgroup .E8 K γ := by
  change (CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily .E8) K γ).map _ = _
  rw [CFSG.LieType.Steinberg.Adjoint.rootGroup_of_isRoot hγ,
    ← RootOperatorFamily.subgroupOf_rootSubgroup_eq (rootOperatorFamily .E8) K ⟨γ, hγ⟩,
    subgroupOf_map_subtype, inf_of_le_left (rootSubgroup_le_adjointGroup γ)]

theorem map_subtype_levi_adjDatumE8 (J : Finset (Fin (Tag.rank .E8))) :
    (CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J).map (adjointGroup .E8 K).subtype =
      rootSpan .E8 K (amalgamRoots J) := by
  have hj : ∀ j : Fin (Tag.rank .E8),
      (CFSG.LieType.CurtisTits.rankOne (adjDatumE8 K).rootGroup j).map
          (adjointGroup .E8 K).subtype =
        rootSubgroup .E8 K (Pi.single j 1) ⊔ rootSubgroup .E8 K (-Pi.single j 1) := fun j => by
    rw [CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup,
      map_subtype_rootGroup_E8 (isRoot_single _ j),
      map_subtype_rootGroup_E8 (isRoot_neg_single _ j)]
  rw [CFSG.LieType.CurtisTits.levi, Subgroup.map_iSup]
  simp_rw [Subgroup.map_iSup, hj]
  apply le_antisymm
  · refine iSup₂_le fun j hj => sup_le ?_ ?_
    · exact le_iSup₂_of_le (f := fun α (_ : α ∈ amalgamRoots J) => rootSubgroup .E8 K α)
        (Pi.single j 1) ⟨j, hj, Or.inl rfl⟩ le_rfl
    · exact le_iSup₂_of_le (f := fun α (_ : α ∈ amalgamRoots J) => rootSubgroup .E8 K α)
        (-Pi.single j 1) ⟨j, hj, Or.inr rfl⟩ le_rfl
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨j, hj, rfl | rfl⟩ := hγ
    · exact le_iSup₂_of_le (f := fun j (_ : j ∈ J) =>
        rootSubgroup .E8 K (Pi.single j 1) ⊔ rootSubgroup .E8 K (-Pi.single j 1)) j hj le_sup_left
    · exact le_iSup₂_of_le (f := fun j (_ : j ∈ J) =>
        rootSubgroup .E8 K (Pi.single j 1) ⊔ rootSubgroup .E8 K (-Pi.single j 1)) j hj le_sup_right

theorem levi_adjDatumE8_eq (J : Finset (Fin (Tag.rank .E8))) :
    CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J =
      (rootSpan .E8 K (amalgamRoots J)).subgroupOf (adjointGroup .E8 K) := by
  rw [← map_subtype_levi_adjDatumE8]
  exact (Subgroup.comap_map_eq_self_of_injective (adjointGroup .E8 K).subtype_injective _).symm

theorem levi_le_orthRoots {J : Finset (Fin (Tag.rank .E8))} {θ : Fin (Tag.rank .E8) → ℤ}
    (h : ∀ j ∈ J, iform θ (Pi.single j 1) = 0) :
    CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J ≤
      (rootSpan .E8 K (orthRoots θ)).subgroupOf (adjointGroup .E8 K) := by
  rw [levi_adjDatumE8_eq]
  exact Subgroup.subgroupOf_mono _ (rootSpan_mono_E8 (amalgamRoots_subset_orthRoots_iff.2 h))

theorem levi_le_neighbourLevi {J : Finset (Fin (Tag.rank .E8))} {N : E8Neighbour}
    (h : J ⊆ N.nodes) : CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J ≤ N.levi K :=
  levi_le_orthRoots fun j hj => (N.iform_root_single_eq_zero_iff j).2 (h hj)

theorem levi_le_e7Levi {J : Finset (Fin (Tag.rank .E8))} (h : (7 : Fin (Tag.rank .E8)) ∉ J) :
    CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J ≤ e7Levi K := by
  rw [← levi_high]
  exact levi_le_neighbourLevi fun j hj => mem_nodes_high_of_ne fun h' => h (h' ▸ hj)

theorem leviAmalgam_le_placementLevi (J : {J : Finset (Fin (adjDatumE8 K).rank) // J.card ≤ 2}) :
    (adjDatumE8 K).leviAmalgam J ≤ (amalgamPlacement J.1).levi K :=
  levi_le_neighbourLevi (subset_nodes_amalgamPlacement J.2)

theorem leviAmalgam_le_e7Levi_or_two_or_six
    (J : {J : Finset (Fin (adjDatumE8 K).rank) // J.card ≤ 2}) :
    ((7 : Fin (Tag.rank .E8)) ∉ J.1 → (adjDatumE8 K).leviAmalgam J ≤ e7Levi K) ∧
    ((1 : Fin (Tag.rank .E8)) ∉ J.1 → (3 : Fin (Tag.rank .E8)) ∉ J.1 →
      (adjDatumE8 K).leviAmalgam J ≤ two.levi K) ∧
    (J.1 ⊆ six.nodes → (adjDatumE8 K).leviAmalgam J ≤ six.levi K) ∧
    ((adjDatumE8 K).leviAmalgam J ≤ e7Levi K ∨ (adjDatumE8 K).leviAmalgam J ≤ two.levi K ∨
      (adjDatumE8 K).leviAmalgam J ≤ six.levi K) := by
  refine ⟨levi_le_e7Levi, fun h1 h3 => levi_le_neighbourLevi fun j hj =>
    mem_nodes_two_of_ne (fun h => h1 (h ▸ hj)) fun h => h3 (h ▸ hj),
    fun h => levi_le_neighbourLevi h, ?_⟩
  have h := leviAmalgam_le_placementLevi J
  unfold amalgamPlacement at h
  split_ifs at h with h7 h13
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · rw [levi_high] at h
    exact Or.inl h

end Placement

end CFSG.SeitzReduction.E8Pilot
