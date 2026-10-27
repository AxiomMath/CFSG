module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

local instance e7PilotAmalgamNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

@[expose] def amalgamRoots (J : Finset (Fin (Tag.rank .E7))) : Set (Fin (Tag.rank .E7) → ℤ) :=
  {γ | ∃ j ∈ J, γ = Pi.single j 1 ∨ γ = -Pi.single j 1}

@[expose] def orthRoots (θ : Fin (Tag.rank .E7) → ℤ) : Set (Fin (Tag.rank .E7) → ℤ) :=
  {γ | IsRoot .E7 γ ∧ iform θ γ = 0}

theorem isRoot_of_mem_amalgamRoots {J : Finset (Fin (Tag.rank .E7))}
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ amalgamRoots J) : IsRoot .E7 γ := by
  obtain ⟨j, -, rfl | rfl⟩ := hγ
  exacts [isRoot_single _ j, isRoot_neg_single _ j]

theorem apply_eq_zero_of_mem_amalgamRoots {J : Finset (Fin (Tag.rank .E7))}
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ amalgamRoots J) {i : Fin (Tag.rank .E7)}
    (hi : i ∉ J) : γ i = 0 := by
  obtain ⟨j, hj, rfl | rfl⟩ := hγ <;> have hij : i ≠ j := fun h => hi (h ▸ hj)
  · exact Pi.single_eq_of_ne hij _
  · rw [Pi.neg_apply, Pi.single_eq_of_ne hij, neg_zero]

theorem amalgamRoots_mono {I J : Finset (Fin (Tag.rank .E7))} (h : I ⊆ J) :
    amalgamRoots I ⊆ amalgamRoots J := by
  rintro γ ⟨j, hj, hγ⟩
  exact ⟨j, h hj, hγ⟩

theorem iform_neg_right_E7 (θ v : Fin (Tag.rank .E7) → ℤ) : iform θ (-v) = -iform θ v := by
  simp only [iform, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem amalgamRoots_subset_orthRoots_iff {J : Finset (Fin (Tag.rank .E7))}
    {θ : Fin (Tag.rank .E7) → ℤ} :
    amalgamRoots J ⊆ orthRoots θ ↔ ∀ j ∈ J, iform θ (Pi.single j 1) = 0 := by
  constructor
  · intro h j hj
    exact (h ⟨j, hj, Or.inl rfl⟩).2
  · rintro h γ ⟨j, hj, rfl | rfl⟩
    · exact ⟨isRoot_single _ j, h j hj⟩
    · refine ⟨isRoot_neg_single _ j, ?_⟩
      rw [iform_neg_right_E7, h j hj, neg_zero]

theorem perpRoots_eq_orthRoots : EPilot.perpRoots .E7 = orthRoots (highRoot .E7) := by
  ext γ
  exact EPilot.mem_perpRoots_iff_iform (Or.inr (Or.inl rfl))

inductive E7Neighbour
  | high
  | seven
  | four
  deriving DecidableEq

namespace E7Neighbour

@[expose] def root : E7Neighbour → Fin (Tag.rank .E7) → ℤ
  | high => highRoot .E7
  | seven => Pi.single 6 1
  | four => Pi.single 3 1

@[expose] def nodes : E7Neighbour → Finset (Fin (Tag.rank .E7))
  | high => {1, 2, 3, 4, 5, 6}
  | seven => {0, 1, 2, 3, 4}
  | four => {0, 5, 6}

theorem iform_root_single_eq_zero_iff (N : E7Neighbour) (j : Fin (Tag.rank .E7)) :
    iform N.root (Pi.single j 1) = 0 ↔ j ∈ N.nodes := by
  revert j
  cases N <;> decide +kernel

theorem iform_root_root_eq_zero {N N' : E7Neighbour} (h : N ≠ N') : iform N.root N'.root = 0 := by
  revert h
  cases N <;> cases N' <;> decide +kernel

theorem iform_root_self (N : E7Neighbour) : iform N.root N.root = 2 := by
  cases N <;> decide +kernel

theorem isRoot_root (N : E7Neighbour) : IsRoot .E7 N.root := by
  cases N
  exacts [isRoot_highRoot _, isRoot_single _ _, isRoot_single _ _]

theorem root_mem_coverRoots (N : E7Neighbour) : N.root ∈ EPilot.coverRoots .E7 := by
  cases N <;> decide +kernel


@[expose] noncomputable def levi (K : Type) [Field K] (N : E7Neighbour) :
    Subgroup (adjointGroup .E7 K) :=
  (rootSpan .E7 K (orthRoots N.root)).subgroupOf (adjointGroup .E7 K)

theorem levi_high (K : Type) [Field K] : high.levi K = EPilot.perpLevi .E7 K := by
  rw [levi, EPilot.perpLevi, perpRoots_eq_orthRoots]
  rfl

end E7Neighbour

open E7Neighbour

theorem amalgamRoots_subset_orthRoots_iff_subset_nodes {J : Finset (Fin (Tag.rank .E7))}
    {N : E7Neighbour} : amalgamRoots J ⊆ orthRoots N.root ↔ J ⊆ N.nodes := by
  rw [amalgamRoots_subset_orthRoots_iff]
  exact forall₂_congr fun j _ => N.iform_root_single_eq_zero_iff j

@[expose] def amalgamPlacement (J : Finset (Fin (Tag.rank .E7))) : E7Neighbour :=
  if (0 : Fin (Tag.rank .E7)) ∈ J then
    (if (5 : Fin (Tag.rank .E7)) ∈ J ∨ (6 : Fin (Tag.rank .E7)) ∈ J then .four else .seven)
  else .high

theorem amalgamPlacement_of_zero_not_mem {J : Finset (Fin (Tag.rank .E7))}
    (h0 : (0 : Fin (Tag.rank .E7)) ∉ J) : amalgamPlacement J = .high := by
  rw [amalgamPlacement, ite_eq_right h0]

theorem amalgamPlacement_of_five_or_six_mem {J : Finset (Fin (Tag.rank .E7))}
    (h0 : (0 : Fin (Tag.rank .E7)) ∈ J)
    (h56 : (5 : Fin (Tag.rank .E7)) ∈ J ∨ (6 : Fin (Tag.rank .E7)) ∈ J) :
    amalgamPlacement J = .four := by
  rw [amalgamPlacement, ite_eq_left h0, ite_eq_left h56]

theorem amalgamPlacement_of_not_five_six {J : Finset (Fin (Tag.rank .E7))}
    (h0 : (0 : Fin (Tag.rank .E7)) ∈ J) (h5 : (5 : Fin (Tag.rank .E7)) ∉ J)
    (h6 : (6 : Fin (Tag.rank .E7)) ∉ J) : amalgamPlacement J = .seven := by
  rw [amalgamPlacement, ite_eq_left h0, ite_eq_right (not_or.2 ⟨h5, h6⟩)]

theorem mem_nodes_high_of_ne {j : Fin (Tag.rank .E7)} (h : j ≠ 0) : j ∈ high.nodes := by
  revert j
  decide

theorem mem_nodes_seven_of_ne {j : Fin (Tag.rank .E7)} (h5 : j ≠ 5) (h6 : j ≠ 6) :
    j ∈ seven.nodes := by
  revert j
  decide

theorem mem_nodes_four_of_ne {j : Fin (Tag.rank .E7)} (h1 : j ≠ 1) (h2 : j ≠ 2) (h3 : j ≠ 3)
    (h4 : j ≠ 4) : j ∈ four.nodes := by
  revert j
  decide

theorem eq_pair_of_card_le_two {J : Finset (Fin (Tag.rank .E7))} (hJ : J.card ≤ 2)
    {a b : Fin (Tag.rank .E7)} (hab : a ≠ b) (ha : a ∈ J) (hb : b ∈ J) : J = {a, b} := by
  have hsub : ({a, b} : Finset (Fin (Tag.rank .E7))) ⊆ J := by
    intro j hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    exacts [ha, hb]
  have h2 : ({a, b} : Finset (Fin (Tag.rank .E7))).card = 2 := Finset.card_pair hab
  exact (Finset.eq_of_subset_of_card_le hsub (h2 ▸ hJ)).symm

theorem subset_nodes_amalgamPlacement {J : Finset (Fin (Tag.rank .E7))} (hJ : J.card ≤ 2) :
    J ⊆ (amalgamPlacement J).nodes := by
  by_cases h0 : (0 : Fin (Tag.rank .E7)) ∈ J
  · by_cases h56 : (5 : Fin (Tag.rank .E7)) ∈ J ∨ (6 : Fin (Tag.rank .E7)) ∈ J
    · rw [amalgamPlacement_of_five_or_six_mem h0 h56]
      rcases h56 with h5 | h6
      · rw [eq_pair_of_card_le_two hJ (by decide) h0 h5]
        decide
      · rw [eq_pair_of_card_le_two hJ (by decide) h0 h6]
        decide
    · rw [not_or] at h56
      rw [amalgamPlacement_of_not_five_six h0 h56.1 h56.2]
      exact fun j hj => mem_nodes_seven_of_ne (fun h => h56.1 (h ▸ hj)) fun h => h56.2 (h ▸ hj)
  · rw [amalgamPlacement_of_zero_not_mem h0]
    exact fun j hj => mem_nodes_high_of_ne fun h => h0 (h ▸ hj)

theorem amalgamRoots_subset_orthRoots_placement {J : Finset (Fin (Tag.rank .E7))}
    (hJ : J.card ≤ 2) : amalgamRoots J ⊆ orthRoots (amalgamPlacement J).root :=
  amalgamRoots_subset_orthRoots_iff_subset_nodes.2 (subset_nodes_amalgamPlacement hJ)

theorem amalgamRoots_subset_high_or_seven_iff {J : Finset (Fin (Tag.rank .E7))}
    (hJ : J.card ≤ 2) :
    amalgamRoots J ⊆ orthRoots high.root ∨ amalgamRoots J ⊆ orthRoots seven.root ↔
      J ≠ {0, 5} ∧ J ≠ {0, 6} := by
  rw [amalgamRoots_subset_orthRoots_iff_subset_nodes,
    amalgamRoots_subset_orthRoots_iff_subset_nodes]
  constructor
  · rintro (h | h) <;> refine ⟨?_, ?_⟩ <;> rintro rfl <;> revert h <;> decide
  · rintro ⟨h05, h06⟩
    by_cases h0 : (0 : Fin (Tag.rank .E7)) ∈ J
    · right
      refine fun j hj => mem_nodes_seven_of_ne ?_ ?_
      · rintro rfl
        exact h05 (eq_pair_of_card_le_two hJ (by decide) h0 hj)
      · rintro rfl
        exact h06 (eq_pair_of_card_le_two hJ (by decide) h0 hj)
    · left
      exact fun j hj => mem_nodes_high_of_ne fun h => h0 (h ▸ hj)

theorem amalgamRoots_subset_high_or_four_iff {J : Finset (Fin (Tag.rank .E7))}
    (hJ : J.card ≤ 2) :
    amalgamRoots J ⊆ orthRoots high.root ∨ amalgamRoots J ⊆ orthRoots four.root ↔
      J ≠ {0, 1} ∧ J ≠ {0, 2} ∧ J ≠ {0, 3} ∧ J ≠ {0, 4} := by
  rw [amalgamRoots_subset_orthRoots_iff_subset_nodes,
    amalgamRoots_subset_orthRoots_iff_subset_nodes]
  constructor
  · rintro (h | h) <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert h <;> decide
  · rintro ⟨h01, h02, h03, h04⟩
    by_cases h0 : (0 : Fin (Tag.rank .E7)) ∈ J
    · right
      refine fun j hj => mem_nodes_four_of_ne ?_ ?_ ?_ ?_
      · rintro rfl
        exact h01 (eq_pair_of_card_le_two hJ (by decide) h0 hj)
      · rintro rfl
        exact h02 (eq_pair_of_card_le_two hJ (by decide) h0 hj)
      · rintro rfl
        exact h03 (eq_pair_of_card_le_two hJ (by decide) h0 hj)
      · rintro rfl
        exact h04 (eq_pair_of_card_le_two hJ (by decide) h0 hj)
    · left
      exact fun j hj => mem_nodes_high_of_ne fun h => h0 (h ▸ hj)

section Placement


variable {K : Type} [Field K]

theorem rootSpan_mono_E7 {S T : Set (Fin (Tag.rank .E7) → ℤ)} (h : S ⊆ T) :
    rootSpan .E7 K S ≤ rootSpan .E7 K T :=
  iSup₂_le fun α hα => le_iSup₂_of_le (f := fun α (_ : α ∈ T) => rootSubgroup .E7 K α) α (h hα)
    le_rfl


variable (K) in
noncomputable abbrev adjDatumE7 :
    CFSG.LieType.Universal.UniversalRootDatum ↥(adjointGroup .E7 K) :=
  adjDatum (rootOperatorFamily .E7) K

theorem map_subtype_rootGroup_E7 {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    ((adjDatumE7 K).rootGroup γ).map (adjointGroup .E7 K).subtype = rootSubgroup .E7 K γ := by
  change (CFSG.LieType.Steinberg.Adjoint.rootGroup (rootOperatorFamily .E7) K γ).map _ = _
  rw [CFSG.LieType.Steinberg.Adjoint.rootGroup_of_isRoot hγ,
    ← RootOperatorFamily.subgroupOf_rootSubgroup_eq (rootOperatorFamily .E7) K ⟨γ, hγ⟩,
    subgroupOf_map_subtype, inf_of_le_left (rootSubgroup_le_adjointGroup γ)]

theorem map_subtype_levi_adjDatumE7 (J : Finset (Fin (Tag.rank .E7))) :
    (CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J).map (adjointGroup .E7 K).subtype =
      rootSpan .E7 K (amalgamRoots J) := by
  have hj : ∀ j : Fin (Tag.rank .E7),
      (CFSG.LieType.CurtisTits.rankOne (adjDatumE7 K).rootGroup j).map
          (adjointGroup .E7 K).subtype =
        rootSubgroup .E7 K (Pi.single j 1) ⊔ rootSubgroup .E7 K (-Pi.single j 1) := fun j => by
    rw [CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup,
      map_subtype_rootGroup_E7 (isRoot_single _ j),
      map_subtype_rootGroup_E7 (isRoot_neg_single _ j)]
  rw [CFSG.LieType.CurtisTits.levi, Subgroup.map_iSup]
  simp_rw [Subgroup.map_iSup, hj]
  apply le_antisymm
  · refine iSup₂_le fun j hj => sup_le ?_ ?_
    · exact le_iSup₂_of_le (f := fun α (_ : α ∈ amalgamRoots J) => rootSubgroup .E7 K α)
        (Pi.single j 1) ⟨j, hj, Or.inl rfl⟩ le_rfl
    · exact le_iSup₂_of_le (f := fun α (_ : α ∈ amalgamRoots J) => rootSubgroup .E7 K α)
        (-Pi.single j 1) ⟨j, hj, Or.inr rfl⟩ le_rfl
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨j, hj, rfl | rfl⟩ := hγ
    · exact le_iSup₂_of_le (f := fun j (_ : j ∈ J) =>
        rootSubgroup .E7 K (Pi.single j 1) ⊔ rootSubgroup .E7 K (-Pi.single j 1)) j hj le_sup_left
    · exact le_iSup₂_of_le (f := fun j (_ : j ∈ J) =>
        rootSubgroup .E7 K (Pi.single j 1) ⊔ rootSubgroup .E7 K (-Pi.single j 1)) j hj le_sup_right

theorem levi_adjDatumE7_eq (J : Finset (Fin (Tag.rank .E7))) :
    CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J =
      (rootSpan .E7 K (amalgamRoots J)).subgroupOf (adjointGroup .E7 K) := by
  rw [← map_subtype_levi_adjDatumE7]
  exact (Subgroup.comap_map_eq_self_of_injective (adjointGroup .E7 K).subtype_injective _).symm

theorem levi_le_orthRoots {J : Finset (Fin (Tag.rank .E7))} {θ : Fin (Tag.rank .E7) → ℤ}
    (h : ∀ j ∈ J, iform θ (Pi.single j 1) = 0) :
    CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J ≤
      (rootSpan .E7 K (orthRoots θ)).subgroupOf (adjointGroup .E7 K) := by
  rw [levi_adjDatumE7_eq]
  exact Subgroup.subgroupOf_mono _ (rootSpan_mono_E7 (amalgamRoots_subset_orthRoots_iff.2 h))

theorem levi_le_neighbourLevi {J : Finset (Fin (Tag.rank .E7))} {N : E7Neighbour}
    (h : J ⊆ N.nodes) : CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J ≤ N.levi K :=
  levi_le_orthRoots fun j hj => (N.iform_root_single_eq_zero_iff j).2 (h hj)

theorem levi_le_perpLevi {J : Finset (Fin (Tag.rank .E7))} (h : (0 : Fin (Tag.rank .E7)) ∉ J) :
    CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J ≤ EPilot.perpLevi .E7 K := by
  rw [← levi_high]
  exact levi_le_neighbourLevi fun j hj => mem_nodes_high_of_ne fun h' => h (h' ▸ hj)

theorem leviAmalgam_le_placementLevi (J : {J : Finset (Fin (adjDatumE7 K).rank) // J.card ≤ 2}) :
    (adjDatumE7 K).leviAmalgam J ≤ (amalgamPlacement J.1).levi K :=
  levi_le_neighbourLevi (subset_nodes_amalgamPlacement J.2)

theorem leviAmalgam_le_perpLevi_or_seven_or_four
    (J : {J : Finset (Fin (adjDatumE7 K).rank) // J.card ≤ 2}) :
    ((0 : Fin (Tag.rank .E7)) ∉ J.1 → (adjDatumE7 K).leviAmalgam J ≤ EPilot.perpLevi .E7 K) ∧
    ((5 : Fin (Tag.rank .E7)) ∉ J.1 → (6 : Fin (Tag.rank .E7)) ∉ J.1 →
      (adjDatumE7 K).leviAmalgam J ≤ seven.levi K) ∧
    (J.1 ⊆ four.nodes → (adjDatumE7 K).leviAmalgam J ≤ four.levi K) ∧
    ((adjDatumE7 K).leviAmalgam J ≤ EPilot.perpLevi .E7 K ∨
      (adjDatumE7 K).leviAmalgam J ≤ seven.levi K ∨
      (adjDatumE7 K).leviAmalgam J ≤ four.levi K) := by
  refine ⟨levi_le_perpLevi, fun h5 h6 => levi_le_neighbourLevi fun j hj =>
    mem_nodes_seven_of_ne (fun h => h5 (h ▸ hj)) fun h => h6 (h ▸ hj),
    fun h => levi_le_neighbourLevi h, ?_⟩
  have h := leviAmalgam_le_placementLevi J
  unfold amalgamPlacement at h
  split_ifs at h with h0 h56
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · rw [levi_high] at h
    exact Or.inl h

end Placement

end CFSG.SeitzReduction.E7Pilot
