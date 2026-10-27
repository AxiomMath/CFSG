module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Set
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Measure

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem ncard_kStarComponents_le (hq : QuasisimpleTwoPartInput) (hKK : KStarKProper G)
    {N C : Subgroup G} (hN : IsSolomonChoice N)
    (hv : IsKBalanced C → ¬ solomonKStarOf C ≤ solomonKStarOf (⊤ : Subgroup G)) :
    (kStarComponents C).ncard ≤ (kStarComponents N).ncard := by
  by_contra hlt
  push Not at hlt
  have h2 : 2 ≤ (kStarComponents N).ncard := by
    obtain ⟨r, Kf, hinj, hiff, h2r, -⟩ := hN.1
    have hmem : ∀ i, Kf i ∈ kStarComponents N := fun i => (hiff (Kf i)).mpr ⟨i, rfl⟩
    have hne : Kf ⟨0, by omega⟩ ≠ Kf ⟨1, h2r⟩ := fun h => by
      have := hinj h
      simp at this
    rw [← Set.ncard_pair hne]
    exact Set.ncard_le_ncard (Set.insert_subset (hmem _) (Set.singleton_subset_iff.mpr (hmem _)))
  have hC : IsKBalanced C := isKBalanced_of_three_le_ncard hq hKK (by omega)
  exact absurd (ncard_le_of_isSolomonChoice hN hC (hv hC)) (not_le.mpr hlt)

noncomputable abbrev otherComponents (N K : Subgroup G) : Finset (Subgroup G) :=
  (Set.toFinite (kStarComponents N \ {K})).toFinset

noncomputable abbrev pumpFinset (K' C : Subgroup G) : Finset (Subgroup G) :=
  (Set.toFinite (pumpSet K' C)).toFinset

theorem sum_card_pumpFinset_le {N K : Subgroup G} (hK : K ∈ kStarComponents N) {b : G}
    (hbK : b ∈ K) (hb2 : orderOf b = 2) :
    ∑ K' ∈ otherComponents N K, (pumpFinset K' (centralizer ({b} : Set G))).card ≤
      (kStarComponents (centralizer ({b} : Set G))).ncard := by
  classical
  set C := centralizer ({b} : Set G) with hC
  have hdisj : ((otherComponents N K : Finset (Subgroup G)) : Set (Subgroup G)).PairwiseDisjoint
      (fun K' => pumpFinset K' C) := by
    intro K' hK' K'' hK'' hne
    simp only [Set.Finite.coe_toFinset, Set.mem_sdiff, Set.mem_singleton_iff] at hK' hK''
    change Disjoint (pumpFinset K' C) (pumpFinset K'' C)
    rw [Set.Finite.disjoint_toFinset]
    exact pumpSet_disjoint hK'.1 hK''.1 hne
      (mem_coreActionKernel_of_ne hK hK'.1 (Ne.symm hK'.2) hbK)
      (mem_coreActionKernel_of_ne hK hK''.1 (Ne.symm hK''.2) hbK) hb2
  rw [← Finset.card_biUnion hdisj, Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  apply Finset.card_le_card
  intro M hM
  simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset] at hM
  obtain ⟨K', -, hM'⟩ := hM
  rw [Set.Finite.mem_toFinset]
  exact hM'.1

theorem two_pumpSet_structure (hq : QuasisimpleTwoPartInput) (hKK : KStarKProper G)
    {N K K₀ : Subgroup G} (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N)
    (hK₀ : K₀ ∈ kStarComponents N) (hKK₀ : K ≠ K₀) {b : G} (hbK : b ∈ K) (hb2 : orderOf b = 2)
    (hv : IsKBalanced (centralizer ({b} : Set G)) →
      ¬ solomonKStarOf (centralizer ({b} : Set G)) ≤ solomonKStarOf (⊤ : Subgroup G))
    (h2 : 2 ≤ (pumpSet K₀ (centralizer ({b} : Set G))).ncard) :
    (pumpSet K₀ (centralizer ({b} : Set G))).ncard = 2 ∧
      (∀ K' ∈ kStarComponents N, K' ≠ K → K' ≠ K₀ →
        (pumpSet K' (centralizer ({b} : Set G))).ncard = 1) ∧
      (kStarComponents (centralizer ({b} : Set G))).ncard = (kStarComponents N).ncard ∧
      ∀ M ∈ kStarComponents (centralizer ({b} : Set G)), ∃ K' ∈ kStarComponents N, K' ≠ K ∧
        M ∈ pumpSet K' (centralizer ({b} : Set G)) := by
  classical
  set C := centralizer ({b} : Set G) with hC
  set T := otherComponents N K with hT
  have hcardT : T.card + 1 = (kStarComponents N).ncard := by
    rw [hT, ← Set.ncard_eq_toFinset_card _ (Set.toFinite _), Set.ncard_sdiff_singleton_of_mem hK]
    have : 1 ≤ (kStarComponents N).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨K, hK⟩
    omega
  have hK₀T : K₀ ∈ T := by
    rw [hT, Set.Finite.mem_toFinset]
    exact ⟨hK₀, fun h => hKK₀ (Set.mem_singleton_iff.mp h).symm⟩
  have hfc : ∀ K' : Subgroup G, (pumpFinset K' C).card = (pumpSet K' C).ncard := fun K' =>
    (Set.ncard_eq_toFinset_card _ (Set.toFinite _)).symm
  have hone : ∀ K' ∈ T, 1 ≤ (pumpFinset K' C).card := by
    intro K' hK'
    rw [hT, Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_singleton_iff] at hK'
    rw [hfc]
    exact (Set.ncard_pos (Set.toFinite _)).mpr
      (pumpSet_nonempty hK'.1 (mem_coreActionKernel_of_ne hK hK'.1 (Ne.symm hK'.2) hbK) hb2)
  have hsum : ∑ K' ∈ T, (pumpFinset K' C).card ≤ (kStarComponents C).ncard :=
    sum_card_pumpFinset_le hK hbK hb2
  have hle : (kStarComponents C).ncard ≤ (kStarComponents N).ncard :=
    ncard_kStarComponents_le hq hKK hN hv
  have hsplit : (pumpFinset K₀ C).card + ∑ K' ∈ T.erase K₀, (pumpFinset K' C).card =
      ∑ K' ∈ T, (pumpFinset K' C).card :=
    Finset.add_sum_erase T (fun K' => (pumpFinset K' C).card) hK₀T
  have hrest : (T.erase K₀).card ≤ ∑ K' ∈ T.erase K₀, (pumpFinset K' C).card := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun K' hK' => hone K' (Finset.mem_of_mem_erase hK')
  have hcardE : (T.erase K₀).card + 1 = T.card := Finset.card_erase_add_one hK₀T
  have h2' : 2 ≤ (pumpFinset K₀ C).card := by rw [hfc]; exact h2
  have hS : ∑ K' ∈ T, (pumpFinset K' C).card = (kStarComponents N).ncard := by omega
  have hK₀2 : (pumpFinset K₀ C).card = 2 := by omega
  have hrestEq : ∑ K' ∈ T.erase K₀, (pumpFinset K' C).card = (T.erase K₀).card := by omega
  refine ⟨by rw [← hfc]; exact hK₀2, ?_, by omega, ?_⟩
  · intro K' hK' hKK' hK'K₀
    have hK'T : K' ∈ T.erase K₀ := by
      rw [Finset.mem_erase, hT, Set.Finite.mem_toFinset]
      exact ⟨hK'K₀, hK', fun h => hKK' (Set.mem_singleton_iff.mp h)⟩
    have hall := (Finset.sum_eq_sum_iff_of_le (s := T.erase K₀) (f := fun _ => 1)
      (g := fun K' => (pumpFinset K' C).card)
      (fun K'' hK'' => hone K'' (Finset.mem_of_mem_erase hK''))).mp
      (by rw [← Finset.card_eq_sum_ones]; exact hrestEq.symm)
    rw [← hfc]
    exact (hall K' hK'T).symm
  ·
    intro M hM
    by_contra hno
    push Not at hno
    have hsub : T.biUnion (fun K' => pumpFinset K' C) ⊂
        (Set.toFinite (kStarComponents C)).toFinset := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun h => ?_⟩
      · intro M' hM'
        simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset] at hM'
        obtain ⟨K', -, hM''⟩ := hM'
        rw [Set.Finite.mem_toFinset]
        exact hM''.1
      · have hMf : M ∈ (Set.toFinite (kStarComponents C)).toFinset := by
          rw [Set.Finite.mem_toFinset]; exact hM
        rw [← h] at hMf
        simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset] at hMf
        obtain ⟨K', hK'T, hMK'⟩ := hMf
        rw [hT, Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_singleton_iff] at hK'T
        exact hno K' hK'T.1 hK'T.2 hMK'
    have hlt := Finset.card_lt_card hsub
    have hdisj : ((T : Finset (Subgroup G)) : Set (Subgroup G)).PairwiseDisjoint
        (fun K' => pumpFinset K' C) := by
      intro K' hK' K'' hK'' hne
      simp only [Set.Finite.coe_toFinset, Set.mem_sdiff, Set.mem_singleton_iff, hT] at hK' hK''
      change Disjoint (pumpFinset K' C) (pumpFinset K'' C)
      rw [Set.Finite.disjoint_toFinset]
      exact pumpSet_disjoint hK'.1 hK''.1 hne
        (mem_coreActionKernel_of_ne hK hK'.1 (Ne.symm hK'.2) hbK)
        (mem_coreActionKernel_of_ne hK hK''.1 (Ne.symm hK''.2) hbK) hb2
    rw [Finset.card_biUnion hdisj, ← Set.ncard_eq_toFinset_card _ (Set.toFinite _)] at hlt
    omega

end CFSG.ComponentClassification.Sol76T13
