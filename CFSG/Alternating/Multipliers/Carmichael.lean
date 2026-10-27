module

public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm

public section

namespace CFSG.Alternating.Multipliers

open Subgroup CFSG.LieType.Multipliers CFSG.LocalAnalysis.ComponentInitial

theorem finite_closure_of_carmichael {G : Type*} [Group G] :
    ∀ (m : ℕ) (a : Fin m → G), (∀ i, a i ^ 3 = 1) → (∀ i j, i ≠ j → (a i * a j) ^ 2 = 1) →
      Finite (closure (Set.range a)) := by
  intro m
  induction m with
  | zero =>
    intro a _ _
    rw [Set.range_eq_empty, Subgroup.closure_empty]
    exact Finite.of_subsingleton
  | succ m ih =>
    intro a ha haa
    set b := a (Fin.last m)
    set a' : Fin m → G := fun i => a i.castSucc
    set H := closure (Set.range a')
    have hH : Finite H := ih a' (fun i => ha _) fun i j hij =>
      haa _ _ (fun h => hij (Fin.castSucc_injective _ h))
    have hHle : H ≤ closure (Set.range a) :=
      closure_mono (Set.range_subset_iff.mpr fun i => ⟨i.castSucc, rfl⟩)
    have hrep : ∀ k, carmichaelRep a' b k ∈ closure (Set.range a) := by
      have hb : b ∈ closure (Set.range a) := subset_closure ⟨_, rfl⟩
      rintro (k | i)
      · fin_cases k
        · exact one_mem _
        · exact hb
        · exact pow_mem hb _
      · exact mul_mem (subset_closure ⟨_, rfl⟩) (pow_mem hb _)
    have hcov : ∀ g ∈ closure (Set.range a), ∃ k, ∃ h ∈ H, g = carmichaelRep a' b k * h := by
      have hstep : ∀ x ∈ Set.range a, ∀ g, (∃ k, ∃ h ∈ H, g = carmichaelRep a' b k * h) →
          ∃ k, ∃ h ∈ H, x * g = carmichaelRep a' b k * h := by
        rintro x ⟨j, rfl⟩ g ⟨k, h, hh, rfl⟩
        have hx : a j = b ∨ ∃ i, a j = a' i := by
          cases j using Fin.lastCases with
          | last => exact Or.inl rfl
          | cast i => exact Or.inr ⟨i, rfl⟩
        obtain ⟨k', h', hh', he⟩ := exists_mul_carmichaelRep_eq a' b (fun i => ha _) (ha _)
          (fun i => haa _ _ (Fin.castSucc_ne_last i)) (fun i j hij => haa _ _
            (fun h => hij (Fin.castSucc_injective _ h))) (a j) hx k
        exact ⟨k', h' * h, H.mul_mem hh' hh, by rw [← mul_assoc, he, mul_assoc]⟩
      intro g hg
      induction hg using closure_induction_left with
      | one => exact ⟨.inl 0, 1, H.one_mem, by simp [carmichaelRep]⟩
      | mul_left x hx g _ ih => exact hstep x hx g ih
      | inv_mul_cancel x hx g _ ih =>
        obtain ⟨j, rfl⟩ := hx
        rw [inv_eq_sq_of_pow_three (ha j), sq, mul_assoc]
        exact hstep _ ⟨j, rfl⟩ _ (hstep _ ⟨j, rfl⟩ g ih)
    let f : (Fin 3 ⊕ Fin m) × H → closure (Set.range a) := fun p =>
      ⟨carmichaelRep a' b p.1 * p.2, mul_mem (hrep _) (hHle p.2.2)⟩
    refine Finite.of_surjective f ?_
    rintro ⟨g, hg⟩
    obtain ⟨k, h, hh, rfl⟩ := hcov g hg
    exact ⟨(k, ⟨h, hh⟩), rfl⟩

@[expose] def carmichaelWords (m : ℕ) : List (List (Fin m × Bool)) :=
  (List.finRange m).map (fun i => [(i, true), (i, true), (i, true)]) ++
    (List.finRange m).flatMap fun i => ((List.finRange m).filter fun j => i < j).map fun j =>
      [(i, true), (j, true), (i, true), (j, true)]

theorem mk_cube {G : Type*} [Group G] {m : ℕ} (f : Fin m → G) (i : Fin m) :
    FreeGroup.lift f (FreeGroup.mk [(i, true), (i, true), (i, true)]) = f i ^ 3 := by
  simp [FreeGroup.lift_mk, pow_succ, mul_assoc]

theorem mk_sq {G : Type*} [Group G] {m : ℕ} (f : Fin m → G) (i j : Fin m) :
    FreeGroup.lift f (FreeGroup.mk [(i, true), (j, true), (i, true), (j, true)]) =
      (f i * f j) ^ 2 := by
  simp [FreeGroup.lift_mk, sq, mul_assoc]

theorem lift_carmichaelWords_eq_one {G : Type*} [Group G] {m : ℕ} {f : Fin m → G}
    (h3 : ∀ i, f i ^ 3 = 1) (h2 : ∀ i j, i ≠ j → (f i * f j) ^ 2 = 1) :
    ∀ r ∈ wordSet (carmichaelWords m), FreeGroup.lift f r = 1 := by
  intro r hr
  simp only [wordSet, carmichaelWords, Set.mem_ofPred_eq, List.map_append, List.map_map,
    List.mem_append, List.mem_map, List.mem_finRange, true_and, List.mem_flatMap,
    List.mem_filter, decide_eq_true_eq, Function.comp_apply] at hr
  rcases hr with ⟨i, rfl⟩ | ⟨w, ⟨i, j, hij, rfl⟩, rfl⟩
  · exact (mk_cube f i).trans (h3 i)
  · exact (mk_sq f i j).trans (h2 i j (ne_of_lt hij))

theorem of_carmichael (m : ℕ) :
    (∀ i, (PresentedGroup.of i : PresentedGroup (wordSet (carmichaelWords m))) ^ 3 = 1) ∧
      ∀ i j, i ≠ j → ((PresentedGroup.of i : PresentedGroup (wordSet (carmichaelWords m))) *
        PresentedGroup.of j) ^ 2 = 1 := by
  have hl : ∀ w ∈ carmichaelWords m,
      FreeGroup.lift (PresentedGroup.of : Fin m → PresentedGroup (wordSet (carmichaelWords m)))
        (FreeGroup.mk w) = 1 := fun w hw => by
    have h := (IsPresentation.presentedGroup (wordSet (carmichaelWords m))).lift_eq_one
      (r := FreeGroup.mk w) (List.mem_map_of_mem hw)
    exact h
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [← mk_cube (PresentedGroup.of : Fin m → PresentedGroup (wordSet (carmichaelWords m)))]
    exact hl _ (List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange i)))
  · rcases lt_or_gt_of_ne hij with h | h
    · rw [← mk_sq (PresentedGroup.of : Fin m → PresentedGroup (wordSet (carmichaelWords m)))]
      refine hl _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩))
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_finRange j, by simpa using h⟩)
    · refine sq_mul_comm_eq_one ?_
      rw [← mk_sq (PresentedGroup.of : Fin m → PresentedGroup (wordSet (carmichaelWords m)))]
      refine hl _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, List.mem_finRange j, ?_⟩))
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_finRange i, by simpa using h⟩)

theorem isPresentation_carmichael (m : ℕ) :
    IsPresentation (altThreeCycle (n := m)) (wordSet (carmichaelWords m)) := by
  obtain ⟨h3, h2⟩ := of_carmichael m
  have hfin : Finite (PresentedGroup (wordSet (carmichaelWords m))) := by
    have h := finite_closure_of_carmichael m PresentedGroup.of h3 h2
    rw [PresentedGroup.closure_range_of] at h
    exact Finite.of_equiv _ Subgroup.topEquiv.toEquiv
  refine IsPresentation.of_card_le (lift_carmichaelWords_eq_one altThreeCycle_pow_three
    fun i j hij => altThreeCycle_mul_sq hij) closure_altThreeCycle ?_
  have h := card_closure_le_of_carmichael m PresentedGroup.of h3 h2
  rw [PresentedGroup.closure_range_of, card_top] at h
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin (m + 2)), Fintype.card_fin]
  exact h

@[expose] def carmichaelPairs (m : ℕ) (i : Fin m) :
    List (List (Fin m × Bool) × List (Fin m × Bool)) :=
  [(commWord [(finRotate m i, true)] [(finRotate m (finRotate m i), true)], [(i, true)])]

@[expose] def carmichaelRel01 (m : ℕ) : List (Fin (m + 2) × Bool) :=
  [(0, true), (1, true), (0, true), (1, true)]

theorem carmichaelRel01_mem (m : ℕ) : carmichaelRel01 m ∈ carmichaelWords (m + 2) := by
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨0, List.mem_finRange 0, ?_⟩)
  exact List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_finRange 1, by simp⟩)

end CFSG.Alternating.Multipliers
