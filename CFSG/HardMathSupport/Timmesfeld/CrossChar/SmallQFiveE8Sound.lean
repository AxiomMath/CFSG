module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Data

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.Native
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section Sound


@[expose] def famK' (fl : List ℤ) : Set (Fin Tag.E8.rank → ℤ) :=
  {γ | IsRoot Tag.E8 γ ∧ fib5 fl (List.ofFn γ) = List.replicate 4 0}

@[expose] def famS' (fl : List ℤ) : Set (WeylGroup Tag.E8) :=
  {u | ∀ i : Fin Tag.E8.rank, fib5 fl (List.ofFn (u • (Pi.single i 1 : Fin Tag.E8.rank → ℤ))) =
    fib5 fl (List.ofFn (Pi.single i 1 : Fin Tag.E8.rank → ℤ))}

theorem ofFn_getD_eq' {n : ℕ} {b : List ℤ} (hb : b.length = n) :
    List.ofFn (fun i : Fin n => b.getD i 0) = b := by
  refine List.ext_getElem (by simp [hb]) fun k h1 h2 => ?_
  simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
    Option.getD_some]

theorem mem_rootsN5 {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β) :
    (List.ofFn β, iform β β) ∈ rootsN5 := by
  rw [rootsN5, List.mem_map]
  exact ⟨List.ofFn β, isRoot_iff_mem_artifactRoots.1 hβ, by rw [formB_gramL]⟩

theorem isRoot_of_mem_rootsN5 {p : List ℤ × ℤ} (hp : p ∈ rootsN5) :
    ∃ β : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 β ∧ p = (List.ofFn β, iform β β) := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hp
  have hlen := length_of_mem_artifactRoots hl
  have hβl : List.ofFn (fun i : Fin Tag.E8.rank => l.getD i 0) = l := ofFn_getD_eq' hlen
  refine ⟨fun i => l.getD i 0, isRoot_iff_mem_artifactRoots.2 (hβl ▸ hl), ?_⟩
  have h2 : formB (gramL Tag.E8) l l = iform (fun i : Fin Tag.E8.rank => l.getD i 0)
      (fun i : Fin Tag.E8.rank => l.getD i 0) := by
    conv_lhs => rw [← hβl]
    exact formB_gramL _ _
  rw [hβl, h2]

theorem imgTuple_mem_tuplesL5 {fl : List ℤ} {u : WeylGroup Tag.E8} (hu : u ∈ famS' fl) :
    imgTuple u ∈ tuplesL (gramL Tag.E8) (fibRootsG (fib5 fl) rootsN5) (simpleL Tag.E8)
      ((simpleL Tag.E8).map (fib5 fl))
      ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) := by
  rw [tuplesL, length_simpleL]
  refine mem_foldl_extend Tag.E8.rank (imgTuple u) (by simp [imgTuple]) fun i hi => ⟨?_, ?_⟩
  · set i' : Fin Tag.E8.rank := ⟨i, hi⟩
    have hgi : (imgTuple u).getD i [] =
        List.ofFn (u • (Pi.single i' 1 : Fin Tag.E8.rank → ℤ)) := getD_imgTuple u i'
    rw [hgi, candL, List.mem_map]
    have hroot : IsRoot Tag.E8 (u • (Pi.single i' 1 : Fin Tag.E8.rank → ℤ)) :=
      IsRoot.smul (isRoot_single Tag.E8 i') u
    refine ⟨(List.ofFn (u • (Pi.single i' 1 : Fin Tag.E8.rank → ℤ)),
      iform (u • (Pi.single i' 1 : Fin Tag.E8.rank → ℤ)) (u • (Pi.single i' 1 : Fin Tag.E8.rank → ℤ)),
      fib5 fl (List.ofFn (u • (Pi.single i' 1 : Fin Tag.E8.rank → ℤ)))),
      List.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
    · rw [fibRootsG, List.mem_map]
      exact ⟨_, mem_rootsN5 hroot, rfl⟩
    · have hE : (simpleL Tag.E8).getD i [] =
          List.ofFn (Pi.single i' 1 : Fin Tag.E8.rank → ℤ) := getD_simpleL i'
      have h1 : ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e).getD i 0 =
          formB (gramL Tag.E8) ((simpleL Tag.E8).getD i []) ((simpleL Tag.E8).getD i []) := by
        rw [List.getD_eq_getElem _ _ (by simp [length_simpleL, hi]),
          List.getD_eq_getElem _ _ (by simp [length_simpleL, hi])]
        simp
      have h2 : ((simpleL Tag.E8).map (fib5 fl)).getD i [] =
          fib5 fl ((simpleL Tag.E8).getD i []) := by
        rw [List.getD_eq_getElem _ _ (by simp [length_simpleL, hi]),
          List.getD_eq_getElem _ _ (by simp [length_simpleL, hi])]
        simp
      rw [h1, h2, hE, formB_gramL, iform_smul, hu i']
      simp
  · rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    set i' : Fin Tag.E8.rank := ⟨i, hi⟩
    set j' : Fin Tag.E8.rank := ⟨j, by omega⟩
    rw [getD_take_of_lt hj, getD_imgTuple u j', getD_imgTuple u i', getD_simpleL j',
      getD_simpleL i', formB_gramL, formB_gramL, iform_smul]
    simp

theorem exists_root_of_mem_ker {fl x : List ℤ}
    (hx : x ∈ kerRootsL (fibRootsG (fib5 fl) rootsN5) (List.replicate 4 0)) :
    ∃ γ : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 γ ∧ x = List.ofFn γ ∧
      fib5 fl x = List.replicate 4 0 := by
  rw [kerRootsL, List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rw [List.mem_filter, fibRootsG, List.mem_map] at hp
  obtain ⟨⟨q, hq, rfl⟩, hpz⟩ := hp
  obtain ⟨γ, hγ, rfl⟩ := isRoot_of_mem_rootsN5 hq
  exact ⟨γ, hγ, rfl, by simpa using hpz⟩

theorem mem_ker_iff {fl : List ℤ} (γ : Fin Tag.E8.rank → ℤ) :
    γ ∈ famK' fl ↔ List.ofFn γ ∈ kerRootsL (fibRootsG (fib5 fl) rootsN5) (List.replicate 4 0) ∧
      IsRoot Tag.E8 γ := by
  constructor
  · rintro ⟨hγ, hf⟩
    refine ⟨?_, hγ⟩
    rw [kerRootsL, List.mem_map]
    refine ⟨(List.ofFn γ, iform γ γ, fib5 fl (List.ofFn γ)), List.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
    · rw [fibRootsG, List.mem_map]
      exact ⟨_, mem_rootsN5 hγ, rfl⟩
    · simpa using hf
  · rintro ⟨hk, hγ⟩
    obtain ⟨γ', -, hγ', hf⟩ := exists_root_of_mem_ker hk
    exact ⟨hγ, hf⟩

theorem imgTuple_mul_reflections {α β : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α)
    (hβ : IsRoot Tag.E8 β) :
    imgTuple (rootReflection α * rootReflection β) =
      List.map (reflB (gramL Tag.E8) (List.ofFn α))
        (List.map (reflB (gramL Tag.E8) (List.ofFn β)) (simpleL Tag.E8)) := by
  rw [imgTuple, simpleL_eq, List.map_ofFn, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [reflB_ofFn hβ, reflB_ofFn hα, mul_smul]

theorem famData_of_famOK5 (fl : List ℤ)
    (h : famOK5 (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
      ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) e8FourMat fl = true) :
    (famK' fl = ∅ ∧ ∀ u ∈ famS' fl, u = 1) ∨
      ∃ α β : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 α ∧ IsRoot Tag.E8 β ∧
        List.ofFn β = matVecL e8FourMat (List.ofFn α) ∧ famK' fl = {α, -α, β, -β} ∧
        ∀ u ∈ famS' fl, u = 1 ∨ u = rootReflection α ∨ u = rootReflection β ∨
          u = rootReflection α * rootReflection β := by
  have hT := fun {u : WeylGroup Tag.E8} (hu : u ∈ famS' fl) => imgTuple_mem_tuplesL5 hu
  unfold famOK5 at h
  simp only at h
  by_cases hKe : (kerRootsL (fibRootsG (fib5 fl) rootsN5) (List.replicate 4 0)).isEmpty = true
  · left
    rw [if_pos hKe] at h
    have hK : kerRootsL (fibRootsG (fib5 fl) rootsN5) (List.replicate 4 0) = [] :=
      List.isEmpty_iff.1 hKe
    refine ⟨Set.eq_empty_iff_forall_notMem.2 fun γ hγ => ?_, fun u hu => ?_⟩
    · have := ((mem_ker_iff γ).1 hγ).1
      rw [hK] at this
      exact List.not_mem_nil this
    · rw [List.all_eq_true] at h
      have h1 := h _ (hT hu)
      rw [beq_iff_eq] at h1
      exact eq_of_imgTuple_eq (h1.trans imgTuple_one.symm)
  · right
    rw [if_neg hKe, List.any_eq_true] at h
    obtain ⟨αl, hαl, hcond⟩ := h
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
      List.contains_iff_mem] at hcond
    obtain ⟨⟨⟨⟨hsub, hnα⟩, hMα⟩, hnMα⟩, hTall⟩ := hcond
    obtain ⟨α, hαr, rfl, -⟩ := exists_root_of_mem_ker hαl
    obtain ⟨β, hβr, hβl, -⟩ := exists_root_of_mem_ker hMα
    have hnβ : (matVecL e8FourMat (List.ofFn α)).map (- ·) = List.ofFn (-β) := by
      rw [hβl, List.map_ofFn]
      rfl
    have hnα' : (List.ofFn α).map (- ·) = List.ofFn (-α) := by
      rw [List.map_ofFn]
      rfl
    refine ⟨α, β, hαr, hβr, hβl.symm, ?_, ?_⟩
    · ext γ
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hγ
        have hk := ((mem_ker_iff γ).1 hγ).1
        have := hsub _ hk
        rcases this with ((h1 | h1) | h1) | h1
        · exact Or.inl (List.ofFn_injective h1)
        · rw [hnα'] at h1
          exact Or.inr (Or.inl (List.ofFn_injective h1))
        · rw [hβl] at h1
          exact Or.inr (Or.inr (Or.inl (List.ofFn_injective h1)))
        · rw [hnβ] at h1
          exact Or.inr (Or.inr (Or.inr (List.ofFn_injective h1)))
      · rintro (rfl | rfl | rfl | rfl)
        · exact (mem_ker_iff _).2 ⟨hαl, hαr⟩
        · exact (mem_ker_iff _).2 ⟨by rw [← hnα']; exact hnα, IsRoot.neg hαr⟩
        · exact (mem_ker_iff _).2 ⟨by rw [← hβl]; exact hMα, hβr⟩
        · exact (mem_ker_iff _).2 ⟨by rw [← hnβ]; exact hnMα, IsRoot.neg hβr⟩
    · intro u hu
      have h1 := hTall _ (hT hu)
      rcases h1 with ((h1 | h1) | h1) | h1
      · exact Or.inl (eq_of_imgTuple_eq (h1.trans imgTuple_one.symm))
      · exact Or.inr (Or.inl (eq_of_imgTuple_eq (h1.trans (imgTuple_rootReflection hαr).symm)))
      · rw [hβl] at h1
        exact Or.inr (Or.inr (Or.inl (eq_of_imgTuple_eq (h1.trans
          (imgTuple_rootReflection hβr).symm))))
      · rw [hβl] at h1
        exact Or.inr (Or.inr (Or.inr (eq_of_imgTuple_eq (h1.trans
          (imgTuple_mul_reflections hαr hβr).symm))))

end Sound

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

end
