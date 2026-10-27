module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Sound
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQE8EightData

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQ17

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.Native
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section Sound


@[expose] def fK17 : Set (Fin Tag.E8.rank → ℤ) :=
  {γ | IsRoot Tag.E8 γ ∧ rr17 (List.ofFn γ) = List.replicate 2 0}

@[expose] def fS17 : Set (WeylGroup Tag.E8) :=
  {u | ∀ i : Fin Tag.E8.rank, rr17 (List.ofFn (u • (Pi.single i 1 : Fin Tag.E8.rank → ℤ))) =
    rr17 (List.ofFn (Pi.single i 1 : Fin Tag.E8.rank → ℤ))}

theorem imgTuple_mem_tuplesL17 {u : WeylGroup Tag.E8} (hu : u ∈ fS17) :
    imgTuple u ∈ tuplesL (gramL Tag.E8) (fibRootsG rr17 rootsN5) (simpleL Tag.E8)
      ((simpleL Tag.E8).map rr17)
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
      rr17 (List.ofFn (u • (Pi.single i' 1 : Fin Tag.E8.rank → ℤ)))),
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
      have h2 : ((simpleL Tag.E8).map rr17).getD i [] =
          rr17 ((simpleL Tag.E8).getD i []) := by
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

theorem fK17_eq_empty
    (h : (kerRootsL (fibRootsG rr17 rootsN5) (List.replicate 2 0)).isEmpty = true) :
    fK17 = ∅ := by
  have hK : kerRootsL (fibRootsG rr17 rootsN5) (List.replicate 2 0) = [] :=
    List.isEmpty_iff.1 h
  refine Set.eq_empty_iff_forall_notMem.2 fun γ hγ => ?_
  obtain ⟨hγr, hf⟩ := hγ
  have hmem : List.ofFn γ ∈ kerRootsL (fibRootsG rr17 rootsN5) (List.replicate 2 0) := by
    rw [kerRootsL, List.mem_map]
    refine ⟨(List.ofFn γ, iform γ γ, rr17 (List.ofFn γ)), List.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
    · rw [fibRootsG, List.mem_map]
      exact ⟨_, mem_rootsN5 hγr, rfl⟩
    · simpa using hf
  rw [hK] at hmem
  exact List.not_mem_nil hmem

theorem fam17_data
    (h : fam17OK (gramL Tag.E8) rootsN5 (simpleL Tag.E8)
      ((simpleL Tag.E8).map fun e => formB (gramL Tag.E8) e e) = true) :
    fK17 = ∅ ∧ ∀ u ∈ fS17, u = 1 := by
  unfold fam17OK at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hKe, hT⟩ := h
  refine ⟨fK17_eq_empty hKe, fun u hu => ?_⟩
  exact eq_of_imgTuple_eq ((hT _ (imgTuple_mem_tuplesL17 hu)).trans imgTuple_one.symm)

end Sound

end CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQ17

end
