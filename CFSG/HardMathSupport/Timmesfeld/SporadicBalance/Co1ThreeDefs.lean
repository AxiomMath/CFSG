module

public import CFSG.Sporadic.Schreier.Co1SplitLocal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeData

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree

@[expose] noncomputable def lG : List GL24 :=
  (List.range 6).map (fun i => W (CFSG.Sporadic.Co1Schreier.Data.elemIdx.getD i 0)) ++
    [g 0, g 1, g 2] ++ dagG [A₁, A₂] (Co1T.Data.dagWords.map Native.decWord)

theorem lG_mem : ∀ x ∈ lG, x ∈ GA := by
  have hE : ∀ i < 6, W (CFSG.Sporadic.Co1Schreier.Data.elemIdx.getD i 0) ∈ GA := by
    intro i hi
    have h : W (CFSG.Sporadic.Co1Schreier.Data.elemIdx.getD i 0) = a ⟨i, hi⟩ := rfl
    rw [h]
    exact A_le_GA (Subgroup.subset_closure (Set.mem_union_left _ (a_mem_E _)))
  have hg : ∀ i : Fin 3, g i ∈ GA := by
    intro i
    apply A_le_GA
    fin_cases i
    · exact Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_insert _ _))
    · exact Subgroup.subset_closure (Set.mem_union_right _
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    · exact Subgroup.subset_closure (Set.mem_union_right _
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))
  intro x hx
  simp only [lG, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with ((⟨i, hi, rfl⟩ | rfl | rfl | rfl) | hx)
  · exact hE i hi
  · exact hg 0
  · exact hg 1
  · exact hg 2
  · have hbase : ∀ y ∈ [A₁, A₂], y ∈ GA := by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with h | h
      · rw [h]; exact A₁_mem
      · rw [h]; exact A₂_mem
    exact dagG_mem hbase _ x hx

@[expose] noncomputable def wG (w : List ℕ) : ↥GA :=
  ⟨wordG lG (Native.decWord w), wordG_mem lG_mem _⟩

@[expose] noncomputable def eltG (fs : List ↥GA) (b : List ℕ) : ↥GA :=
  (fs.zip b).foldl (fun acc fb => acc * fb.1 ^ fb.2) 1

@[expose] noncomputable def aGA : List ↥GA :=
  (List.finRange 6).map fun i => (⟨a i, A_le_GA (Subgroup.subset_closure
    (Set.mem_union_left _ (a_mem_E i)))⟩ : ↥GA)

@[expose] noncomputable def root (j : ℕ) : ↥GA := wG (Co1T.Data.rootWords.getD j [])

@[expose] noncomputable def qG : List ↥GA := Co1T.Data.qGenWords.map wG

@[expose] noncomputable def Qg : Subgroup ↥GA := Subgroup.closure {x | x ∈ qG}

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

end
