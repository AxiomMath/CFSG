module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE7
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Defs

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

@[expose] def e7Top : Fin Tag.E7.rank := (0 : Fin 7)

@[expose] def e7FrameX : List (Fin Tag.E7.rank → ℤ) := [![0, 1, 1, 2, 2, 2, 1]]

@[expose] def e7FrameY : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 1, 1, 2, 1, 1, 1], ![0, 1, 1, 2, 2, 1, 0]]

@[expose] def e7FrameZ : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 1, 1, 2, 2, 1, 0], ![0, 1, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1, 1]]

@[expose] def e7FrameU : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 1, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 0, 0], ![0, 1, 0, 1, 1, 1, 1]]

@[expose] def e7FrameV : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 0, 1, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 1, 0],
    ![0, 1, 1, 2, 1, 0, 0]]

@[expose] def e7WordX : List (Fin Tag.E7.rank) := ([0, 2, 3, 4, 1, 3, 2, 0] : List (Fin 7))

@[expose] def e7WordY : List (Fin Tag.E7.rank) :=
  ([0, 2, 3, 4, 5, 6, 1, 3, 4, 5] : List (Fin 7))

@[expose] def e7WordZ : List (Fin Tag.E7.rank) :=
  ([0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2] : List (Fin 7))

@[expose] def e7WordU : List (Fin Tag.E7.rank) := ([0, 2, 3, 4, 5, 6] : List (Fin 7))

@[expose] def e7WordV : List (Fin Tag.E7.rank) :=
  ([0, 2, 3, 4, 5, 6, 1, 3, 4, 2, 3, 1] : List (Fin 7))

theorem e7WordX_map :
    [highRoot .E7].map (fun σ => e7WordX.foldr (reflect .E7) σ) = e7FrameX := by
  decide +kernel

theorem e7WordY_map :
    oddDerivE7YFrame.map (fun σ => e7WordY.foldr (reflect .E7) σ) = e7FrameY := by
  decide +kernel

theorem e7WordZ_map :
    oddDerivE7ZFrame.map (fun σ => e7WordZ.foldr (reflect .E7) σ) = e7FrameZ := by
  decide +kernel

theorem e7WordU_map :
    oddDerivE7UFrame.map (fun σ => e7WordU.foldr (reflect .E7) σ) = e7FrameU := by
  decide +kernel

theorem e7WordV_map :
    oddDerivE7VFrame.map (fun σ => e7WordV.foldr (reflect .E7) σ) = e7FrameV := by
  decide +kernel

theorem isRoot_of_mem_e7Frames :
    ∀ σ ∈ e7FrameX ++ e7FrameY ++ e7FrameZ ++ e7FrameU ++ e7FrameV,
      IsRoot .E7 σ ∧ σ e7Top = 0 ∧ 0 < height σ := by
  have h : ∀ σ ∈ e7FrameX ++ e7FrameY ++ e7FrameZ ++ e7FrameU ++ e7FrameV,
      List.ofFn σ ∈ Tag.artifactRoots .E7 ∧ σ e7Top = 0 ∧ 0 < height σ := by
    decide +kernel
  intro σ hσ
  obtain ⟨h1, h2, h3⟩ := h σ hσ
  exact ⟨isRoot_iff_mem_artifactRoots.2 h1, h2, h3⟩

variable (K : Type) [Field K]

@[expose] noncomputable def e7FramePt
    (F : List (Fin Tag.E7.rank → ℤ)) : adjointGroup .E7 K :=
  ⟨(F.map fun σ => pinnedX .E7 K σ 1).prod, list_prod_map_pinnedX_mem_adjointGroup F⟩

@[expose] noncomputable def e7Reps :
    List (adjointGroup .E7 K) :=
  [e7FramePt K e7FrameX, e7FramePt K e7FrameY, e7FramePt K e7FrameZ, e7FramePt K e7FrameU,
    e7FramePt K e7FrameV]

@[expose] def e7LeviNodes : Set (Fin Tag.E7.rank) := {i | i ≠ e7Top}

variable {K}

theorem isConj_e7FramePt_of_frameProdConj
    {F F' : List (Fin Tag.E7.rank → ℤ)}
    (h : FrameProdConj .E7 K F F') : IsConj (e7FramePt K F) (e7FramePt K F') := by
  obtain ⟨g, hg, e⟩ := h
  exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext (by simpa [e7FramePt] using e)⟩

theorem isRoot_of_mem_innerFrames_e7 :
    ∀ σ ∈ [highRoot .E7] ++ oddDerivE7YFrame ++ oddDerivE7ZFrame ++ oddDerivE7UFrame ++
      oddDerivE7VFrame, IsRoot .E7 σ := by
  have h : ∀ σ ∈ [highRoot .E7] ++ oddDerivE7YFrame ++ oddDerivE7ZFrame ++ oddDerivE7UFrame ++
      oddDerivE7VFrame, List.ofFn σ ∈ Tag.artifactRoots .E7 := by
    decide +kernel
  exact fun σ hσ => isRoot_iff_mem_artifactRoots.2 (h σ hσ)

theorem isConj_e7FramePt_inner
    [CharP K 2] :
    IsConj (e7FramePt K [highRoot .E7]) (e7FramePt K e7FrameX) ∧
      IsConj (e7FramePt K oddDerivE7YFrame) (e7FramePt K e7FrameY) ∧
      IsConj (e7FramePt K oddDerivE7ZFrame) (e7FramePt K e7FrameZ) ∧
      IsConj (e7FramePt K oddDerivE7UFrame) (e7FramePt K e7FrameU) ∧
      IsConj (e7FramePt K oddDerivE7VFrame) (e7FramePt K e7FrameV) := by
  have hr : ∀ F : List (Fin Tag.E7.rank → ℤ),
      (∀ σ ∈ F, σ ∈ [highRoot .E7] ++ oddDerivE7YFrame ++ oddDerivE7ZFrame ++
        oddDerivE7UFrame ++ oddDerivE7VFrame) →
        ∀ σ ∈ F, IsRoot .E7 σ := fun F hF σ hσ => isRoot_of_mem_innerFrames_e7 σ (hF σ hσ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := E8.frameProdConj_word (K := K) e7WordX (F := [highRoot .E7])
      (hr _ fun σ hσ => by simp_all)
    rw [e7WordX_map] at h
    exact isConj_e7FramePt_of_frameProdConj h
  · have h := E8.frameProdConj_word (K := K) e7WordY (F := oddDerivE7YFrame)
      (hr _ fun σ hσ => by simp_all)
    rw [e7WordY_map] at h
    exact isConj_e7FramePt_of_frameProdConj h
  · have h := E8.frameProdConj_word (K := K) e7WordZ (F := oddDerivE7ZFrame)
      (hr _ fun σ hσ => by simp_all)
    rw [e7WordZ_map] at h
    exact isConj_e7FramePt_of_frameProdConj h
  · have h := E8.frameProdConj_word (K := K) e7WordU (F := oddDerivE7UFrame)
      (hr _ fun σ hσ => by simp_all)
    rw [e7WordU_map] at h
    exact isConj_e7FramePt_of_frameProdConj h
  · have h := E8.frameProdConj_word (K := K) e7WordV (F := oddDerivE7VFrame)
      (hr _ fun σ hσ => by simp_all)
    rw [e7WordV_map] at h
    exact isConj_e7FramePt_of_frameProdConj h

theorem isConj_e7Reps
    [CharP K 2] :
    ∀ s ∈ innerRepsE7 K, ∃ x ∈ e7Reps K, IsConj s x := by
  obtain ⟨cX, cY, cZ, cU, cV⟩ := isConj_e7FramePt_inner (K := K)
  intro s hs
  simp only [innerRepsE7, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · refine ⟨e7FramePt K e7FrameX, by simp [e7Reps], ?_⟩
    have e : e7FramePt K [highRoot .E7] =
        ⟨pinnedX .E7 K (highRoot .E7) 1, pinnedX_mem_adjointGroup _ _⟩ :=
      Subtype.ext (by simp [e7FramePt])
    rw [← e]
    exact cX
  · exact ⟨e7FramePt K e7FrameY, by simp [e7Reps], cY⟩
  · exact ⟨e7FramePt K e7FrameZ, by simp [e7Reps], cZ⟩
  · exact ⟨e7FramePt K e7FrameU, by simp [e7Reps], cU⟩
  · exact ⟨e7FramePt K e7FrameV, by simp [e7Reps], cV⟩

theorem classesCover_e7Reps
    [Finite K] [CharP K 2] : Exc.ClassesCover (e7Reps K) := by
  intro t ht2 ht1
  obtain ⟨g, hg⟩ := exists_conj_mem_innerRepsE7 (by rw [sq]; exact ht2) ht1
  obtain ⟨x, hx, hsx⟩ := isConj_e7Reps _ hg
  exact ⟨x, hx, hsx.symm.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)⟩

theorem coe_mem_subsystemGroup_of_mem_e7Reps :
    ∀ x ∈ e7Reps K, (x : ModGL .E7 K) ∈ subsystemGroup .E7 K e7LeviNodes := by
  have hF : ∀ F : List (Fin Tag.E7.rank → ℤ),
      (∀ σ ∈ F, σ ∈ e7FrameX ++ e7FrameY ++ e7FrameZ ++ e7FrameU ++ e7FrameV) →
        ((e7FramePt K F : adjointGroup .E7 K) : ModGL .E7 K) ∈
          subsystemGroup .E7 K e7LeviNodes := by
    intro F hF
    refine list_prod_mem fun _ hg => ?_
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2, h3⟩ := isRoot_of_mem_e7Frames σ (hF σ hσ)
    have hpos : σ ∈ parabolicPosRoots .E7 e7LeviNodes :=
      ⟨⟨h1, fun i hi => by
        have hi0 : i = e7Top := by simpa [e7LeviNodes] using hi
        rw [hi0]
        exact h2⟩, h1, h3⟩
    exact parabolicLeviUnipotent_le_subsystemGroup
      ((le_iSup₂_of_le σ hpos le_rfl : rootSubgroup .E7 K σ ≤ parabolicLeviUnipotent .E7 K
        e7LeviNodes) (Subgroup.subset_closure ⟨1, rfl⟩))
  intro x hx
  simp only [e7Reps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact hF _ fun σ hσ => by simp_all

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
