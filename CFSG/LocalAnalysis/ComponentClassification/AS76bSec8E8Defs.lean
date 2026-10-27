module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE8
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE6Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcDefs
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

@[expose] def e8Top : Fin Tag.E8.rank := (7 : Fin 8)

@[expose] def e8FrameX : List (Fin Tag.E8.rank → ℤ) := [![2, 2, 3, 4, 3, 2, 1, 0]]

@[expose] def e8FrameY : List (Fin Tag.E8.rank → ℤ) :=
  [![1, 2, 2, 3, 2, 2, 1, 0], ![1, 1, 2, 3, 3, 2, 1, 0]]

@[expose] def e8FrameZ : List (Fin Tag.E8.rank → ℤ) :=
  [![1, 2, 2, 3, 2, 1, 0, 0], ![1, 1, 2, 3, 2, 1, 1, 0], ![1, 1, 2, 2, 2, 2, 1, 0]]

@[expose] def e8FrameU : List (Fin Tag.E8.rank → ℤ) :=
  [![1, 2, 2, 3, 2, 1, 0, 0], ![0, 1, 1, 2, 2, 2, 1, 0], ![1, 1, 2, 2, 1, 1, 1, 0],
    ![1, 1, 1, 2, 2, 1, 1, 0]]

@[expose] def e8WordX : List (Fin Tag.E8.rank) :=
  ([7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7] : List (Fin 8))

@[expose] def e8WordY : List (Fin Tag.E8.rank) :=
  ([7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0] : List (Fin 8))

@[expose] def e8WordZ : List (Fin Tag.E8.rank) :=
  ([7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6] : List (Fin 8))

@[expose] def e8WordU : List (Fin Tag.E8.rank) :=
  ([7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 1] : List (Fin 8))

theorem e8WordX_map :
    [highRoot .E8].map (fun σ => e8WordX.foldr (reflect .E8) σ) = e8FrameX := by
  decide +kernel

theorem e8WordY_map :
    oddDerivE8YFrame.map (fun σ => e8WordY.foldr (reflect .E8) σ) = e8FrameY := by
  decide +kernel

theorem e8WordZ_map :
    oddDerivE8ZFrame.map (fun σ => e8WordZ.foldr (reflect .E8) σ) = e8FrameZ := by
  decide +kernel

theorem e8WordU_map :
    oddDerivE8UFrame.map (fun σ => e8WordU.foldr (reflect .E8) σ) = e8FrameU := by
  decide +kernel

theorem isRoot_foldr_reflect {τ : Tag} (ω : List (Fin τ.rank)) {σ : Fin τ.rank → ℤ}
    (hσ : IsRoot τ σ) : IsRoot τ (ω.foldr (reflect τ) σ) := by
  induction ω with
  | nil => exact hσ
  | cons j ω ih => exact IsRoot.reflect j ih

theorem frameProdConj_word
    {τ : Tag} {K : Type} [Field K] [CharP K 2]
    (ω : List (Fin τ.rank)) {F : List (Fin τ.rank → ℤ)} (hF : ∀ σ ∈ F, IsRoot τ σ) :
    FrameProdConj τ K F (F.map fun σ => ω.foldr (reflect τ) σ) := by
  induction ω generalizing F with
  | nil =>
    have e : (F.map fun σ => ([] : List (Fin τ.rank)).foldr (reflect τ) σ) = F := by
      conv_rhs => rw [← List.map_id F]
      rfl
    rw [e]
    exact FrameProdConj.refl F
  | cons i ω ih =>
    have hF' : ∀ σ ∈ F.map (fun σ => ω.foldr (reflect τ) σ), IsRoot τ σ := by
      intro σ hσ
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hσ
      exact isRoot_foldr_reflect ω (hF ρ hρ)
    have h₂ := frameProdConj_map_reflect (K := K) i hF'
    rw [List.map_map] at h₂
    exact (ih hF).trans h₂

theorem isRoot_of_mem_e8Frames :
    ∀ σ ∈ e8FrameX ++ e8FrameY ++ e8FrameZ ++ e8FrameU,
      IsRoot .E8 σ ∧ σ e8Top = 0 ∧ 0 < height σ := by
  have h : ∀ σ ∈ e8FrameX ++ e8FrameY ++ e8FrameZ ++ e8FrameU,
      List.ofFn σ ∈ Tag.artifactRoots .E8 ∧ σ e8Top = 0 ∧ 0 < height σ := by
    decide +kernel
  intro σ hσ
  obtain ⟨h1, h2, h3⟩ := h σ hσ
  exact ⟨isRoot_iff_mem_artifactRoots.2 h1, h2, h3⟩

variable (K : Type) [Field K]

@[expose] noncomputable def e8FramePt
    (F : List (Fin Tag.E8.rank → ℤ)) : adjointGroup .E8 K :=
  ⟨(F.map fun σ => pinnedX .E8 K σ 1).prod, list_prod_map_pinnedX_mem_adjointGroup F⟩

@[expose] noncomputable def e8Reps :
    List (adjointGroup .E8 K) :=
  [e8FramePt K e8FrameX, e8FramePt K e8FrameY, e8FramePt K e8FrameZ, e8FramePt K e8FrameU]

@[expose] def e8LeviNodes : Set (Fin Tag.E8.rank) := {i | i ≠ e8Top}

variable {K}

theorem isConj_e8FramePt_of_frameProdConj
    {F F' : List (Fin Tag.E8.rank → ℤ)}
    (h : FrameProdConj .E8 K F F') : IsConj (e8FramePt K F) (e8FramePt K F') := by
  obtain ⟨g, hg, e⟩ := h
  exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext (by simpa [e8FramePt] using e)⟩

theorem isRoot_of_mem_innerFrames :
    ∀ σ ∈ [highRoot .E8] ++ oddDerivE8YFrame ++ oddDerivE8ZFrame ++ oddDerivE8UFrame,
      IsRoot .E8 σ := by
  have h : ∀ σ ∈ [highRoot .E8] ++ oddDerivE8YFrame ++ oddDerivE8ZFrame ++ oddDerivE8UFrame,
      List.ofFn σ ∈ Tag.artifactRoots .E8 := by
    decide +kernel
  exact fun σ hσ => isRoot_iff_mem_artifactRoots.2 (h σ hσ)

theorem isConj_e8Reps
    [CharP K 2] :
    ∀ s ∈ innerRepsE8 K, ∃ x ∈ e8Reps K, IsConj s x := by
  have hr : ∀ F : List (Fin Tag.E8.rank → ℤ),
      (∀ σ ∈ F, σ ∈ [highRoot .E8] ++ oddDerivE8YFrame ++ oddDerivE8ZFrame ++ oddDerivE8UFrame) →
        ∀ σ ∈ F, IsRoot .E8 σ := fun F hF σ hσ => isRoot_of_mem_innerFrames σ (hF σ hσ)
  intro s hs
  simp only [innerRepsE8, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · refine ⟨e8FramePt K e8FrameX, by simp [e8Reps], ?_⟩
    have h := frameProdConj_word (K := K) e8WordX (F := [highRoot .E8])
      (hr _ fun σ hσ => by simp_all)
    rw [e8WordX_map] at h
    have e : e8FramePt K [highRoot .E8] =
        ⟨pinnedX .E8 K (highRoot .E8) 1, pinnedX_mem_adjointGroup _ _⟩ :=
      Subtype.ext (by simp [e8FramePt])
    rw [← e]
    exact isConj_e8FramePt_of_frameProdConj h
  · refine ⟨e8FramePt K e8FrameY, by simp [e8Reps], ?_⟩
    have h := frameProdConj_word (K := K) e8WordY (F := oddDerivE8YFrame)
      (hr _ fun σ hσ => by simp_all)
    rw [e8WordY_map] at h
    exact isConj_e8FramePt_of_frameProdConj h
  · refine ⟨e8FramePt K e8FrameZ, by simp [e8Reps], ?_⟩
    have h := frameProdConj_word (K := K) e8WordZ (F := oddDerivE8ZFrame)
      (hr _ fun σ hσ => by simp_all)
    rw [e8WordZ_map] at h
    exact isConj_e8FramePt_of_frameProdConj h
  · refine ⟨e8FramePt K e8FrameU, by simp [e8Reps], ?_⟩
    have h := frameProdConj_word (K := K) e8WordU (F := oddDerivE8UFrame)
      (hr _ fun σ hσ => by simp_all)
    rw [e8WordU_map] at h
    exact isConj_e8FramePt_of_frameProdConj h

theorem classesCover_e8Reps
    [Finite K] [CharP K 2] : Exc.ClassesCover (e8Reps K) := by
  intro t ht2 ht1
  obtain ⟨g, hg⟩ := classListE8_exists_conj_mem_innerRepsE8 (by rw [sq]; exact ht2) ht1
  obtain ⟨x, hx, hsx⟩ := isConj_e8Reps _ hg
  exact ⟨x, hx, hsx.symm.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)⟩

theorem coe_mem_subsystemGroup_of_mem_e8Reps :
    ∀ x ∈ e8Reps K, (x : ModGL .E8 K) ∈ subsystemGroup .E8 K e8LeviNodes := by
  have hF : ∀ F : List (Fin Tag.E8.rank → ℤ),
      (∀ σ ∈ F, σ ∈ e8FrameX ++ e8FrameY ++ e8FrameZ ++ e8FrameU) →
        ((e8FramePt K F : adjointGroup .E8 K) : ModGL .E8 K) ∈
          subsystemGroup .E8 K e8LeviNodes := by
    intro F hF
    refine list_prod_mem fun _ hg => ?_
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2, h3⟩ := isRoot_of_mem_e8Frames σ (hF σ hσ)
    have hpos : σ ∈ parabolicPosRoots .E8 e8LeviNodes :=
      ⟨⟨h1, fun i hi => by
        have hi7 : i = e8Top := by simpa [e8LeviNodes] using hi
        rw [hi7]
        exact h2⟩, h1, h3⟩
    exact parabolicLeviUnipotent_le_subsystemGroup
      ((le_iSup₂_of_le σ hpos le_rfl : rootSubgroup .E8 K σ ≤ parabolicLeviUnipotent .E8 K
        e8LeviNodes) (Subgroup.subset_closure ⟨1, rfl⟩))
  intro x hx
  simp only [e8Reps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> exact hF _ fun σ hσ => by simp_all

end CFSG.ComponentClassification.RankTwoExceptional.E8
