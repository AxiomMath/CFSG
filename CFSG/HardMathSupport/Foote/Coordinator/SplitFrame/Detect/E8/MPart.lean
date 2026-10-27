module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false

@[expose] def sRootsList : List (Fin Tag.E8.rank → ℤ) :=
  [![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 1, 1],
    ![2, 3, 4, 6, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 4, 2, 1], ![2, 3, 4, 6, 5, 4, 3, 1]]

theorem sRootsList_nodup : sRootsList.Nodup := by decide +kernel

theorem sRootsList_data : ∀ β ∈ sRootsList, β ∈ rootFinset .E8 ∧ β 7 = 1 ∧ β ∈ e8ListB := by
  rw [rootFinset_E8_eq]
  decide +kernel

theorem sRootsList_cover : ∀ β ∈ rootFinset .E8, β 7 = 1 → β 4 % 5 = 0 → β ∈ sRootsList := by
  rw [rootFinset_E8_eq]
  decide +kernel

theorem theta_mem_S1set : theta ∈ S1set := by
  show theta ∈ e8ListB
  decide +kernel

theorem neg_theta_mem_S1set : -theta ∈ S1set := by
  show -theta ∈ e8ListB
  decide +kernel


variable (K : Type) [Field K]

@[expose] def MElement (q : ModGL Tag.E8 K) : Prop := ∃ β ∈ mRoots, heisCoord Tag.E8 K q β ≠ 0

@[expose] def MPart (H : Subgroup (ModGL Tag.E8 K)) : Prop :=
  ∃ q ∈ H, q ∈ Qθ Tag.E8 K ∧ MElement K q

theorem mem_Deg1_E8 {β : Fin Tag.E8.rank → ℤ} : β ∈ Deg1 Tag.E8 ↔ IsRoot Tag.E8 β ∧ β 7 = 1 :=
  Iff.rfl

theorem Uθ_le_X1 : Uθ Tag.E8 K ≤ X1 K :=
  rootSubgroup_le_rootSpan_of_mem theta_mem_S1set

theorem Uneg_le_X1 : Heis.Uneg Tag.E8 K ≤ X1 K :=
  rootSubgroup_le_rootSpan_of_mem neg_theta_mem_S1set

theorem Deg1_cases {β : Fin Tag.E8.rank → ℤ} (h : β ∈ Deg1 Tag.E8) :
    β ∈ mRoots ∨ β ∈ sRoots1 :=
  deg_one_roots β (mem_rootFinset.2 h.1) h.2

theorem mem_X1_of_coord_M_zero {q : ModGL Tag.E8 K} (hq : q ∈ Qθ Tag.E8 K)
    (h : ∀ β ∈ mRoots, heisCoord Tag.E8 K q β = 0) : q ∈ X1 K := by
  classical
  have hs := heisCoord_spec Tag.E8 K
  have hD : ∀ β ∈ sRootsList, β ∈ Deg1 Tag.E8 := fun β hβ => by
    obtain ⟨h1, h2, -⟩ := sRootsList_data β hβ
    exact ⟨mem_rootFinset.1 h1, h2⟩
  have hsupp : ∀ ν, ν ∉ sRootsList → heisCoord Tag.E8 K q ν = 0 := by
    intro ν hν
    by_cases hD1 : ν ∈ Deg1 Tag.E8
    · rcases Deg1_cases hD1 with hm | hsr
      · exact h ν hm
      · exact absurd (sRootsList_cover ν (Finset.mem_filter.1 hsr).1 hD1.2
          (Finset.mem_filter.1 hsr).2.2) hν
    · exact hs.support q hq ν hD1
  obtain ⟨u, hu, e⟩ := exists_prodX_of_support sRootsList_nodup hD hq hsupp
  rw [e]
  refine mul_mem (Uθ_le_X1 K hu) ?_
  exact CoordAux.prodX_mem_rootSpan (fun α hα => (sRootsList_data α hα).2.2) _

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
