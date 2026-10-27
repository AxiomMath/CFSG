module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Centralizer
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.GroupTheory

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false


variable (K : Type) [Field K]

theorem torus_comm {a b : ModGL Tag.E8 K} (ha : a ∈ torusGroup Tag.E8 K)
    (hb : b ∈ torusGroup Tag.E8 K) : a * b = b * a :=
  (triangular_borel_structure.{0, 0} Tag.E8 K).1 a ha b hb

theorem torus_le_normalizer_X2 : torusGroup Tag.E8 K ≤ Subgroup.normalizer (X2 K : Set (ModGL Tag.E8 K)) :=
  torusGroup_le_normalizer_rootSpan fun _ hα => isRoot_of_mem_S2set hα

theorem exists_conj_not_le {H : Subgroup (ModGL Tag.E8 K)} (hH : H ≤ adjointGroup Tag.E8 K)
    (hX : XS K ≤ H) (hN : ¬ H ≤ Subgroup.normalizer (XS K : Set (ModGL Tag.E8 K))) :
    ∃ h ∈ H, ∃ α ∈ S1set, ¬ conjSub h (rootSubgroup Tag.E8 K α) ≤ XS K := by
  by_contra hcon
  push Not at hcon
  apply hN
  rw [XS_eq]
  refine Detect.normalizes_of_forall_conj_le H (adjointGroup Tag.E8 K) (X1 K) (X2 K)
    (torusGroup Tag.E8 K) hH ((X1_le_XS K).trans hX) ((X2_le_XS K).trans hX) (X1_X2_commute K)
    (X1_perfect K) (X2_quasisimple K) (fun a ha b hb => torus_comm K ha hb)
    (torus_le_normalizer_X2 K) (fun g hg hc => centralizer_X1_le K hg hc) ?_
  intro h hh
  rw [← XS_eq]
  show conjSub h (⨆ α, ⨆ (_ : α ∈ S1set), rootSubgroup Tag.E8 K α) ≤ _
  unfold conjSub
  rw [Subgroup.map_iSup]
  refine iSup_le fun α => ?_
  rw [Subgroup.map_iSup]
  exact iSup_le fun hα => hcon h hh α hα

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
