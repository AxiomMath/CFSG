module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Centralizer
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.GroupTheory

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false


variable (K : Type) [Field K]

theorem torus_comm {a b : ModGL Tag.F4 K} (ha : a ∈ torusGroup Tag.F4 K)
    (hb : b ∈ torusGroup Tag.F4 K) : a * b = b * a :=
  (triangular_borel_structure.{0, 0} Tag.F4 K).1 a ha b hb

theorem torus_le_normalizer_X2 : torusGroup Tag.F4 K ≤ Subgroup.normalizer (X2 K : Set (ModGL Tag.F4 K)) :=
  torusGroup_le_normalizer_rootSpan fun _ hα => isRoot_of_mem_S2set hα

theorem exists_conj_not_le {H : Subgroup (ModGL Tag.F4 K)} (hH : H ≤ adjointGroup Tag.F4 K)
    (hX : XS K ≤ H) (hN : ¬ H ≤ Subgroup.normalizer (XS K : Set (ModGL Tag.F4 K))) :
    ∃ h ∈ H, ∃ α ∈ S1set, ¬ conjSub h (rootSubgroup Tag.F4 K α) ≤ XS K := by
  by_contra hcon
  push Not at hcon
  apply hN
  rw [XS_eq]
  refine Detect.normalizes_of_forall_conj_le H (adjointGroup Tag.F4 K) (X1 K) (X2 K)
    (torusGroup Tag.F4 K) hH ((X1_le_XS K).trans hX) ((X2_le_XS K).trans hX) (X1_X2_commute K)
    (X1_perfect K) (X2_quasisimple K) (fun a ha b hb => torus_comm K ha hb)
    (torus_le_normalizer_X2 K) (fun g hg hc => centralizer_X1_le K hg hc) ?_
  intro h hh
  rw [← XS_eq]
  show conjSub h (⨆ α, ⨆ (_ : α ∈ S1set), rootSubgroup Tag.F4 K α) ≤ _
  unfold conjSub
  rw [Subgroup.map_iSup]
  refine iSup_le fun α => ?_
  rw [Subgroup.map_iSup]
  exact iSup_le fun hα => hcon h hh α hα

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
