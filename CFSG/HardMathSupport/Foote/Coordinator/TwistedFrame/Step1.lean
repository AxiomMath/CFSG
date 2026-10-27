module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Hyp
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.GroupTheory

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K]

theorem conjSub_gen (X₁ : Subgroup (ModGL τ K)) (hgen : (⨆ x ∈ X₁, conjSub x (Uθ τ K)) = X₁)
    (h : ModGL τ K) : conjSub h X₁ = ⨆ x ∈ X₁, conjSub (h * x) (Uθ τ K) := by
  conv_lhs => rw [← hgen]
  unfold conjSub
  rw [Subgroup.map_iSup]
  refine iSup_congr fun x => ?_
  rw [Subgroup.map_iSup]
  refine iSup_congr fun hx => ?_
  exact (conjSub_mul h x (Uθ τ K)).symm

theorem exists_conj_not_le {X₁ X₂ H : Subgroup (ModGL τ K)} (hb : TwBasic X₁ X₂)
    (hq : TwQuasi X₁ X₂) (hc : TwCentral X₁ X₂) (hHG : H ≤ adjointGroup τ K)
    (hXH : X₁ ⊔ X₂ ≤ H)
    (hN : ¬ H ≤ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup (ModGL τ K)) : Set (ModGL τ K))) :
    ∃ g ∈ H, ¬ conjSub g (Uθ τ K) ≤ X₁ ⊔ X₂ := by
  by_contra hcon
  push Not at hcon
  apply hN
  obtain ⟨T, hTcomm, hTN, hTcent⟩ := hc.centralizer_le
  have hX₁H : X₁ ≤ H := le_sup_left.trans hXH
  have hX₂H : X₂ ≤ H := le_sup_right.trans hXH
  refine Detect.normalizes_of_forall_conj_le H (adjointGroup τ K) X₁ X₂ T hHG hX₁H hX₂H hb.comm
    (Detect.perfect_subgroup_commutator X₁ hq.1.1) hq.2 hTcomm hTN hTcent ?_
  intro h hh
  rw [conjSub_gen X₁ hb.gen h]
  refine iSup_le fun x => iSup_le fun hx => ?_
  exact hcon (h * x) (H.mul_mem hh (hX₁H hx))

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
