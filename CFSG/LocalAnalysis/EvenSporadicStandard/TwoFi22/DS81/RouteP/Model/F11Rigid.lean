module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F11Pin
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutFinal

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.Sporadic.Fi23 (Cd)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem f11 :
    ∀ α : ↥L0 ≃* ↥L0, (∀ b : ↥L0, (b : Q3) ∈ B0 → α b = b) → α = MulEquiv.refl _ := by
  intro α hα
  obtain ⟨ψ, hψ⟩ := exists_equiv_Cd_mem_E0_iff
  exact @eq_refl_of_fixes_of_equiv ↥L0 ↥Cd inferInstance inferInstance ψ (E0.subgroupOf L0)
    (B0.subgroupOf L0) DS81.E0
    (fun x hx => Subgroup.mem_subgroupOf.2 (E0_le_B0 (Subgroup.mem_subgroupOf.1 hx)))
    (fun x => Subgroup.mem_subgroupOf.trans (hψ x)) DS81.Cd_aut_cent
    (fun y hy hc => mem_center_L0_iff.2
      (eq_of_mem_E0_of_commute_B0 (Subgroup.mem_subgroupOf.1 hy) fun b hb =>
        (congrArg Subtype.val (hc ⟨b, B0_le_L0 hb⟩ (Subgroup.mem_subgroupOf.2 hb))).symm))
    α (fun b hb => hα b (Subgroup.mem_subgroupOf.1 hb))

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
