module

public import CFSG.LocalAnalysis.OddStandard.Harada75Reduce
public import CFSG.LocalAnalysis.OddStandard.Harada75Main

public section

namespace CFSG.OddStandard.Harada75

open CFSG Subgroup

theorem twoGroupStatement : TwoGroupStatement := by
  intro S _ _ hS A hA hA8 hCA P
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg (fun x : A => (x : S)) (hA.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian a ha
  have hcent : ∀ x : S, (∀ a ∈ A, x * a = a * x) → x ∈ A := fun x hx => by
    rw [← hCA]
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => (hx a ha).symm
  by_cases hex : ∃ E : Subgroup S, E.Normal ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8
  · obtain ⟨E, hEn, hEab, hE8⟩ := hex
    have hcfg : Cfg S A E :=
      { A_comm := hcomm
        A_sq := hsq
        A_card := hA8
        A_cent := hcent
        E_comm := fun a ha b hb =>
          congrArg (fun x : E => (x : S)) (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
        E_sq := fun a ha => by
          rw [← pow_two]
          exact hEab.2 a ha
        E_card := hE8
        E_norm := fun s e he => hEn.conj_mem e he s }
    exact gen4_of_noE32 hS (noE32_of_cfg hS hcfg) P
  · push Not at hex
    exact CFSG.Milestones.cls_connectivity_macwilliams_four_generator S hS
      (fun E hEn hEab => hex E hEn hEab) P

theorem haradaInput_holds : ComponentClassification.HSFLit.HaradaInput :=
  haradaInput_of_twoGroup twoGroupStatement

end CFSG.OddStandard.Harada75
