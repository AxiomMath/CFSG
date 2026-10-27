module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl1CertN
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2OneMain
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Zero
public import CFSG.LocalAnalysis.OddStandard.ChengHeldONCert
public import CFSG.LocalAnalysis.OddStandard.ChengHeldUnitMain
public import CFSG.LocalAnalysis.OddStandard.L34EvenSylow

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools
open CFSG.OddStandard.ChengHeldData

theorem l34EvenSylowStep_holds :
    CFSG.OddStandard.L34EvenSylowStep := by
  intro G _ _ A hS h34 hev R hcyc
  have h : Hyp G A := Hyp.of_one_cyclic hS h34 hev R hcyc
  obtain ⟨d⟩ := h.exists_datum
  obtain ⟨hcard, -⟩ := d.center_two_part h
  rcases hcard with h2 | h4
  · exact (sec1_false_hyp h h2).elim
  · obtain ⟨α, hα, c, g, -, hg, hgact⟩ := d.exists_chart4_g_cert h h4
    have hP : chPresOK = true := Certificates.certificate6137
    have hQ : chPropsOK = true := Certificates.certificate6138
    rcases c.shape h with hk | hk | hk | hk | hk
    · exact (Chart4.excl_QS hα c h h4 hg hgact hk).elim
    · exact (Chart4.excl_field_cert hα c h h4 hk).elim
    · exact (Chart4.excl_graph hα c h h4 hg hgact hk).elim
    · obtain ⟨hα0, z, hz, hz2, hza, hX, hcardX⟩ :=
        c.unitary_structure_cert hα h h4 hg hgact hk
      obtain ⟨S, hSX⟩ := exists_sylow_of_isSylowOf_top (c.X_sylow_G_of_facts hα h hP hQ)
      subst hα0
      obtain ⟨T, ⟨e⟩⟩ := exists_mulEquiv_onSylow_cert c.frame hz2 hza hX hcardX
      exact ⟨S, T, ⟨(MulEquiv.subgroupCongr hSX).trans e⟩⟩
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hα with hα0 | hα1
      · subst hα0
        exact (Chart4.excl_both_zero_hyp h h4 c hg hgact hk).elim
      · subst hα1
        exact (Chart4.excl_both_one_hyp h h4 c hg hgact hk).elim

end CFSG.OddStandard.ChengHeld
