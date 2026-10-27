module

public import CFSG.ClassicalInvolution.Q3.Q3T8NAssem
public import CFSG.ClassicalInvolution.Q3.Q3NHMain

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

section Hyp51


theorem hyp51Tri_proved : T8T.Hyp51Tri := by
  intro G _ _ _ Ω M x R hs hnt hF hind
  have hs3 : Q3.Disc3.AscStand3 Ω (M 0) := hs.toStand3
  have hfr := fuzzyFrame3_of_triFrame hs.hyp hs.modU hnt hF hind
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨J, z, hJ, -⟩ := hfr
    obtain ⟨a, -, hac⟩ := IsConcreteLE.not_le_iff_exists.mp (hJ 0).2.not_le_center
    rw [Subgroup.mem_center_iff] at hac
    push Not at hac
    obtain ⟨b, hb⟩ := hac
    exact ⟨b, a, hb⟩
  exact Q3NH.hyp51_of_fuzzyFrame (Q3T7.inClass3_of_stand3 hs3) (Q3T7.cit3Below_of_stand3 hs3)
    hnab hfr

end Hyp51

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
