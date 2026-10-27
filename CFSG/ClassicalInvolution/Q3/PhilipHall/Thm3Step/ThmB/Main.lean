module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.Reduce
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.StdRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB


theorem thm3RThmB_proved (m : ℕ) : Thm3RThmB m :=
  thm3RThmB_of_rows fun _ _ _ Φ K hc _ z hz hzO hall =>
    thm3RowsG_of_std hc.odd Φ hc.hyp K hc.mem hc.notEmpty z hz hzO hall hc.gen

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
