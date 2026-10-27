module

public import CFSG.ClassicalInvolution.Asc77.AscT7PE
public import CFSG.ClassicalInvolution.Asc77.AscT7W13

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace T7P

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]

theorem c21_14_Y_conn_W_of_spinSectionConn_proved (hSpin : SpinSectionConn p f) :
    C21_14_Y_conn_W p f :=
  c21_14_Y_conn_W_of_spinSectionConn
    (twinFrameHyp51t_proved (twinSmallInner_rows_proved p))
    (twinFrameHyp51u_proved (twinSmallOuter_rows_proved p)) hSpin

end T7P

end CFSG.ClassicalInvolution.Asc77
