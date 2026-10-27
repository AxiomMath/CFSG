module

public import Certificates.Certificate125

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2
open CFSG.ClassicalInvolution.Generic


theorem gen_comm_x0 : gen 8 * mainPerm 0 = mainPerm 0 * gen 8 ∧
    gen 9 * mainPerm 0 = mainPerm 0 * gen 9 :=
  ⟨Certificates.certificate125.2.2.1.1, Certificates.certificate125.2.2.1.2.1⟩

theorem ws_comm_x0 : ∀ k ∈ [1, 3, 4], wsP.getD k 1 * mainPerm 0 = mainPerm 0 * wsP.getD k 1 :=
  Certificates.certificate125.2.2.1.2.2.1

theorem three_facts : three ^ 3 = 1 ∧ conjSub three K0 = K0 ∧ three * u0 ≠ u0 * three :=
  Certificates.certificate125.2.2.1.2.2.2

end CFSG.ClassicalInvolution.Q3.TL4.E4O8
