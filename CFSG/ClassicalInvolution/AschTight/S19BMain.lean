module

public import CFSG.Goldschmidt75.CorollaryB1
public import CFSG.ClassicalInvolution.AschTight.S19BStmt

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem goldschmidtB1Tmp_holds : GoldschmidtB1Tmp :=
  fun _ _ _ _ hnonab S _ hBS hB hsc =>
    CFSG.Goldschmidt75.goldschmidtB1_simple hnonab S hBS hB hsc

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
