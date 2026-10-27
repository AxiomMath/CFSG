module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfoldNames
import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M
import CFSG.Certificates.Kernel.Fi22.Bound2.Data.C_Sel
import CFSG.Certificates.Kernel.Fi22.Bound2.Std3
import CFSG.Certificates.Kernel.Fi22.Bound.Data.Cov

#kc_repo #kc_items_root CFSG.KD.Fi22KM.MRows.P0 "CFSG/Certificates/Kernel/Fi22/Bound2/Data/M/rows/M_0_P.bin" 134 18264438263561613501
#kc_repo #kc_items_root CFSG.KD.Fi22KM.MRows.P1 "CFSG/Certificates/Kernel/Fi22/Bound2/Data/M/rows/M_1_P.bin" 360 4860361684404279625
#kc_repo #kc_items_root CFSG.KD.Fi22KM.MRows.P2 "CFSG/Certificates/Kernel/Fi22/Bound2/Data/M/rows/M_2_P.bin" 118 10513242201560492209
#kc_repo #kc_items_root CFSG.KD.Fi22KM.MRows.P3 "CFSG/Certificates/Kernel/Fi22/Bound2/Data/M/rows/M_3_P.bin" 119 17004104213238762419
#kc_repo #kc_items_root CFSG.KD.Fi22KM.MRows.P4 "CFSG/Certificates/Kernel/Fi22/Bound2/Data/M/rows/M_4_P.bin" 137 12052250327483522665
#kc_repo #kc_items_root CFSG.KD.Fi22KM.MRows.P6 "CFSG/Certificates/Kernel/Fi22/Bound2/Data/M/rows/M_6_P.bin" 158 16438182180766723978
#kc_repo #kc_items_root CFSG.KD.Fi22KM.MRows.P7 "CFSG/Certificates/Kernel/Fi22/Bound2/Data/M/rows/M_7_P.bin" 75930 9602822159561911124
#kc_select CFSG.KD.Fi22KC MRows.CVs CV 16

namespace CFSG.KD.Fi22KM.MRows

open CFSG.KD.Fi22KM CFSG.KC

noncomputable def hom (g : Nat) : Bool :=
  Nat.beq (Fi22K.evalE FIs (XRs (P0 g))) Fi22B.Cov.one4

noncomputable def letW (g : Nat) : Bool :=
  andB (Nat.beq (Fi22K.lX (CFSG.KD.Fi22KC.LETs (P1 (8 * g + 0))))
      (Fi22K.evalE FIs (WJs (P1 (8 * g + 1)))))
    (andB (Nat.beq (Fi22B.Cov.mul4 (Fi22K.lX (CFSG.KD.Fi22KC.LETs (P1 (8 * g + 2))))
        (Fi22K.lXI (CFSG.KD.Fi22KC.LETs (P1 (8 * g + 3))))) Fi22B.Cov.one4)
      (andB (Nat.beq (Fi22K.lP (CFSG.KD.Fi22KC.LETs (P1 (8 * g + 4)))) (P1 (8 * g + 5)))
        (Nat.beq (Fi22K.lN (CFSG.KD.Fi22KC.LETs (P1 (8 * g + 6)))) (P1 (8 * g + 7)))))

noncomputable def letE (g : Nat) : Bool :=
  Nat.beq (CFSG.KD.Fi22KC.LETs (P2 (4 * g + 0)))
    (Fi22K.labOf (FIs (P2 (4 * g + 1))) (FIs (P2 (4 * g + 2))) (P2 (4 * g + 3)) Fi22K.OFF)

noncomputable def eh (g : Nat) : Bool :=
  Nat.beq (EHs (P3 (4 * g + 0)))
    (Fi22B2.Std3.evalW CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B
      (Fi22B.Cov.pw4 CFSG.KD.Fi22BC3.B (P3 (4 * g + 1)))
      (LceS.wWord (Fi22K.subY (P3 (4 * g + 2)))) (LceS.wLen (Fi22K.subY (P3 (4 * g + 3)))))

noncomputable def cj (g : Nat) : Bool :=
  Fi22K.scalEq
    (Fi22B2.Std3.evalW CFSG.KD.Fi22BC3.A CFSG.KD.Fi22BC3.B
      (Fi22B.Cov.pw4 CFSG.KD.Fi22BC3.B (P4 (4 * g + 0)))
      (LceS.wWord (Fi22B.sub (P4 (4 * g + 1)))) (LceS.wLen (Fi22B.sub (P4 (4 * g + 2)))))
    (Fi22K.evalE EHs (WJs (P4 (4 * g + 3))))

noncomputable def anon (_ : Nat) : Bool :=
  notB (Fi22K.scalEq CFSG.KD.Fi22BC3.A Fi22B.Cov.one4)

noncomputable def row (g : Nat) : Bool :=
  Fi22K.rowOK CFSG.KD.Fi22BC3.A (CFSG.KD.Fi22KC.MRows.CVs (P6 (2 * g + 0))) (ROWs (P6 (2 * g + 1)))

noncomputable def cmb (g : Nat) : Bool :=
  Fi22K.coordOK
    [Nat.lor (ROWs (P7 (37 * g + 0))) (P7 (37 * g + 1)),
     Nat.lor (ROWs (P7 (37 * g + 2))) (P7 (37 * g + 3)),
     Nat.lor (ROWs (P7 (37 * g + 4))) (P7 (37 * g + 5)),
     Nat.lor (ROWs (P7 (37 * g + 6))) (P7 (37 * g + 7)),
     Nat.lor (ROWs (P7 (37 * g + 8))) (P7 (37 * g + 9)),
     Nat.lor (ROWs (P7 (37 * g + 10))) (P7 (37 * g + 11)),
     Nat.lor (ROWs (P7 (37 * g + 12))) (P7 (37 * g + 13)),
     Nat.lor (ROWs (P7 (37 * g + 14))) (P7 (37 * g + 15)),
     Nat.lor (ROWs (P7 (37 * g + 16))) (P7 (37 * g + 17)),
     Nat.lor (ROWs (P7 (37 * g + 18))) (P7 (37 * g + 19)),
     Nat.lor (ROWs (P7 (37 * g + 20))) (P7 (37 * g + 21)),
     Nat.lor (ROWs (P7 (37 * g + 22))) (P7 (37 * g + 23)),
     Nat.lor (ROWs (P7 (37 * g + 24))) (P7 (37 * g + 25)),
     Nat.lor (ROWs (P7 (37 * g + 26))) (P7 (37 * g + 27)),
     Nat.lor (ROWs (P7 (37 * g + 28))) (P7 (37 * g + 29)),
     Nat.lor (ROWs (P7 (37 * g + 30))) (P7 (37 * g + 31))]
    (P7 (37 * g + 32)) (P7 (37 * g + 33)) (P7 (37 * g + 34)) (P7 (37 * g + 35)) (P7 (37 * g + 36))

end CFSG.KD.Fi22KM.MRows

set_option maxRecDepth 100000

#kc_each_unfold CFSG.KD.Fi22KM.MRows.hom 0 27 as CFSG.KD.Fi22KM.hom eval CFSG.KD.Fi22KM.MRows.P0
#kc_each_unfold CFSG.KD.Fi22KM.MRows.letW 0 7 as CFSG.KD.Fi22KM.let eval CFSG.KD.Fi22KM.MRows.P1
#kc_each_unfold CFSG.KD.Fi22KM.MRows.letE 7 13 as CFSG.KD.Fi22KM.let at 0
  eval CFSG.KD.Fi22KM.MRows.P2
#kc_each_unfold CFSG.KD.Fi22KM.MRows.eh 0 6 as CFSG.KD.Fi22KM.eh eval CFSG.KD.Fi22KM.MRows.P3
#kc_each_unfold CFSG.KD.Fi22KM.MRows.cj 0 7 as CFSG.KD.Fi22KM.cj eval CFSG.KD.Fi22KM.MRows.P4

#kc_unfold CFSG.KD.Fi22KM.anonscalar CFSG.KD.Fi22KM.MRows.anon 0

#kc_each_unfold_names CFSG.KD.Fi22KM.MRows.row 0 16 as CFSG.KD.Fi22KM.row
  eval CFSG.KD.Fi22KM.MRows.P6 names (CFSG.KD.Fi22KC.MRows.CVs CFSG.KD.Fi22KC.CV)

#kc_each_unfold CFSG.KD.Fi22KM.MRows.cmb 0 10 as CFSG.KD.Fi22KM.cmb0_ at 0 eval CFSG.KD.Fi22KM.MRows.P7
#kc_each_unfold CFSG.KD.Fi22KM.MRows.cmb 0 10 as CFSG.KD.Fi22KM.cmb1_ at 10 eval CFSG.KD.Fi22KM.MRows.P7
#kc_each_unfold CFSG.KD.Fi22KM.MRows.cmb 0 10 as CFSG.KD.Fi22KM.cmb2_ at 20 eval CFSG.KD.Fi22KM.MRows.P7
#kc_each_unfold CFSG.KD.Fi22KM.MRows.cmb 0 10 as CFSG.KD.Fi22KM.cmb3_ at 30 eval CFSG.KD.Fi22KM.MRows.P7
#kc_each_unfold CFSG.KD.Fi22KM.MRows.cmb 0 10 as CFSG.KD.Fi22KM.cmb4_ at 40 eval CFSG.KD.Fi22KM.MRows.P7
#kc_each_unfold CFSG.KD.Fi22KM.MRows.cmb 0 10 as CFSG.KD.Fi22KM.cmb5_ at 50 eval CFSG.KD.Fi22KM.MRows.P7
#kc_each_unfold CFSG.KD.Fi22KM.MRows.cmb 0 10 as CFSG.KD.Fi22KM.cmb6_ at 60 eval CFSG.KD.Fi22KM.MRows.P7
#kc_each_unfold CFSG.KD.Fi22KM.MRows.cmb 0 10 as CFSG.KD.Fi22KM.cmb7_ at 70 eval CFSG.KD.Fi22KM.MRows.P7
#kc_each_unfold CFSG.KD.Fi22KM.MRows.cmb 0 10 as CFSG.KD.Fi22KM.cmb8_ at 80 eval CFSG.KD.Fi22KM.MRows.P7
#kc_each_unfold CFSG.KD.Fi22KM.MRows.cmb 0 10 as CFSG.KD.Fi22KM.cmb9_ at 90 eval CFSG.KD.Fi22KM.MRows.P7
