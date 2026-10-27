module

public import CFSG.Certificates.Kernel.Fi22LH.Defs

public section

namespace CFSG.KS.Fi22LH.LHChecks

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.KS.Fi22L

variable {D : LHData} (h : LHChecks D)
include h

theorem al : D.al = orbT 0 := h.1
theorem be : D.be = orbT 1 := h.2.1
theorem op : D.op = orbT 2 := h.2.2.1
theorem ol : D.ol = orbT 3 := h.2.2.2.1
theorem lb0 : ∀ j < 351, ent D.lb0 j = ((lhData ())[0]!)[j]! := h.2.2.2.2.1
theorem lb1 : ∀ j < 351, ent D.lb1 j = ((lhData ())[1]!)[j]! := h.2.2.2.2.2.1
theorem pd : ∀ i < 693, fld(D.pd, 10 * i, 1023) = phiData[i]! := h.2.2.2.2.2.2.1
theorem tall : ∀ s < 26, tallSl D.R D.al D.be D.bi D.op D.ol s = true := h.2.2.2.2.2.2.2.1
theorem fix : ∀ s < 6, fixSl D.R D.Z s = true := h.2.2.2.2.2.2.2.2.1
theorem bi : biK D.be D.bi = true := h.2.2.2.2.2.2.2.2.2.1
theorem setA : ∀ s < 20, setSl D.QA D.al D.be s = true := h.2.2.2.2.2.2.2.2.2.2.1
theorem setB : ∀ s < 20, setSl D.QB D.al D.be s = true := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem bfsA : orbBfsK D.QA = true := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem bfsB : orbBfsK D.QB = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem walkA : walkOK D.QA D.lb0 (fd D.mt 14 16383) = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem walkB : walkOK D.QB D.lb1 (fd D.mt 28 16383) = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem notIn : notInK D.QA D.lb1 = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem flat : flatK D.QA D.qa D.qb D.qbi = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem phi : ∀ l < 7, phiK D.op D.ol D.qa D.qb D.qbi D.ph l = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem rootX : rootW D.R D.X D.lb0 D.rq0 = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem rootY : rootW D.R D.Y D.lb1 D.rq1 = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem commX : commK D.R D.X D.lb0 D.cq0 = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem commY : commK D.R D.Y D.lb1 D.cq1 = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem dom : ∀ s < 4, domSlW D.R D.lb1 s = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem row : ∀ s < 8, rowSlW D.R D.P D.QA D.lb0 s = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem rowInv : rowInvK D.P D.QA (bs D.lb0) = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem up : upK D.up = true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem star : starW D.al D.eb D.lb0 D.lb1 D.h0 D.h1 D.h2 D.up D.pd = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem fail : failK D.R D.al D.eb D.h1 = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem swap : swapK D.R D.C D.QA D.QB D.u D.lb0 D.lb1 (fd D.mt 42 16383) (fd D.mt 56 16383) =
    true := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem far : farW D.QA D.TF D.ph D.lb0 (fd D.mt 0 16383) (fd D.mt 80 16383) = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem mu : ∀ s < 4, muSlW D.R D.Z D.P D.QA D.lb0 (fd D.mt 0 16383) s = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem muTree : muTreeW D.R D.Z D.P D.QA D.M D.G D.mq (fd D.mt 70 1023) = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ml : mlK D.mq D.ml (fd D.mt 70 1023) = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ed : ∀ s < 8, edSlW D.R D.Z D.P D.QA D.G D.mq D.ml (fd D.mt 0 16383) s = true :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.KS.Fi22LH.LHChecks
