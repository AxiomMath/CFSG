module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Main
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAStar
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen4
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L284
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Axb
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der615
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der73
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Closed2
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Stmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Basic
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Steps
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt12
public import CFSG.GH74.GLS.Stage2.Signalizer.Kinds
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
public import CFSG.GH74.GLS.Stage2.Signalizer.SDWr
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5
public import CFSG.Goldschmidt.Basic
public import CFSG.Goldschmidt.Steps.Sec8Bender
public import CFSG.Walter.Bender1970.S1
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.Bender1970.S3
public import CFSG.Walter.Bender1970.S38
public import CFSG.Walter.PSL2Facts

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem lemma18_6_thm
    (hMin : MinIndexL34) (hInv : InvSec) (hkb : KB813)
    (h171 : Prop17_1) (hL31 : Lemma31Narrow) (hB12 : Bender12) (h183 : Lemma18_3a)
    (h184 : Lemma18_4ac) (hKA : IVK_8_13_lift) : Lemma18_6 :=
  L6.lemma18_6_of hMin hInv
    (fun _ _ _ hF _ _ hα2 hα1 _ hp hp2 _ hP hP1 hcomm hnorm =>
      kay_star_L34_full hF hα2 hα1 hp hp2 hP hP1 hcomm hnorm)
    (fun _ _ _ hF hs _ _ ht2 ht1 hb => invol_not_comm_order_three hF hs ht2 ht1 hb)
    hkb h171 hL31 hB12 h183 h184 hKA

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
