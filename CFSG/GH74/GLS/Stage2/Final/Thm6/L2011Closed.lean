module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Final
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdFinal
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CFTypeMain
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Proved
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413HProved
public import CFSG.GH74.GLS.Stage2.Local.GHSchMain
public import CFSG.GH74.GLS.IVK.Proofs2.Sec3c

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT (Data411Clauses cfTypeAut_of_data)

theorem lemma20_11_closed
    (h411 : Data411Clauses) : Lemma20_11 :=
  lemma20_11_of_leaves Ad.adapter20_9
    (cfTypeAut_of_data IVK.Proofs2.ivk93Pair_proved IVK.Proofs2.ivk_4_13_H_proved h411)
    (fun J _ _ _ hn hG => Stage2.Local.GHSch.ghSchreier_thm J hn hG) IVK.ivk_3_1a
    IVK.Proofs2.ivk_3_1c IVK.Proofs2.ivk_3_1g_fixed

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
