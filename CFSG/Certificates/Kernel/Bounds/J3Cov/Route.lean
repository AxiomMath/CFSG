module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.J3Cov.T1vData
public import CFSG.Certificates.Kernel.Bounds.J3Cov.T2vData
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Data.CoverCenterThreeJ3
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates CFSG.SectionRank.Native CFSG.KC.MiscCoset

public section

namespace CFSG.KBRoute.J3Cov

@[expose] def nWords : List (List (Fin 6 × Bool)) := j3CoverRels ++ [List.replicate 8 (0, true)]

@[expose] def rels1 : List (List (Nat × Bool)) := j3GammaWords.map encW

@[expose] def rels2 : List (List (Nat × Bool)) := nWords.map encW

#kb_table CFSG.KBRoute.J3Cov T1 J3Cov_T1v include_bytes "data/J3Cov_T1v.meta" 1555 2933350278563230335 6618611909121 CFSG.KBRoute.J3Cov.rels1 "1"

#kb_table CFSG.KBRoute.J3Cov T2 J3Cov_T2v include_bytes "data/J3Cov_T2v.meta" 395 12510794691574565412 6618611909121 CFSG.KBRoute.J3Cov.rels2 "1"

theorem top1 : KB.topOk T1.amap (nat_lit 6) = true := by quickRfl

theorem top2 : KB.topOk T2.amap (nat_lit 6) = true := by quickRfl

end CFSG.KBRoute.J3Cov

end
