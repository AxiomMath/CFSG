module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.McCov.T2vData
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Data.CoverCenterThreeMcL
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates CFSG.SectionRank.Native CFSG.KC.MiscCoset

public section

namespace CFSG.KBRoute.McCov

@[expose] def rels2 : List (List (Nat × Bool)) := mclPresWords.map encW

#kb_table CFSG.KBRoute.McCov T2 McCov_T2v include_bytes "data/McCov_T2v.meta" 17392 12814432063599842300 1976943448883713 CFSG.KBRoute.McCov.rels2 "1"

theorem top2 : KB.topOk T2.amap (nat_lit 7) = true := by quickRfl

end CFSG.KBRoute.McCov

end
