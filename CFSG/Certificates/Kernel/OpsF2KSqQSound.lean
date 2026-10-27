module

public import Certificates.Data.Kernel.OpsF2KSqQ
public import CFSG.Certificates.Kernel.OpsF2KQSound
import CFSG.Certificates.Kernel.Misc.F2BfsRec2Sound

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native
open CFSG.KC.Misc.G24 (mulF2)
open CFSG.KC.F2BfsRec (mulF2_eq_mulF)

theorem sqQ_eq (d A B : Nat) (D : SqData) : sqQ d A B D = sqK d A B D := by
  cases hs : seedsOK d A B
  · simp only [sqQ, sqK, hs, Bool.false_and]
  cases he : D.prog.all expOK
  · simp only [sqQ, sqK, hs, he, Bool.true_and, Bool.false_and]
  obtain ⟨hR, hbd⟩ := runQ_eq (n := D.nregs) hs he
  cases hb : [D.r, D.oh, D.a, D.b, D.c, D.d].all (decide <| · < 65536)
  · simp only [sqQ, sqK, hb, Bool.and_false, Bool.false_and]
  have hb' : ∀ x ∈ [D.r, D.oh, D.a, D.b, D.c, D.d], x < 2 ^ 16 := fun x hx => by
    have := of_decide_eq_true (List.all_eq_true.1 hb x hx)
    omega
  simp only [sqQ, sqK, hR, commQ_eq, conjQ_eq, mulF2_eq_mulF, pqK_getR hbd (hb' D.r (by simp)),
    pqK_getR hbd (hb' D.oh (by simp)), pqK_getR hbd (hb' D.a (by simp)),
    pqK_getR hbd (hb' D.b (by simp)), pqK_getR hbd (hb' D.c (by simp)),
    pqK_getR hbd (hb' D.d (by simp))]

theorem sqK_of_Q {d A B : Nat} {D : SqData} (h : sqQ d A B D = true) : sqK d A B D = true := by
  rwa [← sqQ_eq]

end CFSG.KC.OpsF2K

end
