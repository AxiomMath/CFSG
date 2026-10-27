module

public import Certificates.Data.CFSGNative.SectionRank.F2
public import Certificates.Data.CFSGNative.SectionRank.F2Fast
public import CFSG.RankThree.Asc83Table.MatCertDefs
import all CFSG.Certificates.Kernel.OpsF2KMcertSound

public section

namespace CFSG.KC.OpsF2K

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

theorem mcertCheck_fr_eq (d : Nat) (sA sB : String) (C : MCert) :
    mcertCheck (ops2fr d) sA sB C = mcertCheck (ops2 d) sA sB C := by
  obtain ⟨hregs, hR⟩ := regsOf_fr (d := d) sA sB C.nregs C.prog
  have hf : factOK (ops2fr d) ((ops2fr d).regsOf sA sB C.nregs C.prog) C.nregs =
      factOK (ops2 d) ((ops2 d).regsOf sA sB C.nregs C.prog) C.nregs := by
    rw [hregs]
    exact funext (factOK_fr hR C.nregs)
  change (decide (2 ≤ C.nregs) && C.prog.all (Op.lt C.nregs) &&
      C.facts.all (factOK (ops2fr d) ((ops2fr d).regsOf sA sB C.nregs C.prog) C.nregs)) =
    (decide (2 ≤ C.nregs) && C.prog.all (Op.lt C.nregs) &&
      C.facts.all (factOK (ops2 d) ((ops2 d).regsOf sA sB C.nregs C.prog) C.nregs))
  rw [hf]

end CFSG.KC.OpsF2K

end
