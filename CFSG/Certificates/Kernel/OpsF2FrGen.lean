module

public import Certificates.Data.CFSGNative.SectionRank.F2
public import Certificates.Data.CFSGNative.SectionRank.F2Fast
public import CFSG.Certificates.Kernel.GenWfSound
import all CFSG.Certificates.Kernel.OpsF2KMcertSound
import CFSG.Certificates.Kernel.OpsF2FrMcert

public section

namespace CFSG.KC.OpsF2K

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e

theorem regsOf_fr_eq {d : Nat} (sA sB : String) (n : Nat) (prog : List Op) :
    (ops2fr d).regsOf sA sB n prog = (ops2 d).regsOf sA sB n prog ∧
      ∀ x ∈ (ops2 d).regsOf sA sB n prog, x.size ≤ d :=
  regsOf_fr sA sB n prog

theorem evalW_fr_eq {d : Nat} {R : Array (Array Nat)} (hR : ∀ x ∈ R, x.size ≤ d) (w : Word) :
    evalW (ops2fr d) R w = evalW (ops2 d) R w :=
  (evalW_fr hR w).1

theorem eq_fr (d : Nat) (X Y : Array Nat) : (ops2fr d).eq X Y = (ops2 d).eq X Y := rfl

theorem genCheck_fr_eq (d p : Nat) (sA sB : String) (D : GenData) :
    genCheck (ops2fr d) p sA sB D = genCheck (ops2 d) p sA sB D := by
  rw [genCheck_eq, genCheck_eq, mcertCheck_fr_eq, (regsOf_fr_eq (d := d) sA sB D.nregs D.prog).1]
  rfl

end CFSG.KC.OpsF2K

end
