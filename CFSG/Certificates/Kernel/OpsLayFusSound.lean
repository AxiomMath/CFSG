module

public import Certificates.Data.Kernel.OpsLayFus
public import Certificates.Data.CFSGNative.SectionRank.F3
public import Certificates.Data.CFSGNative.SectionRank.Fp
import CFSG.Certificates.Kernel.OpsLayMcertSoundP

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.RankThree.PartOne.CTP.Fus (Spec fusCheck)

theorem fusCheck_of_seeds {M V : Type} [Inhabited M] {O : Ops M V} {sA sB : String}
    {nregs : Nat} {prog : List Op} {D : Spec}
    (h : mcertCheck O sA sB ⟨nregs, prog, D.facts⟩ = true ∧ D.rA < nregs ∧ D.rB < nregs ∧
      O.eq (O.regsOf sA sB nregs prog)[D.rA]! (O.decode sA) = true ∧
      O.eq (O.regsOf sA sB nregs prog)[D.rB]! (O.decode sB) = true)
    (hw : D.wf = true) : fusCheck O sA sB nregs prog D = true := by
  obtain ⟨hm, hrA, hrB, h0, h1⟩ := h
  unfold fusCheck
  rw [hm, decide_eq_true hrA, decide_eq_true hrB, h0, h1, hw]
  rfl

theorem fusL_sound {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {nregs : Nat} {prog : List Op}
    {D : Spec} (h : fusL c A B nregs prog D = true) :
    fusCheck (ops3 d) sA sB nregs prog D = true := by
  unfold fusL at h
  rw [Bool.and_eq_true] at h
  exact fusCheck_of_seeds (seedsL_sound hc hp hd hA hB hsA hsB h.1) h.2

theorem fusLP_sound {c : Lay} {p d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = p) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {nregs : Nat} {prog : List Op}
    {D : Spec} (h : fusL c A B nregs prog D = true) :
    fusCheck (opsP p d) sA sB nregs prog D = true := by
  unfold fusL at h
  rw [Bool.and_eq_true] at h
  exact fusCheck_of_seeds (seedsLP_sound hc hp hd hA hB hsA hsB h.1) h.2

end CFSG.KC.OpsLayK

end
