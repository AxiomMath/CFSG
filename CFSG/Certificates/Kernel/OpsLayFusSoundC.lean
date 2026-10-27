module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.RankThree.PartOne.CTP.FusionDefs
import CFSG.Certificates.Kernel.OpsLayMcertSound
import CFSG.Certificates.Kernel.OpsLayFusSound

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.RankThree.PartOne.CTP.Fus (Spec fusCheck)

theorem fusLC_sound {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : Nat} {prog : List Op}
    {D : Spec} (hw : D.wf = true) (hprog : progOK n prog = true) (hrA : D.rA < n)
    (hrB : D.rB < n) {S : Nat → List Nat} {k m kf mf : Nat} (h0 : S 0 = initR c A B n)
    (hm : prog.length ≤ m * k) (hch : ∀ i < m, chunkL c prog k i (S i) (S (i + 1)) = true)
    (hmf : D.facts.length ≤ mf * kf) (hf : ∀ i < mf, factsL c (S m) n D.facts kf i = true)
    (he : seedRegsL c (S m) A B D.rA D.rB = true) :
    fusCheck (ops3 d) sA sB n prog D = true :=
  fusCheck_of_seeds (seedsLC_sound (C := ⟨n, prog, D.facts⟩) hc hp hd hA hB hsA hsB hprog hrA hrB
    h0 hm hch hmf hf he) hw

end CFSG.KC.OpsLayK

end
