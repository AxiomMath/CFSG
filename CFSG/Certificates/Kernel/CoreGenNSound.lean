module

public import Certificates.Data.Kernel.CoreGenN
public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

namespace CFSG.KC.OpsMN

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsHom CFSG.AGLEmbedding.R3

variable {M V₀ V : Type} [Inhabited M] {O₀ : Ops M V₀} {O : Ops Nat V}

theorem coreGenCheck_of_N (H : Hom O₀ O) {sA sB : String} {A B : Nat}
    (eA : O₀.decode sA = H.U A) (eB : O₀.decode sB = H.U B) (hA : H.P A) (hB : H.P B)
    {nregs : Nat} {prog : List Op} {D : RSpec} (hrA : D.rA < nregs) (hrB : D.rB < nregs)
    (hK : coreGenN O A B nregs prog D = true) (hD : D.wf = true) :
    coreGenCheck O₀ sA sB nregs prog D = true := by
  obtain ⟨hm, h0, h1⟩ := seeds_of_N H eA eB hA hB (fs := D.facts) hrA hrB hK
  have hm' : (decide (2 ≤ nregs) && prog.all (Op.lt nregs) &&
      D.facts.all (factOK O₀ (O₀.regsOf sA sB nregs prog) nregs)) = true := hm
  unfold coreGenCheck
  simp only [hm', h0, h1, hD, decide_eq_true hrA, decide_eq_true hrB, Bool.and_self]

end CFSG.KC.OpsMN

end
