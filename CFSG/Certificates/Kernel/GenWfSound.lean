module

public import Certificates.Data.Kernel.GenWf

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3

theorem genCheck_eq {M V : Type} [Inhabited M] (O : Ops M V) (p : Nat) (sA sB : String)
    (D : GenData) :
    genCheck O p sA sB D = (mcertCheck O sA sB ⟨D.nregs, D.prog, D.facts⟩ &&
      O.eq (O.regsOf sA sB D.nregs D.prog)[0]! (O.decode sA) &&
      O.eq (O.regsOf sA sB D.nregs D.prog)[1]! (O.decode sB) && genWf p D) := by
  simp only [genCheck, genWf, GenData.mcert, Bool.and_assoc]

theorem genCheck_of {M V : Type} [Inhabited M] {O : Ops M V} {p : Nat} {sA sB : String}
    {D : GenData} (hm : mcertCheck O sA sB ⟨D.nregs, D.prog, D.facts⟩ = true)
    (h0 : O.eq (O.regsOf sA sB D.nregs D.prog)[0]! (O.decode sA) = true)
    (h1 : O.eq (O.regsOf sA sB D.nregs D.prog)[1]! (O.decode sB) = true)
    (hw : genWf p D = true) : genCheck O p sA sB D = true := by
  rw [genCheck_eq, hm, h0, h1, hw]
  rfl

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e
