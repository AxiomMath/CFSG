module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.OrthMinusReduction
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.AGLEmbedding TauCeti

section Main


theorem simpleStmt_of_twistedD_index (hL : OrthMinusLeviOb) (hC : OrthMinusCentOb) {Y : Type}
    [Group Y] [Finite Y] (hcl : IsClassicalTwoOrG2 Y) {d : TauCeti.ValidLieTypeIndex} {r : ℕ}
    {q : TauCeti.PrimePower} (hdq : d.1 = .twistedD r q) (hp : q.p = 2)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : SimpleStmt Y := by
  obtain ⟨d, hv⟩ := d
  have hdq' : d = .twistedD r q := hdq
  subst hdq'
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
  rw [hp] at h
  exact simpleStmt_of_orth_minus_model hL hC hcl h

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

end
