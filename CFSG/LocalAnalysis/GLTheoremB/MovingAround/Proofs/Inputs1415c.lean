module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1415b
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeAFinal

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415c

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415

structure OpenAtRest : Prop where
  co1_3 : SporNoAltDown 3 12 .Co1 ∧ SporNoAltDown 3 15 .Co1
  co1_5 : SporNoAltDown 5 10 .Co1 ∧ SporNoAltDown 5 15 .Co1
  hn_3 : SporNoAltDown 3 12 .HN
  b_3 : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group →
    SporNoAltDown 3 12 .B ∧ SporNoAltDown 3 15 .B
  b_5 : ∀ m : ℕ, 10 ≤ m → m ≤ 20 → CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group →
    SporNoAltDown 5 m .B
  m_3 : ∀ m : ℕ, 10 ≤ m → m ≤ 32 → CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group →
    SporNoAltDown 3 m .M
  m_5 : ∀ m : ℕ, 10 ≤ m → m ≤ 32 → CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group →
    SporNoAltDown 5 m .M
  m_7 : ∀ m : ℕ, 7 ∣ m → 10 ≤ m → m ≤ 32 → CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group →
    SporNoAltDown 7 m .M
  m_11 : ∀ m : ℕ, 11 ≤ m → m ≤ 21 → CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group →
    SporNoAltDown 11 m .M

section Holds

set_option linter.unusedSectionVars false

theorem openAt_of_rest (h : OpenAtRest) : Inputs1415b.OpenAt :=
  ⟨CFSG.HardMathSupport.Dickson.I271.TabCo1.co1ThreeAShape_holds
      CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group,
    h.co1_3, h.co1_5, h.hn_3, h.b_3, h.b_5, h.m_3, h.m_5, h.m_7, h.m_11⟩

end Holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415c

end
