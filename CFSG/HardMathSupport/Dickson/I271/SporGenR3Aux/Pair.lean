module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Shape
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.Yardstones.Md0ec50421ce4

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem isLocallyOneBalancedAbs_of_pair {name : TauCeti.SporadicName} {p : ℕ}
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : SporadicOnePairHolds name p) (S : Type) [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group)) :
    IsLocallyOneBalancedAbs p S := by
  haveI := hS
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hOutS : Nat.card (Outer S) ≤ 2 := hOut S hS hnab name he
  obtain ⟨h1, h2⟩ := hP
  have he' : Nonempty (S ≃* NativeSporadic.Carrier name) := ⟨he.some.trans (hBr name).some.symm⟩
  exact isLocallyOneBalancedAbs_of_parts hp hp2 hcen hOutS (h1 S he') (h2 S he')

@[expose] def LeafShape (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  CentShape p (LeafType p) (NativeSporadic.Carrier name)

end CFSG.HardMathSupport.Dickson.I271
