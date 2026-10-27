module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Defs

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.Yardstones.Md42047359a2a (LieFamily lieFamily)

@[expose] def IsExcUntwisted : TauCeti.LieTypeIndex → Prop
  | .G2 _ | .F4 _ | .E6 _ | .E7 _ | .E8 _ => True
  | _ => False

@[expose] def IsExcTwistedE6 : TauCeti.LieTypeIndex → Prop
  | .twistedE6 _ => True
  | _ => False

@[expose] def IsExcTrialityD4 : TauCeti.LieTypeIndex → Prop
  | .trialityD4 _ => True
  | _ => False

@[expose] def IsExcTwisted (d : TauCeti.LieTypeIndex) : Prop :=
  IsExcTwistedE6 d ∨ IsExcTrialityD4 d

@[expose] def OuterCentExcTags (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, P idx.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
        ∀ p : ℕ, p.Prime → p ≠ 2 → p = idx.1.characteristic →
          ∀ β : MulAut S, orderOf β = p → β ∉ innerAut S → OuterCentData p β

theorem isExcUntwisted_or_isExcTwisted {d : TauCeti.LieTypeIndex}
    (h : lieFamily d = LieFamily.exceptional) : IsExcUntwisted d ∨ IsExcTwisted d := by
  cases d <;> simp_all [lieFamily, IsExcUntwisted, IsExcTwisted, IsExcTwistedE6, IsExcTrialityD4]

theorem outerCentOn_exceptional_of_tags (h1 : OuterCentExcTags IsExcUntwisted)
    (h2 : OuterCentExcTags IsExcTwistedE6) (h3 : OuterCentExcTags IsExcTrialityD4) :
    OuterCentOn LieFamily.exceptional := by
  intro S _ _ hs hnc idx hfam he p hp hp2 hpc β hβ hout
  rcases isExcUntwisted_or_isExcTwisted hfam with h | h | h
  · exact h1 S hs hnc idx h he p hp hp2 hpc β hβ hout
  · exact h2 S hs hnc idx h he p hp hp2 hpc β hβ hout
  · exact h3 S hs hnc idx h he p hp hp2 hpc β hβ hout

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
