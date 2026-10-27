module

public import CFSG.Yardstones.Md42047359a2a.Definitions
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Chevalley
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TwistedE6
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Triality
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityThree

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator



theorem lieDefCharOuter_exceptional (h2 : TrialityThreeOuter) (idx : TauCeti.ValidLieTypeIndex)
    (hfam : CFSG.Yardstones.Md42047359a2a.lieFamily idx.1 =
        CFSG.Yardstones.Md42047359a2a.LieFamily.exceptional)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = idx.1.characteristic)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β ∨ CFSG.Open.GLAPPrimeCoreOf p (fixSubgroup β) = ⊥ := by
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  cases d with
  | E6 q =>
    exact .inl (perfectInLayer_E6_outer q hv hnc e hp hp2
      (hpc.trans (TauCeti.LieTypeIndex.characteristic_E6 q)) hβ hout)
  | E7 q =>
    exact .inl (perfectInLayer_E7_outer q hv hnc e hp hp2
      (hpc.trans (TauCeti.LieTypeIndex.characteristic_E7 q)) hβ hout)
  | E8 q =>
    exact .inl (perfectInLayer_E8_outer q hv hnc e hp hp2
      (hpc.trans (TauCeti.LieTypeIndex.characteristic_E8 q)) hβ hout)
  | F4 q =>
    exact .inl (perfectInLayer_F4_outer q hv hnc e hp hp2
      (hpc.trans (TauCeti.LieTypeIndex.characteristic_F4 q)) hβ hout)
  | G2 q =>
    exact .inl (perfectInLayer_G2_outer q hv hnc e hp hp2
      (hpc.trans (TauCeti.LieTypeIndex.characteristic_G2 q)) hβ hout)
  | twistedE6 q =>
    exact .inl (perfectInLayer_twistedE6_outer q hv hnc e hp hp2
      (hpc.trans (TauCeti.LieTypeIndex.characteristic_twistedE6 q)) hβ hout)
  | trialityD4 q =>
    have hpq := hpc.trans (TauCeti.LieTypeIndex.characteristic_trialityD4 q)
    by_cases h3 : p = 3
    · exact lieDefCharOuter_trialityD4_three h2 q hv hnc e hpq h3 hβ hout
    · exact .inl (perfectInLayer_trialityD4_outer q hv hnc e hp hp2 hpq h3 hβ hout)
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hfam

end CFSG.HardMathSupport.Dickson.DefCharOuter
