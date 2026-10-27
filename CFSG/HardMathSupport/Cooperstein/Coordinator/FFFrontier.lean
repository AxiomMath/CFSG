module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFReduction
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsOdd
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8MinDegAll
public import CFSG.HardMathSupport.Cooperstein.Proving.SporadicNoIrrFF

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding

@[expose] def GF2NoFFSporadic : Prop :=
  ∀ n : TauCeti.SporadicName, ¬ IsSQTKSporadic n →
    NoFFModule (TauCeti.CFSGIndex.sporadic n).Group

@[expose] def GF2NoFFLieOdd : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic ≠ 2 →
    ¬ IsClassicalTwoOrG2 (TauCeti.CFSGIndex.lie d).Group → ¬ IsSQTKOddLieIndex d.1 →
      NoFFModule (TauCeti.CFSGIndex.lie d).Group

@[expose] def CoopersteinNoFFExceptional : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
    ¬ IsClassicalTwoOrG2 (TauCeti.CFSGIndex.lie d).Group → ¬ IsSQTKExceptionalTwoIndex d.1 →
      NoFFModule (TauCeti.CFSGIndex.lie d).Group

@[expose] def IsE8TwoIndex : TauCeti.LieTypeIndex → Prop
  | .E8 q => q.p = 2 ∧ q.exponent = 1
  | _ => False

@[expose] def CoopersteinNoFFExceptionalRest : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
    ¬ IsClassicalTwoOrG2 (TauCeti.CFSGIndex.lie d).Group → ¬ IsSQTKExceptionalTwoIndex d.1 →
      ¬ IsE8TwoIndex d.1 → NoFFModule (TauCeti.CFSGIndex.lie d).Group

theorem coopersteinNoFFExceptional_of_rest
    (h : CoopersteinNoFFExceptionalRest) : CoopersteinNoFFExceptional := by
  intro d hd hc hq
  by_cases h8 : IsE8TwoIndex d.1
  · obtain ⟨d, hv⟩ := d
    cases d with
    | E8 q =>
      obtain ⟨hq2, hq1⟩ := h8
      exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_E8_two q hv hq2 hq1)
    | _ => exact absurd h8 (by simp [IsE8TwoIndex])
  · exact h d hd hc hq h8

@[expose] def IsE8Index : TauCeti.LieTypeIndex → Prop
  | .E8 _ => True
  | _ => False

@[expose] def CoopersteinNoFFExceptionalRestNoE8 : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
    ¬ IsClassicalTwoOrG2 (TauCeti.CFSGIndex.lie d).Group → ¬ IsSQTKExceptionalTwoIndex d.1 →
      ¬ IsE8Index d.1 → NoFFModule (TauCeti.CFSGIndex.lie d).Group

theorem coopersteinNoFFExceptionalRest_of_noE8
    (h : CoopersteinNoFFExceptionalRestNoE8) : CoopersteinNoFFExceptionalRest := by
  intro d hd hc hq _
  by_cases h8 : IsE8Index d.1
  · obtain ⟨d, hv⟩ := d
    cases d with
    | E8 q =>
      have hq2 : q.p = 2 := by simpa using hd
      exact noFFModule_of_noIrrFFOffender (CurtisExc.noIrrFFOffender_E8_allq q hv hq2)
    | _ => exact absurd h8 (by simp [IsE8Index])
  · exact h d hd hc hq h8

theorem ffModuleTheorem_of
    (hS : GF2NoFFSporadic) (hO : GF2NoFFLieOdd)
    (hE : CoopersteinNoFFExceptional) : FFModuleTheorem := by
  intro V _ _ hV H L hhyp hFF
  obtain ⟨i, ⟨e⟩⟩ := hhyp.2.2.2
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hhyp.2.1.2.2
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod p)) _ _
  | alternating n hn => exact Or.inr ⟨n, hn, ⟨e⟩⟩
  | lie d =>
    by_cases hc : IsClassicalTwoOrG2 (TauCeti.CFSGIndex.lie d).Group
    · exact Or.inl (Proving.isClassicalTwoOrG2_of_mulEquiv e.symm hc)
    · by_cases hd : d.1.characteristic = 2
      · by_cases hq : IsSQTKExceptionalTwoIndex d.1
        · exact absurd hFF (noFFModule_of_noIrrFFOffender (noIrrFFOffender_exceptional_two d hq)
            V hV H L hhyp ⟨e⟩)
        · exact absurd hFF (hE d hd hc hq V hV H L hhyp ⟨e⟩)
      · by_cases hq : IsSQTKOddLieIndex d.1
        · exact absurd hFF (noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_odd d hq)
            V hV H L hhyp ⟨e⟩)
        · exact absurd hFF (hO d hd hc hq V hV H L hhyp ⟨e⟩)
  | sporadic n =>
    by_cases hq : IsSQTKSporadic n
    · exact absurd hFF (noFFModule_of_noIrrFFOffender (Proving.noIrrFFOffender_sporadic n hq)
        V hV H L hhyp ⟨e⟩)
    · exact absurd hFF (hS n hq V hV H L hhyp ⟨e⟩)

end CFSG.HardMathSupport.Cooperstein.Coordinator
