module

public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.Schreier.J1Outer

public section

namespace CFSG.ComponentClassification.SporadicSchreierDispatch

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def SporadicSchreierCase (s : TauCeti.SporadicName) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    Nonempty (T ≃* NativeSporadic.Carrier s) → Group.IsSolvable (Outer T)

theorem sporadicSchreierCase_of_outer {s : TauCeti.SporadicName}
    (h : Group.IsSolvable (Outer (NativeSporadic.Carrier s))) : SporadicSchreierCase s :=
  fun _ _ _ _ _ ⟨e⟩ => (LocalAnalysis.ComponentInitial.outer_isomorphism e).2.2 h

theorem sporadicRep_schreier_of_cases (h : ∀ s, SporadicSchreierCase s) (S : Type) [Group S]
    [Finite S] [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a)
    (hS : NativeSporadic.SporadicRep S) : Group.IsSolvable (Outer S) := by
  obtain ⟨s, he⟩ := hS
  exact h s S hnonab he

theorem sporadicSchreierCase_M11 : SporadicSchreierCase .M11 :=
  sporadicSchreierCase_of_outer Sporadic.Schreier.at_m11_schreier.2.2

theorem sporadicSchreierCase_M12 : SporadicSchreierCase .M12 :=
  sporadicSchreierCase_of_outer Sporadic.Schreier.at_m12_schreier.2.2

theorem sporadicSchreierCase_M22 : SporadicSchreierCase .M22 :=
  sporadicSchreierCase_of_outer Sporadic.Schreier.at_m22_schreier.2.2

theorem sporadicSchreierCase_M23 : SporadicSchreierCase .M23 :=
  sporadicSchreierCase_of_outer Sporadic.Schreier.at_m23_schreier.2.2

theorem sporadicSchreierCase_M24 : SporadicSchreierCase .M24 :=
  sporadicSchreierCase_of_outer Sporadic.Schreier.at_m24_schreier.2.2

theorem sporadicSchreierCase_J1 : SporadicSchreierCase .J1 :=
  sporadicSchreierCase_of_outer Sporadic.Schreier.at_j1_schreier.2.2

theorem sporadicRep_schreier_of_remaining (hJ2 : SporadicSchreierCase .J2)
    (hJ3 : SporadicSchreierCase .J3) (hJ4 : SporadicSchreierCase .J4)
    (hCo1 : SporadicSchreierCase .Co1) (hCo2 : SporadicSchreierCase .Co2)
    (hCo3 : SporadicSchreierCase .Co3) (hFi22 : SporadicSchreierCase .Fi22)
    (hFi23 : SporadicSchreierCase .Fi23) (hFi24 : SporadicSchreierCase .Fi24Prime)
    (hHS : SporadicSchreierCase .HS) (hMcL : SporadicSchreierCase .McL)
    (hHe : SporadicSchreierCase .He) (hRu : SporadicSchreierCase .Ru)
    (hSuz : SporadicSchreierCase .Suz) (hON : SporadicSchreierCase .ONan)
    (hHN : SporadicSchreierCase .HN) (hLy : SporadicSchreierCase .Ly)
    (hTh : SporadicSchreierCase .Th) (hB : SporadicSchreierCase .B)
    (hM : SporadicSchreierCase .M) (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (hS : NativeSporadic.SporadicRep S) :
    Group.IsSolvable (Outer S) := by
  refine sporadicRep_schreier_of_cases (fun s => ?_) S hnonab hS
  have := sporadicSchreierCase_M11
  have := sporadicSchreierCase_M12
  have := sporadicSchreierCase_M22
  have := sporadicSchreierCase_M23
  have := sporadicSchreierCase_M24
  have := sporadicSchreierCase_J1
  cases s <;> assumption

end CFSG.ComponentClassification.SporadicSchreierDispatch
