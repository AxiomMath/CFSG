module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcUntwisted
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTwistedE6
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityGe5
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriClassA
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriThree

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Yardstones.Md42047359a2a (LieFamily)

theorem outerCentExcTags_excUntwisted : OuterCentExcTags IsExcUntwisted := by
  intro S _ _ hS hnc idx htag he p hp hp2 hpc β hβ hout
  obtain ⟨d, hv⟩ := idx
  cases d with
  | G2 q =>
    exact outerCentData_excUntwisted S hS hnc ⟨.G2 q, hv⟩ ⟨q, Or.inl rfl⟩ he p hp hp2 hpc β hβ hout
  | F4 q =>
    exact outerCentData_excUntwisted S hS hnc ⟨.F4 q, hv⟩ ⟨q, Or.inr (Or.inl rfl)⟩ he p hp hp2 hpc
      β hβ hout
  | E6 q =>
    exact outerCentData_excUntwisted S hS hnc ⟨.E6 q, hv⟩ ⟨q, Or.inr (Or.inr (Or.inl rfl))⟩ he p hp
      hp2 hpc β hβ hout
  | E7 q =>
    exact outerCentData_excUntwisted S hS hnc ⟨.E7 q, hv⟩
      ⟨q, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩ he p hp hp2 hpc β hβ hout
  | E8 q =>
    exact outerCentData_excUntwisted S hS hnc ⟨.E8 q, hv⟩
      ⟨q, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩ he p hp hp2 hpc β hβ hout
  | _ => simp [IsExcUntwisted] at htag

theorem outerCentExcTags_trialityD4 : OuterCentExcTags IsExcTrialityD4 := by
  intro S _ _ hS hnc idx htag he p hp hp2 hpc β hβ hout
  by_cases hp3 : p = 3
  · subst hp3
    exact outerCentData_trialityD4_three_of
      (fun f hf K _ _ _ hK σ hσ => outerCentData_three_classA hf hK σ hσ)
      S idx htag he hpc β hβ hout
  · exact outerCentData_trialityD4_ne_three S hS hnc idx htag he p hp hp2 hp3 hpc β hβ hout

theorem outerCentOn_exceptional : OuterCentOn LieFamily.exceptional :=
  outerCentOn_exceptional_of_tags outerCentExcTags_excUntwisted outerCentExcTags_twistedE6
    outerCentExcTags_trialityD4

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
