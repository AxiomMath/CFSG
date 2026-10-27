module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalIndexA
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalIndexC
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalIndexO
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalIndexU
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcIndex
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcIndexRee
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcIndexTits

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open TauCeti

section


theorem e27LieOuterAut_of_families
    (hA : LinearDiagSlice) (hU : UnitaryRestSlice)
    (hB2 : E27LieOuterAutAt (fun i => ∃ q, i = .B 2 q ∧ q.p = 2))
    (hD4 : E27LieOuterAutAt (fun i => ∃ q, i = .D 4 q))
    (hE6 : E27LieOuterAutAt (fun i => ∃ q, i = .E6 q))
    (htE6 : E27LieOuterAutAt (fun i => ∃ q, i = .twistedE6 q))
    (hT : E27LieOuterAutAt (fun i => ∃ q, i = .trialityD4 q)) :
    CFSG.HardMathSupport.Foote.E27.E27LieOuterAut := by
  refine e27LieOuterAut_of_all ?_
  rintro K _ _ ⟨i, hv⟩ - he hAut u hu3 hout ha hb hc
  have hr := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases i with
  | A r q =>
    exact e27LieOuterAutAt_A_all_of_diag hA K ⟨_, hv⟩ ⟨r, q, rfl⟩ he hAut u hu3 hout ha hb hc
  | twistedA r q =>
    exact e27LieOuterAutAt_twistedA_of_rest hU K ⟨_, hv⟩ ⟨r, q, rfl⟩ he hAut u hu3 hout ha hb hc
  | B r q =>
    by_cases hp : q.p = 2
    · by_cases hr2 : r = 2
      · subst hr2
        exact hB2 K ⟨_, hv⟩ ⟨q, rfl, hp⟩ he hAut u hu3 hout ha hb hc
      · have hr3 : 3 ≤ r := by have := hr.1; omega
        exact e27LieOuterAutAt_B_even_three K ⟨_, hv⟩ ⟨r, q, rfl, hp, hr3⟩ he hAut u hu3 hout ha hb
          hc
    · exact e27LieOuterAutAt_B_odd K ⟨_, hv⟩ ⟨r, q, rfl, hp⟩ he hAut u hu3 hout ha hb hc
  | C r q => exact e27LieOuterAutAt_C K ⟨_, hv⟩ ⟨r, q, rfl⟩ he hAut u hu3 hout ha hb hc
  | D r q =>
    by_cases hr4 : r = 4
    · subst hr4
      exact hD4 K ⟨_, hv⟩ ⟨q, rfl⟩ he hAut u hu3 hout ha hb hc
    · have hr5 : 5 ≤ r := by omega
      exact e27LieOuterAutAt_D K ⟨_, hv⟩ ⟨r, q, rfl, hr5⟩ he hAut u hu3 hout ha hb hc
  | twistedD r q =>
    exact e27LieOuterAutAt_twistedD K ⟨_, hv⟩ ⟨r, q, rfl⟩ he hAut u hu3 hout ha hb hc
  | E6 q => exact hE6 K ⟨_, hv⟩ ⟨q, rfl⟩ he hAut u hu3 hout ha hb hc
  | E7 q => exact e27LieOuterAutAt_E7 K ⟨_, hv⟩ ⟨q, rfl⟩ he hAut u hu3 hout ha hb hc
  | E8 q => exact e27LieOuterAutAt_E8 K ⟨_, hv⟩ ⟨q, rfl⟩ he hAut u hu3 hout ha hb hc
  | F4 q => exact e27LieOuterAutAt_F4 K ⟨_, hv⟩ ⟨q, rfl⟩ he hAut u hu3 hout ha hb hc
  | G2 q => exact e27LieOuterAutAt_G2 K ⟨_, hv⟩ ⟨q, rfl⟩ he hAut u hu3 hout ha hb hc
  | twistedE6 q => exact htE6 K ⟨_, hv⟩ ⟨q, rfl⟩ he hAut u hu3 hout ha hb hc
  | trialityD4 q => exact hT K ⟨_, hv⟩ ⟨q, rfl⟩ he hAut u hu3 hout ha hb hc
  | suzuki m => exact e27LieOuterAutAt_suzuki K ⟨_, hv⟩ ⟨m, rfl⟩ he hAut u hu3 hout ha hb hc
  | reeG2 m => exact e27LieOuterAutAt_reeG2 K ⟨_, hv⟩ ⟨m, rfl⟩ he hAut u hu3 hout ha hb hc
  | reeF4 m => exact e27LieOuterAutAt_reeF4 K ⟨_, hv⟩ ⟨m, rfl⟩ he hAut u hu3 hout ha hb hc
  | tits => exact e27LieOuterAutAt_tits K ⟨_, hv⟩ rfl he hAut u hu3 hout ha hb hc

end

end CFSG.HardMathSupport.Malle.E27Lie
