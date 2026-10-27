module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveCo1
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Census
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveC
public import Certificates.Certificate13670
import all CFSG.Monster.Existence.Co1Bridge

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMFive

open CFSG.Sporadic.Co1Schreier CFSG.Monster.Existence.Co1Bridge

section Bridge


theorem gA24_eq_A₁ : gA24 = A₁ := by
  apply Units.ext
  rw [val_A₁]
  show aMat = _
  rw [← decode_seed1]
  rfl

theorem gB24_eq_A₂ : gB24 = A₂ := by
  apply Units.ext
  rw [val_A₂]
  show bMat = _
  rw [← decode_seed2]
  rfl

theorem J24_eq_GA : J24 = GA := by
  rw [GA_eq]
  show Subgroup.closure {gA24, gB24} = Subgroup.closure {A₁, A₂}
  rw [gA24_eq_A₁, gB24_eq_A₂]

end Bridge

section Inputs


theorem co1FiveInputs : Co1FiveInputs :=
  Co1FiveInputs.of_eq J24_eq_GA
    (fun s hs => TabCo1.tabCo1_census Certificates.certificate13670 s hs)
    (fun x hx => TabCo1.card_cent_fiveA_le x hx)
    (fun x hx => TabCo1.card_cent_fiveB_le x hx)
    (fun x hx => TabCo1.card_cent_fiveC_le x hx)

end Inputs

end CFSG.HardMathSupport.Dickson.I271.TabMFive
