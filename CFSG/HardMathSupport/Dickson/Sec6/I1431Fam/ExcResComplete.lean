module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResFinal
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthTwoD
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthExc

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false

section Complete

theorem excTLOther_of_tag {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ExcTLOther τ :=
  excTLOther_of_kinds (excTLKind_suN hτ) (excTLKind_twoD hτ) (excTLKind_exc hτ)

theorem excResidual_f4_proved : ExcResidual FamF4 :=
  excResidual_f4_of (excTLOther_of_tag (Or.inl rfl))

theorem excResidual_e6Good_proved : ExcResidual FamE6Good :=
  excResidual_e6Good_of (excTLOther_of_tag (Or.inr (Or.inl rfl)))

theorem excResidual_twE6Good_proved : ExcResidual FamTwE6Good :=
  excResidual_twE6Good_of (excTLOther_of_tag (Or.inr (Or.inl rfl)))

theorem excResidual_e7_proved : ExcResidual FamE7 :=
  excResidual_e7_of (excTLOther_of_tag (Or.inr (Or.inr (Or.inl rfl))))

theorem excResidual_e8_proved : ExcResidual FamE8 :=
  excResidual_e8_of (excTLOther_of_tag (Or.inr (Or.inr (Or.inr rfl))))

end Complete

end CFSG.HardMathSupport.Dickson.Sec6.I1431
