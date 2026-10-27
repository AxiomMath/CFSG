module

public import CFSG.CharacterTheory.TwoRankLowerBound.PiTrace
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def quarticValue (residue : ZMod 4) : ℂ :=
  if residue.val = 0 then 1 else if residue.val = 1 then Complex.I else if residue.val = 2 then -1
    else -Complex.I

theorem quarticValue_zero : quarticValue 0 = 1 := by simp [quarticValue]

set_option backward.isDefEq.respectTransparency false in
theorem quarticValue_add (left right : ZMod 4) :
    quarticValue (left + right) = quarticValue left * quarticValue right := by
  unfold quarticValue
  rw [ZMod.val_add]
  fin_cases left <;> fin_cases right <;> apply Complex.ext <;>
    norm_num [ZMod.val]

@[expose] def quarticAddChar : AddChar (ZMod 4) ℂ :=
  { toFun := quarticValue
    map_zero_eq_one' := quarticValue_zero
    map_add_eq_mul' := quarticValue_add }

noncomputable def quaternionQuarticChar (parameter : ℕ) (hdiv : 4 ∣ parameter) :
    AddChar (ZMod (2 * parameter)) ℂ :=
  quarticAddChar.compAddMonoidHom
    (ZMod.castHom (dvd_mul_of_dvd_right hdiv 2) (ZMod 4)).toAddMonoidHom

theorem quaternionQuarticChar_parameter (parameter : ℕ) (hdiv : 4 ∣ parameter) :
    quaternionQuarticChar parameter hdiv (parameter : ZMod (2 * parameter)) = 1 := by
  unfold quaternionQuarticChar
  simp only [AddChar.compAddMonoidHom_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_ofClass, map_natCast]
  have hzero : (parameter : ZMod 4) = 0 := (ZMod.natCast_eq_zero_iff parameter 4).mpr hdiv
  rw [hzero]
  exact quarticValue_zero

theorem quarticAddChar_neg (residue : ZMod 4) :
    quarticAddChar (-residue) * quarticAddChar residue = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel]
  exact quarticValue_zero

theorem quaternionQuarticChar_one (parameter : ℕ) (hdiv : 4 ∣ parameter) :
    quaternionQuarticChar parameter hdiv 1 = Complex.I := by
  unfold quaternionQuarticChar
  simp only [AddChar.compAddMonoidHom_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_ofClass, map_one]
  rfl

theorem quaternionQuarticChar_ne_one (parameter : ℕ) (hdiv : 4 ∣ parameter) :
    quaternionQuarticChar parameter hdiv ≠ 1 := by
  intro hequal
  have hvalue := congrArg (fun character : AddChar (ZMod (2 * parameter)) ℂ => character 1) hequal
  rw [quaternionQuarticChar_one, AddChar.one_apply] at hvalue
  have himaginary := congrArg Complex.im hvalue
  norm_num at himaginary

theorem quaternionQuarticChar_double_ne_one (parameter : ℕ) (hdiv : 4 ∣ parameter) :
    quaternionQuarticChar parameter hdiv + quaternionQuarticChar parameter hdiv ≠ 1 := by
  intro hequal
  have hvalue := congrArg (fun character : AddChar (ZMod (2 * parameter)) ℂ => character 1) hequal
  rw [AddChar.add_apply, quaternionQuarticChar_one, Complex.I_mul_I, AddChar.one_apply] at hvalue
  have hreal := congrArg Complex.re hvalue
  norm_num at hreal

theorem quaternionQuarticChar_neg_mul_self (parameter : ℕ) (hdiv : 4 ∣ parameter)
    (residue : ZMod (2 * parameter)) :
    quaternionQuarticChar parameter hdiv (-residue) * quaternionQuarticChar parameter hdiv residue = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

theorem quaternionQuarticChar_sum (parameter : ℕ) [NeZero parameter] (hdiv : 4 ∣ parameter) :
    ∑ residue : ZMod (2 * parameter), quaternionQuarticChar parameter hdiv residue = 0 :=
  AddChar.sum_eq_zero_of_ne_one (quaternionQuarticChar_ne_one parameter hdiv)

theorem quaternionQuarticChar_square_sum (parameter : ℕ) [NeZero parameter] (hdiv : 4 ∣ parameter) :
    ∑ residue : ZMod (2 * parameter), (quaternionQuarticChar parameter hdiv residue) ^ 2 = 0 := by
  have hsum := AddChar.sum_eq_zero_of_ne_one (quaternionQuarticChar_double_ne_one parameter hdiv)
  simpa only [AddChar.add_apply, pow_two] using hsum

end CFSG.TwoRankLowerBound.Helpers
