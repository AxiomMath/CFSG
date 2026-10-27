module

public import CFSG.ClassicalInvolution.Q3.Closing
public import CFSG.Sporadic.Mathieu.M11
import all Init.Data.Array.Basic
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Mathieu.Native

theorem m11_check_kernel : check 11 m11Data = true := by decide +kernel

theorem m11_hyp_kernel : Hyp NativeSporadic.M11 m11Data m11a m11b :=
  ⟨by norm_num, closure_pair_eq_top m11_eq _ _, rep_m11a, rep_m11b, m11_check_kernel⟩

theorem card_m11_kernel : Nat.card NativeSporadic.M11 = 7920 := by
  rw [card_eq m11_hyp_kernel]
  rfl

theorem isSimpleGroup_m11_kernel : IsSimpleGroup NativeSporadic.M11 :=
  isSimpleGroup_of_check m11_hyp_kernel (by decide) (by norm_num) (by norm_num [m11Data])
    (by norm_num [m11Data]) (by norm_num [m11Data]) (by decide) (by decide)

theorem m11Facts : M11Facts :=
  ⟨isSimpleGroup_m11_kernel, card_m11_kernel⟩

end CFSG.ClassicalInvolution.Q3
