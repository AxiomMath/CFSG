module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEDefs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

@[expose] def EIHAll (n : ℕ) : Prop :=
      EIH n


theorem EIHAll.of_eih {n : ℕ} (h : EIH n) : EIHAll n := by
  exact h

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
