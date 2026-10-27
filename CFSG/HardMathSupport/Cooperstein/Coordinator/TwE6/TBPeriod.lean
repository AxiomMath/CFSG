module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBPeriodM0
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBPeriodDigits

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

theorem twPeriodArith_holds : TwPeriodArith := fun _ g hf hg hgf ht =>
  ⟨twM0_arith hf hg hgf ht,
    fun _ _ hn h => twM0_dvd_of_periodic hf (twM0_mul hf g) hn h,
    fun _ _ hn hJ hne h => exists_digits_of_periodic hf hg hgf (twM0_mul hf g) hn hJ hne h⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
