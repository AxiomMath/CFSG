module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Pair56
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Coset56

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Tab56_of (hS : Asc82SchurU43) : Asc82Tab56 :=
  ⟨asc82Pair56_of hS, asc82Coset56_of hS⟩

end CFSG.OddStandard.SmallF3.Omega
