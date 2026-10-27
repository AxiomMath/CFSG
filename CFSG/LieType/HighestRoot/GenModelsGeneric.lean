module

public import CFSG.LieType.HighestRoot.GenModels
public import CFSG.ClassicalInvolution.Generic.Induction

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Assembly.LowTwoRank

theorem highestRootGen_genericModelUniv
    (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e) :
    HighestRootGen (CFSG.ClassicalInvolution.Generic.modelUniv t n p e hp).D p := by
  have hf : CFSG.ClassicalInvolution.ModelFacts.IsFundTag t := by
    cases t <;> trivial
  cases t <;> exact highestRootGen_modelUniv _ n p e hp hf hadm

end CFSG.LieType.HighestRoot
