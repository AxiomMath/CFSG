module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bRes4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264sU38Three

public section

namespace CFSG.LocalAnalysis.GLTheoremA

structure I264bResidual5 : Prop where
  linear : ∀ p, HDesc.KDescFamRes p fLinear
  unitary : ∀ p, HDesc.KDescFamRes p fUnitary
  symplectic : ∀ p, HDesc.KDescFamRes p fSymplectic
  omegaPlus : ∀ p, HDesc.KDescFamRes p fOmegaPlus
  omegaMinus : ∀ p, HDesc.KDescFamRes p fOmegaMinus
  e6 : ∀ p, HDesc.KDescFamRes p fE6
  e7 : ∀ p, HDesc.KDescFamRes p fE7
  e8 : ∀ p, HDesc.KDescFamRes p fE8
  f4 : ∀ p, HDesc.KDescFamRes p fF4
  g2 : ∀ p, HDesc.KDescFamRes p fG2
  twE6 : ∀ p, HDesc.KDescFamRes p fTwE6
  triD4 : ∀ p, HDesc.KDescFamRes p fTriD4
  reeTits : ∀ p, HDesc.KDescFamRes p fReeTits

section I264bRes5


theorem i264bResidual4_of_5 (h : I264bResidual5) : I264bResidual4 :=
  ⟨kDescFam_u38_three, h.linear, h.unitary, h.symplectic, h.omegaPlus, h.omegaMinus, h.e6, h.e7, h.e8, h.f4, h.g2,
    h.twE6, h.triD4, h.reeTits⟩

end I264bRes5

end CFSG.LocalAnalysis.GLTheoremA

end
