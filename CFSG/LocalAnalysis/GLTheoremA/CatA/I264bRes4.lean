module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bRes3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HTD42SevenRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA

structure I264bResidual4 : Prop where
  u38_3 : KDescFam 3 fU38
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

section I264bRes4


theorem i264bResidual3_of_4 (h : I264bResidual4) : I264bResidual3 :=
  ⟨td42SevenRank_holds, h.u38_3, h.linear, h.unitary, h.symplectic, h.omegaPlus, h.omegaMinus, h.e6, h.e7, h.e8,
    h.f4, h.g2, h.twE6, h.triD4, h.reeTits⟩

end I264bRes4

end CFSG.LocalAnalysis.GLTheoremA

end
