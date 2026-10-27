module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Basic
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Central
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Quasi
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAux
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxE6X2
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxE8
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxD4

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


theorem twNormalizer_f4Six (K : Type) [Field K] [Finite K] (hK : TwClass.f4Six.minQ ≤ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) :
    TwFrameNormalizerSolvable TwClass.f4Six.tag K (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D) := by
  obtain ⟨h1q, h1o⟩ := NormalizerAux.f4Six_X₁ K hK D
  obtain ⟨h2q, h2o⟩ := NormalizerAux.f4Six_X₂ K hK D
  exact NormalizerAux.twFrameNormalizerSolvable_of_out ⟨h1q, h2q⟩
    (TwBasicAux.twBasic_of_quasi TwClass.f4Six D h1q) (twCentral TwClass.f4Six K hK D) h1o h2o

section E6Sc


theorem twNormalizer_e6Six (K : Type) [Field K] [Finite K] (hK : TwClass.e6Six.minQ ≤ Nat.card K)
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) :
    TwFrameNormalizerSolvable TwClass.e6Six.tag K (TwClass.e6Six.X₁ D ⊔ TwClass.e6Six.X₂ D) := by
  obtain ⟨h1q, h1o⟩ := NormalizerAux.e6Six_X₁ K hK D
  have h2q := (twQuasi TwClass.e6Six K hK D).2
  have h2o := NormalizerAux.e6Six_X₂_outer D h2q.1
  exact NormalizerAux.twFrameNormalizerSolvable_of_out ⟨h1q, h2q⟩
    (TwBasicAux.twBasic_of_quasi TwClass.e6Six D h1q) (twCentral TwClass.e6Six K hK D) h1o h2o

end E6Sc

theorem twNormalizer_e8Ten (K : Type) [Field K] [Finite K] (hK : TwClass.e8Ten.minQ ≤ Nat.card K)
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) :
    TwFrameNormalizerSolvable TwClass.e8Ten.tag K (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) := by
  obtain ⟨h1q, h1o⟩ := NormalizerAux.e8Ten_X₁ K D
  obtain ⟨h2q, h2o⟩ := NormalizerAux.e8Ten_X₂ K D
  exact NormalizerAux.twFrameNormalizerSolvable_of_out ⟨h1q, h2q⟩
    (TwBasicAux.twBasic_of_quasi TwClass.e8Ten D h1q) (twCentral TwClass.e8Ten K hK D) h1o h2o

theorem twNormalizer_e8Twelve (K : Type) [Field K] [Finite K]
    (hK : TwClass.e8Twelve.minQ ≤ Nat.card K)
    (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w) :
    TwFrameNormalizerSolvable TwClass.e8Twelve.tag K
      (TwClass.e8Twelve.X₁ D ⊔ TwClass.e8Twelve.X₂ D) := by
  obtain ⟨h1q, h1o⟩ := NormalizerAux.e8Twelve_X₁ D
  obtain ⟨h2q, h2o⟩ := NormalizerAux.e8Twelve_X₂ D
  exact NormalizerAux.twFrameNormalizerSolvable_of_out ⟨h1q, h2q⟩
    (TwBasicAux.twBasic_of_quasi TwClass.e8Twelve D h1q) (twCentral TwClass.e8Twelve K hK D) h1o h2o

section Generic


theorem twNormalizer (c : TwClass) (K : Type) [Field K] [Finite K] (hK : c.minQ ≤ Nat.card K)
    (D : LangLevi c.tag K c.w) : TwFrameNormalizerSolvable c.tag K (c.X₁ D ⊔ c.X₂ D) := by
  cases c
  · exact twNormalizer_f4Six K hK D
  · exact twNormalizer_e6Six K hK D
  · exact twNormalizer_e8Ten K hK D
  · exact twNormalizer_e8Twelve K hK D

end Generic

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
