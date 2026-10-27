module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def C143Alt : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    IsPGroup 3 (Subgroup.center Y) → Lemma25Ns.IsAltType (Y ⧸ Subgroup.center Y) →
    ∀ α : MulAut Y, α ^ 3 = 1 → ∀ J : Subgroup Y,
      GLAPComponent 3 (Lemma510Ns.fixSub α) J →
      ¬ (IsSLThreeExc (barOf 3 J) ∨ IsSUThreeExc (barOf 3 J))

end CFSG.HardMathSupport.Solomon.Coordinator
