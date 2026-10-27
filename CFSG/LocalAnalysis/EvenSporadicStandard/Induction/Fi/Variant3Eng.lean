module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3EngB

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

theorem fiHyp31V3L_of_rowFacts (pf : FiPinned) (rf : FiV3RowFacts)
    (lx : OddLieCompNotSporadic) :
    Sol78Lit → Hyp31Row IsKFi23 (IsLS [.Fi24Prime]) → ∀ (H : Type) [Group H] [Finite H],
      BelowSec (Sol78PredS fiTypes) H → ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
        CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ¬ IsSporadic ↥N .Fi24Prime →
          Hyp31Core H N IsKFi23 (IsLS [.Fi24Prime]) ∧
            Hyp31FourAL H N IsKFi23 (IsLS [.Fi24Prime]) CanLocV3 := by
  intro lit _ H _ _ ih N hN hidx hkp hN24
  have hcore := hyp31Core_of_rowFacts pf rf lx lit ih hN hidx hkp hN24
  exact ⟨hcore, hyp31FourAL_of_rowFacts pf rf hcore⟩

structure FiV3RowInputs : Prop where
  basic : FiV3Basic
  rows : FiV3RowFacts
  lx : OddLieCompNotSporadic
  outerInv : FiOuterInvolution

end CFSG.EvenSporadicStandard.Induction.Fi.V3
