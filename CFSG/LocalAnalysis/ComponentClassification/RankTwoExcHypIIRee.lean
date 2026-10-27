module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIBasic
public import CFSG.Sporadic.Schreier.TitsInner

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.ComponentClassification.AS76b

theorem hypII_of_reeTits
    {A : Type} [Group A] [Finite A] (hA : commutator A = ⊤)
    {f : ℕ} (h : CFSG.Blueprint.ReeTitsModel (A ⧸ center A) .twistedF4 2 f ∨
      CFSG.Blueprint.ReeTitsModel (A ⧸ center A) .Tits 2 1) : HypII A := by
  have hs : IsSimpleGroup (A ⧸ center A) := by
    rcases h with h | h
    · exact (CFSG.LieType.Simplicity.fam_2f4_simplicity _ 2 f h).2
    · exact (CFSG.LieType.Simplicity.fam_tits_simplicity _ 2 1 h).2
  exact hypII_of_forall_inner (center_quotient_eq_bot hA hs)
    (CFSG.Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner _ f (Or.inr h)) hA
    (MulEquiv.refl _)

end CFSG.ComponentClassification.RankTwoExcHypII
