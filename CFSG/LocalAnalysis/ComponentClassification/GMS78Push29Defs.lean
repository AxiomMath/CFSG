module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Setup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

@[expose] def L2Res : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), BenderHyp G L →
    ∀ f : ℕ, 3 ≤ f → Nonempty (rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) → False

end CFSG.ComponentClassification.GMS78
