module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallHeisLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallIdent
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.AGLEmbeddingD2

section Certified


theorem sporCore_of_isMcL {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (hK : IsSporadicGroup .McL K) (T : Sylow 5 K) :
    SporCore 5 K T :=
  sporCore_of_d2HeisLocalAt Nat.prime_five le_rfl d2HeisLocalAt_mcl hs hnab hK T

theorem autFixInner_of_isMcL {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (hK : IsSporadicGroup .McL K) (T : Sylow 5 K) :
    AutFixInner 5 K T :=
  autFixInner_of_d2HeisLocalAt Nat.prime_five d2HeisLocalAt_mcl hs hnab hK T

end Certified

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
