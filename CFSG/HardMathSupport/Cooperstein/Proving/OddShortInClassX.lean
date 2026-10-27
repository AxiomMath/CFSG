module

public import CFSG.HardMathSupport.Cooperstein.Proving.OddShort
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving.OddShortInClassX

variable {G : Type} [Group G]

theorem eq_bot_of_K1_inClassX [Finite G] {X B Y : Subgroup G}
    (hX : CFSG.QuasithinUnique.CharTwo X) (hBX : B ≤ X)
    (hYX : Y ≤ X) (hBY : B ≤ Y) (hQY : CFSG.Open.pCoreOf 2 X ≤ Y)
    (hY : ∀ p ∈ Y, ∃ b ∈ B, ∃ q ∈ CFSG.Open.pCoreOf 2 X, p = b * q)
    (hBQ : B ⊓ CFSG.Open.pCoreOf 2 X = ⊥)
    (hB : CFSG.AGLEmbedding.InClassXBlock B)
    (hch : Relation.ReflTransGen (fun H K : Subgroup G => H ≤ K ∧ (H.subgroupOf K).Normal) B Y) :
    B = ⊥ :=
  OddShort.eq_bot_of_K1_short hX hBX hYX hBY hQY hY hBQ hB.1 hch

end CFSG.HardMathSupport.Cooperstein.Proving.OddShortInClassX

end
