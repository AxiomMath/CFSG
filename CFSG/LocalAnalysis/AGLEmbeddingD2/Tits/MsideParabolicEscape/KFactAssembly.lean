module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactL32

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def KFactU33SylowPermute : Prop :=
  ∀ (N : Type) [Group N] [Finite N], IsSimpleGroup N → ¬ IsMulCommutative N →
    StatedClassicalModel N .PSU 3 3 1 → ∀ Y : Subgroup (MulAut N), innSub N ≤ Y →
      (innSub N).relIndex Y ≤ 2 → ∀ S : Subgroup (MulAut N), IsSylowTwoOf S Y →
        ∃ P : Subgroup (MulAut N), P ≤ innSub N ∧ Nat.card P = 3 ∧
          (S : Set (MulAut N)) * P = (P : Set (MulAut N)) * S

theorem kFactRankTwoSylowPermute_of_u33 (hU : KFactU33SylowPermute) :
    KFactRankTwoSylowPermute := by
  intro N _ _ hs hnc hty Y hY h2 hperm hL S hS
  rcases hty with he | hL32 | hU33
  · obtain ⟨e⟩ := he
    exact a6_case hs hnc e Y hY h2 (fun h => hperm ⟨e⟩ h) S hS
  · exact l32_case hs hnc hL32 Y hY (hL hL32) S hS
  · exact hU N hs hnc hU33 Y hY h2 S hS

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
