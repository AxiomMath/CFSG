module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanMonsterThreeCore

public section

namespace CFSG.AGLEmbedding.MonsterThree

open CFSG.Open CFSG.Blueprint TauCeti
open CFSG.RankThree.PartTwo.Sec4.Census (SporadicMultipliers)
open CFSG.GH74.Generic (card_ker_dvd_hopfMultiplier)

theorem center_eq_bot_of_isSimple_nonabelian {T : Type} [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases (inferInstance : (Subgroup.center T).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnc
    exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab

end CFSG.AGLEmbedding.MonsterThree
