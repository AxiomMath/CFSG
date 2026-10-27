module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614KTrBasic
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614KTrCases
import CFSG.HardMathSupport.Solomon.Coordinator.I28_5Holds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.OmegaFacts
open P614KTr

theorem kFactTransvRankOne_holds : KFactTransvRankOne := by
  intro V _ _ hV X K τ hO2 hτX hτK hτ hKX hKn hKs hKna hrank hX
  haveI : Finite (MulAut V) := MulEquiv.finite_left
  have hττ : τ * τ = 1 := transvection_mul_self hV hτ
  obtain ⟨r, W, hW⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.input28_5_holds V hV X hO2 τ hτX hτ
  have hMcL : IsMcLaughlinGroup ↥X :=
    isMcLaughlinGroup_of_decomposition hO2 hKX hKn hKs hKna hτX hττ hX hτ.1 hW
  have hidx : (K.subgroupOf X).index = 2 := index_eq_two hKX hKn hτX hτK hττ hX
  have hKna' : ∃ a b : ↥(K.subgroupOf X), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKna
    refine ⟨(subgroupOfEquivOfLe hKX).symm a, (subgroupOfEquivOfLe hKX).symm b, fun h => hab ?_⟩
    simpa using congrArg (subgroupOfEquivOfLe hKX) h
  have hr : ¬ Rank2 (⊤ : Subgroup ↥X) := by
    intro hR
    obtain ⟨a, haX, b, hbX, h1, h2, h12, h1ne, hnot⟩ :=
      Rank2.map X.subtype X.subtype_injective (Subgroup.map_subtype_le ⊤) hR
    have hRK : Rank2 K := ⟨a, mem_of_pow_three hKX hKn hτX hττ hX haX h1, b,
      mem_of_pow_three hKX hKn hτX hττ hX hbX h2, h1, h2, h12, h1ne, hnot⟩
    obtain ⟨E, k, hE, hcard, hk⟩ :=
      exists_elemAbelian_three_pow_of_rank2 (rank2_top_of_subgroup hRK)
    have hle := hrank (E.map K.subtype) (Subgroup.map_subtype_le E)
      (isElemAbelian_map K.subtype hE)
    rw [Subgroup.card_map_of_injective K.subtype_injective, hcard] at hle
    have h9 : 9 ≤ 3 ^ k :=
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    exact absurd (h9.trans hle) (by norm_num)
  obtain ⟨e⟩ := perm_five_of_isMcLaughlinGroup hMcL hKn hidx hKna' hr
  refine ⟨?_, ⟨e⟩⟩
  have hmap : (K.subgroupOf X).map (e : ↥X →* Equiv.Perm (Fin 5)) = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two (by rw [Subgroup.index_map_equiv]; exact hidx)
  exact ⟨(subgroupOfEquivOfLe hKX).symm.trans
    ((e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap))⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
