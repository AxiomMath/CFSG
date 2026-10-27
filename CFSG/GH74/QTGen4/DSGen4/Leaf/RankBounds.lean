module

public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

theorem dsFrattini_eq_map {G : Type} [Group G] (R : Subgroup G) :
    dsFrattini R = (frattini ↥R).map R.subtype := rfl

theorem leafRankBounds : LeafRankBounds := by
  intro G _ _
  have hG : CFSG.GH74.Gen4 G := Finite4.gen4
  refine ⟨fun R hR => ?_, fun E hE => ?_⟩
  ·
    obtain ⟨d, hd, hcard, -⟩ :=
      CFSG.RankThree.PartOne.SectionalRank.frattini_quotient_elementary_of_rank_le_four hR
        (CFSG.GH74.Gen4.rank_le_four hG hR)
    have key : (dsFrattini R).relIndex R = (frattini ↥R).index := by
      rw [dsFrattini_eq_map, Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective R.subtype_injective]
    rw [key, Subgroup.index, hcard]
    exact (Nat.pow_le_pow_right (by norm_num) hd).trans (by norm_num)
  ·
    exact (CFSG.GH74.SectionalTwoRankLE.card_le_of_elementary hG E hE).trans (by norm_num)

end CFSG.GH74.QTGen4.DSGen4
