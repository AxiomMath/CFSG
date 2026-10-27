module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Level
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open Subgroup CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_fixedSubgroup_conjNormal_iff (L : Subgroup Y) [L.Normal] (x : Y) (y : ↥L) :
    y ∈ fixedSubgroup (MulAut.conjNormal x : MulAut ↥L) ↔
      (y : Y) ∈ centralizer ({x} : Set Y) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : x * (y : Y) * x⁻¹ = (y : Y) := congrArg Subtype.val h
    calc (y : Y) * x = x * (y : Y) * x⁻¹ * x := by rw [h1]
      _ = x * (y : Y) := by group
  · intro h
    apply Subtype.ext
    change x * (y : Y) * x⁻¹ = (y : Y)
    calc x * (y : Y) * x⁻¹ = (y : Y) * x * x⁻¹ := by rw [h]
      _ = (y : Y) := by group

theorem succ_pRank_fixed_le {p : ℕ} [Fact p.Prime] (L : Subgroup Y) [L.Normal] {x : Y}
    (hx : orderOf x = p) (hxL : x ∉ L) :
    CFSG.Open.pRank p (fixedSubgroup (MulAut.conjNormal x : MulAut ↥L)) + 1 ≤
      CFSG.Open.pRank p (centralizer ({x} : Set Y)) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨E, hEle, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp1
    (fixedSubgroup (MulAut.conjNormal x : MulAut ↥L))
  refine KD291Lvl.outer_rank (L := L) (E := E.map L.subtype) (x := x)
    (k := CFSG.Open.pRank p (fixedSubgroup (MulAut.conjNormal x : MulAut ↥L)))
    (CFSG.SectionRank.isElemAbelian_map hE L.subtype) ?_ ?_ ?_ hx hxL
  · rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact hEc
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_fixedSubgroup_conjNormal_iff L x y).1 (hEle hy)

theorem three_le_pRank_of_two_le_fixed {p : ℕ} [Fact p.Prime] (L : Subgroup Y) [L.Normal]
    {x : Y} (hx : orderOf x = p) (hxL : x ∉ L)
    (h2 : 2 ≤ CFSG.Open.pRank p (fixedSubgroup (MulAut.conjNormal x : MulAut ↥L))) :
    3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set Y)) := by
  have := succ_pRank_fixed_le L hx hxL
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
