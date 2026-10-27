module

public import CFSG.LocalAnalysis.EvenSmallLie.Children

public section

namespace CFSG.EvenSmallLie

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Recognition

theorem outcome_of_children (h1 : ChildG2F4) (h2 : Child2E6) (h3 : ChildSp6Centerless)
    (h4 : ChildSp6Cover) (h5 : ChildU6Centerless) (h6 : ChildU6Cover)
    (h7 : ChildO8PlusCenterless) (h8 : ChildO8PlusCover) (h9 : ChildO8Minus)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (hres : Exact.EvenStandardResidual L)
    (hbcd : Exact.ResidualB L ∨ Exact.ResidualC L ∨ Exact.ResidualD L) :
    NativeSporadic.IsSporadic G .Co3 ∨ NativeSporadic.IsSporadic G .Fi22 ∨
      NativeSporadic.IsSporadic G .B := by
  have hset : StandardSetting G L := ⟨inferInstance, hnonab, hK, hL, hcore, S, hS⟩
  have hZ2 : IsPGroup 2 (center L) := hres.1
  rcases hbcd with ⟨hc, hB | hB | hB⟩ | hC | ⟨hc, hD⟩
  · exact (h1 G L hset hc (Or.inl hB)).elim
  · exact (h1 G L hset hc (Or.inr hB)).elim
  · exact Or.inr (Or.inr (h2 G L hset hc hB))
  · by_cases hcb : center L = ⊥
    · rcases hC with hC | hC | hC
      · exact (h3 G L hset hcb hC).elim
      · exact (h5 G L hset hcb hC).elim
      · exact (h7 G L hset hcb hC).elim
    · rcases hC with hC | hC | hC
      · exact Or.inl (h4 G L hset hcb hZ2 hC)
      · exact Or.inr (Or.inl (h6 G L hset hcb hZ2 hC))
      · exact (h8 G L hset hcb hZ2 hC).elim
  · exact (h9 G L hset hc hD).elim

end CFSG.EvenSmallLie
