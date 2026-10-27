module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.SectionRank

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem pRank_sylow [hp : Fact p.Prime] (P : Sylow p G) :
    Open.pRank p (P : Subgroup G) = Open.pRank p (⊤ : Subgroup G) ∧
      CFSG.pRank p (P : Subgroup G) = CFSG.pRank p G := by
  have hp1 := hp.out.one_lt
  have h : Open.pRank p (P : Subgroup G) = Open.pRank p (⊤ : Subgroup G) := by
    refine le_antisymm (pRank_mono hp1 le_top) ?_
    obtain ⟨E, -, hE, hcard⟩ := exists_pRank hp1 (⊤ : Subgroup G)
    obtain ⟨Q, hEQ⟩ := (IsPGroup.of_card hcard).exists_le_sylow
    calc Open.pRank p (⊤ : Subgroup G) ≤ Open.pRank p (Q : Subgroup G) :=
          le_pRank hp1 hEQ hE hcard
      _ = Open.pRank p (⊤ : Subgroup (Q : Subgroup G)) := pRank_eq_pRank_top_subgroup _
      _ = Open.pRank p (⊤ : Subgroup (P : Subgroup G)) :=
          pRank_top_eq_of_mulEquiv hp1 (Q.equiv P)
      _ = Open.pRank p (P : Subgroup G) := (pRank_eq_pRank_top_subgroup _).symm
  refine ⟨h, ?_⟩
  rw [pRank_eq_open_pRank_top, pRank_eq_open_pRank_top, ← pRank_eq_pRank_top_subgroup, h]

end CFSG.SectionRank
