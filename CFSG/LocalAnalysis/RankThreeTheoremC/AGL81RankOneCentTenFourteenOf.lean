module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeX
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNineTwoOne
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteenCenter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

structure TenFourteenCentRestAt (p : ℕ) (M C : Subgroup G) : Prop where
  factor : d1KBar p M C ≠ ⊥ → ∀ x ∈ C, ∃ m ∈ C ⊓ M, ∃ k : C,
    QuotientGroup.mk' _ k ∈ d1KBar p M C ∧ x = m * k
  list : d1KBar p M C ≠ ⊥ → TenFourteenOneGroup p ↥(d1KBar p M C)

variable (G) in
@[expose] def AGL81TenFourteenCentRestCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ a : G, a ∈ M → orderOf a = p →
    ¬ Subgroup.centralizer ({a} : Set G) ≤ M →
    (∃ U : Subgroup G, U ≤ Subgroup.centralizer ({a} : Set G) ∧ IsAGLQ p M U) →
    TenFourteenCentRestAt p M (Subgroup.centralizer ({a} : Set G))

theorem centralizer_ne_top_of_setting (hS : Setting G) {a : G} (ha : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) ≠ ⊤ := by
  intro htop
  haveI := hS.simple
  rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with hZ | hZ
  · refine ha ((Subgroup.mem_bot).mp (hZ ▸ Subgroup.mem_center_iff.mpr fun g => ?_))
    exact (Subgroup.mem_centralizer_iff.mp (htop ▸ Subgroup.mem_top g) a
      (Set.mem_singleton a)).symm
  · obtain ⟨x, y, hxy⟩ := hS.nonab
    exact hxy (Subgroup.mem_center_iff.mp (hZ ▸ Subgroup.mem_top y) x)

theorem agl81TenFourteenCentCfg_of
    (h74 : AGL81SevenFourTwo) (hOut : KFactOutCyclic)
    (h : AGL81TenFourteenCentRestCfg G) : AGL81TenFourteenCentCfg G := by
  intro hS p P M H Q K hd a haM hao hC hU
  have hR := h hS p P M H Q K hd a haM hao hC hU
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  obtain ⟨U, hUC, hUQ⟩ := hU
  have ha : a ≠ 1 := fun ha1 => hesc.prime.one_lt.ne' (hao ▸ ha1 ▸ orderOf_one)
  exact
    { core_le := core_le_of_base ⟨hd.escape⟩ hUQ hUC
      cyclic := fun hK _ hB hB3 => isCyclic_center_of_d1KBar_eq_bot h74 hOut hS.kProper hesc hUQ
        hUC hC (centralizer_ne_top_of_setting hS ha) hK hB hB3
      nineThree := fun hK =>
        { normal := d1KBar_normal_of_escape hesc hUQ hUC hK
          plusCore_le := d1PlusCore_le_of_escape hesc hUQ hUC hK
          factor := hR.factor hK }
      rank := fun hK => pRank_d1PlusCore_le_one_of_escape hesc hUQ hUC hK
      center := fun hK => center_d1KBar_eq_bot_of_tenFourteenOneGroup hK (hR.list hK)
      list := hR.list }

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
