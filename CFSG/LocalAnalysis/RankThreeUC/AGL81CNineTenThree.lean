module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenStar
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem starImg_self (p : ℕ) (H : Subgroup G) : starImg p H H = ⊤ := by
  rw [starImg, Subgroup.subgroupOf_self]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem oPPrimeHull_map_kStar (hp : p.Prime) (hL : pLayerIn p H ≤ M) :
    oPPrimeHull p ((kStar p M H).map (QuotientGroup.mk' (CFSG.pCore p (StarGroup p H)))) =
      (kStar p M H).map (QuotientGroup.mk' (CFSG.pCore p (StarGroup p H))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let π : StarGroup p H →* StarGroup p H ⧸ CFSG.pCore p (StarGroup p H) :=
    QuotientGroup.mk' (CFSG.pCore p (StarGroup p H))
  change oPPrimeHull p ((kStar p M H).map π) = (kStar p M H).map π
  let N : Subgroup (StarGroup p H ⧸ CFSG.pCore p (StarGroup p H)) := (kStar p M H).map π
  have hN : N = closure (π '' {x : StarGroup p H | orderOf x = p}) := by
    change (kStar p M H).map π = closure (π '' {x : StarGroup p H | orderOf x = p})
    rw [kStar_eq_closure_of_le hp hL, MonoidHom.map_closure]
  change oPPrimeHull p N = N
  apply le_antisymm
  · rw [oPPrimeHull, Subgroup.closure_le]
    rintro x ⟨hx, -⟩
    exact hx
  · rw [hN, Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    rw [oPPrimeHull]
    refine Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨x, hx, rfl⟩, ?_⟩
    have hx' : orderOf x = p := hx
    have hdvd : orderOf (π x) ∣ p := by
      simpa [hx'] using orderOf_map_dvd π x
    rcases hp.eq_one_or_self_of_dvd (orderOf (π x)) hdvd with h1 | h1
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h1, pow_one]⟩

namespace NineSetting

theorem pRank_star_le_three (h : NineSetting G M p Q H E k) (hH2 : H ∈ H2Fam M Q)
    (hp : p ∉ sigmaM G M) : CFSG.Open.pRank p (⊤ : Subgroup (StarGroup p H)) ≤ 3 := by
  rw [← starImg_self p H, pRank_starImg_eq h.prime le_rfl]
  exact (h.pRank_le_of_mem_H2Fam hH2 hp).1

end NineSetting

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
