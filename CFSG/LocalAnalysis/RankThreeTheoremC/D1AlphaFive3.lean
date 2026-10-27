module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ComponentCases3
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (isPGroup_center_of_isComponentOf)

theorem pRank_top_le_pRank_sylow_of_normal {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (R : Sylow p X) {N : Subgroup X} (hN : N.Normal) :
    Open.pRank p (⊤ : Subgroup N) ≤ Open.pRank p (R : Subgroup X) := by
  have hp : p.Prime := Fact.out
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R hN.isSubnormal
  rw [← pRank_sylow_eq_globalRank p hp T, ← pRank_map_of_injective p hp N.subtype
    N.subtype_injective, hT]
  exact pRank_mono p hp inf_le_left

variable {G : Type} [Group G] [Finite G]

theorem D1ComponentData3.pRank_pbar_eq {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {K : Subgroup (ReducedCentralizer p z)}
    (h : D1ComponentData3 p P M H R z Pbar zbar K) :
    Open.pRank p (Pbar : Subgroup (ReducedCentralizer p z)) = 3 := by
  have hp : p.Prime := Fact.out
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp h.input.mem_centralizer x hx)
  rw [h.pbar, CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype hp _
    (primeComplementCore_coprime p), Subgroup.map_subgroupOf_eq_of_le hPC]
  exact h.input.pRank_eq

theorem D1ComponentData3.pRank_normal_le {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {K : Subgroup (ReducedCentralizer p z)}
    (h : D1ComponentData3 p P M H R z Pbar zbar K) :
    Open.pRank p (⊤ : Subgroup K) ≤ 3 :=
  (pRank_top_le_pRank_sylow_of_normal Pbar h.normal).trans h.pRank_pbar_eq.le

theorem D1ComponentAlphaData3.false_of_five_le {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {K : Subgroup (ReducedCentralizer p z)}
    (h : D1ComponentAlphaData3 p P M H R z Pbar zbar K) (hKF1 : KF1At G)
    (hp5 : 5 ≤ p) : False := by
  have hp : p.Prime := Fact.out
  have hpg : IsPGroup p (Subgroup.center K) :=
    isPGroup_center_of_isComponentOf hp h.data.red.core_eq_bot h.data.comp
  have hcenter : p ∣ Nat.card (Subgroup.center K) :=
    hpg.card_eq_or_dvd.resolve_left fun h1 => h.center_ne_bot (Subgroup.card_eq_one.mp h1)
  have hz1 : z ≠ 1 := by
    intro h1
    have hord := h.data.input.orderOf_eq
    rw [h1, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hC : Subgroup.centralizer ({z} : Set G) ≠ ⊤ := fun htop =>
    h.data.glob.normalizer_zpowers_ne_top hz1
      (eq_top_iff.2 (htop ▸ centralizer_singleton_le_normalizer_zpowers z))
  have h4 := hKF1 p hp hp5 (Subgroup.centralizer ({z} : Set G)) hC (primeComplementCore p) K
    h.data.comp.2.2 (h.data.catalog.isCatalogGroup_center_quotient h.data.comp) hpg hcenter
  have h3 := h.data.pRank_normal_le
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
