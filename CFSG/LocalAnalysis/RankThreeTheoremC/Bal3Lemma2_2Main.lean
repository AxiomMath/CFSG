module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_2Self
public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1CaseA

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ExtremalObstruction.isSylowOf_centralizer (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hDab : IsMulCommutative D) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) :
    CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set G)) :=
  (hext.isSylowOf_centralizer_iff hS hD1 hp hPD hDab
    ((centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)) hzD hz1 hzc hN₀M).mpr
    (hext.inf_centralizer_le_self hS hD1 hp hPD hDab hzD hz1 hzc hN₀M)

theorem bal3Residue_of_setting (hS : Setting G) (hD1 : TheoremD1 G) : Bal3Residue G :=
  fun _ hp _ _ _ hext hPD hab _ hzD hz1 hzc _ hN₀M _ hCP _ _ _ =>
    absurd (hext.inf_centralizer_le_self hS hD1 hp hPD hab hzD hz1 hzc hN₀M) hCP

theorem bal3_of_kfacts (hS : Setting G) (hD1 : TheoremD1 G) (hK : Bal3KFacts) : Bal3 G :=
  bal3_of_residue hS hD1 hK (bal3Residue_of_setting hS hD1)

theorem ExtremalObstruction.isPConstrained_normalizer_zpowers_of_kfact (hS : Setting G)
    (hD1 : TheoremD1 G) (hK : KFactLemma212) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D) {z : G}
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hzp : z ^ p = 1) (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) :
    CFSG.ABGLocalTools.IsPConstrained p (normalizer ((zpowers z : Subgroup G) : Set G)) :=
  hext.isPConstrained_normalizer_zpowers_of_inf_le hS hD1 hK hp hPD hDab hzD hz1 hzc hzp hN₀M
    (hext.inf_centralizer_le_self hS hD1 hp hPD hDab hzD hz1 hzc hN₀M)

end CFSG.LocalAnalysis.RankThreeTheoremC
