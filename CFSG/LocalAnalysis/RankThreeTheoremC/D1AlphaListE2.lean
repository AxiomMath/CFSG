module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ComponentCases3
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (CatalogSimpleSections catalogSimpleSections_of_isKProper)

variable {G : Type} [Group G] [Finite G]

theorem cfsgIsKGroup_of_catalogSimpleSections {X : Type} [Group X] [Finite X]
    (hX : CatalogSimpleSections X) : CFSG.IsKGroup X :=
  CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
    CFSG.Assembly.inCatalog_containsAbelianSimple
    (CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp hX)

theorem rankThreeLocalRank_lt_three_of_three_mem_sigmaA (hrank : evenRank G = 3)
    (h3 : 3 ∈ rankThreeSigmaA G) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) :
    rankThreeLocalRank q G < 3 := by
  classical
  by_contra hlt
  push Not at hlt
  have hupper := rankThreeLocalRank_le_evenRank (G := G) q hq (by omega)
  have hupper3 := rankThreeLocalRank_le_evenRank (G := G) 3 Nat.prime_three (by norm_num)
  have hq_eq : rankThreeLocalRank q G = 3 := by omega
  obtain ⟨H, -, hHrank⟩ := rankThreeLocalRank_attained (G := G) q (by omega)
  have hqdvd : q ∣ Nat.card G := prime_dvd_card_of_pRank_pos q H (by omega)
  have hS3 : ({p : ℕ | p.Prime ∧ 3 < p ∧ p ∣ Nat.card G ∧ rankThreeLocalRank p G = 3}).Nonempty :=
    ⟨q, hq, hq3, hqdvd, hq_eq⟩
  dsimp only [rankThreeSigmaA] at h3
  split_ifs at h3
  · exact absurd h3.2.2.2 (by omega)
  · exact absurd h3.2.1 (by norm_num)
  · exact absurd h3.2.1 (by norm_num)

theorem sectionFourHyp_centralizer (hS : Setting G) (h3 : 3 ∈ rankThreeSigmaA G) {z : G}
    (hz1 : z ≠ 1) :
    CFSG.RankThree.PartTwo.SectionFourHyp (Subgroup.centralizer ({z} : Set G)) := by
  have hC : Subgroup.centralizer ({z} : Set G) ≠ ⊤ := fun htop =>
    hS.normalizer_zpowers_ne_top hz1
      (eq_top_iff.2 (htop ▸ centralizer_singleton_le_normalizer_zpowers z))
  refine ⟨cfsgIsKGroup_of_catalogSimpleSections
    (catalogSimpleSections_of_isKProper hS.kProper _ hC), ?_, fun q hq hq3 => ?_⟩
  · exact (CFSG.RankThree.PartTwo.evenRank_subgroup_le (Subgroup.centralizer ({z} : Set G))).trans
      (le_of_eq hS.rank)
  · exact (CFSG.RankThree.PartTwo.localRank_subgroup_le hq _).trans_lt
      (rankThreeLocalRank_lt_three_of_three_mem_sigmaA hS.rank h3 hq hq3)

theorem D1ComponentData3.isKGroup_twoLocalOddRank_le {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {K : Subgroup (ReducedCentralizer p z)}
    (h : D1ComponentData3 p P M H R z Pbar zbar K) (hp3 : p = 3) :
    CFSG.IsKGroup ↥K ∧ CFSG.twoLocalOddRank ↥K ≤ 3 := by
  subst hp3
  have hp : (3 : ℕ).Prime := Fact.out
  have hz1 : z ≠ 1 := by
    intro h1
    have hord := h.input.orderOf_eq
    rw [h1, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hC := sectionFourHyp_centralizer h.glob h.loc.sigma hz1
  refine ⟨cfsgIsKGroup_of_catalogSimpleSections (h.catalog.subgroup K), ?_⟩
  set O := primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3
  let f : (⊤ : Subgroup (Subgroup.centralizer ({z} : Set G))) →* ReducedCentralizer 3 z :=
    (QuotientGroup.mk' O).comp (⊤ : Subgroup (Subgroup.centralizer ({z} : Set G))).subtype
  have hf : Function.Surjective f := fun y => by
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨c, Subgroup.mem_top c⟩, rfl⟩
  have hker : ¬ 3 ∣ Nat.card f.ker := by
    let g : f.ker →* O :=
      ((⊤ : Subgroup (Subgroup.centralizer ({z} : Set G))).subtype.comp f.ker.subtype).codRestrict
        O fun x => (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp x.2)
    have hg : Function.Injective g := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    have hdvd : Nat.card f.ker ∣ Nat.card O := Subgroup.card_dvd_of_injective g hg
    intro h3
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (primeComplementCore_coprime 3) (h3.trans hdvd)
  have hev : CFSG.Assembly.evenRank (ReducedCentralizer 3 z) ≤ 3 :=
    CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le fun r hr hr2 =>
      CFSG.RankThree.PartTwo.Sec4.Item434Spor.localRank_le_three_of_section hC ⊤ f hf hker hr hr2
  rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
  exact (CFSG.RankThree.PartTwo.evenRank_subgroup_le K).trans hev

end CFSG.LocalAnalysis.RankThreeTheoremC
