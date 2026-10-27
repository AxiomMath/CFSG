module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Config
public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Plane
public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Sylow
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ExtremalObstruction.isPConstrained_normalizer_zpowers (hS : Setting G)
    (hD1 : TheoremD1 G) (hK : KFactLemma212) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D) {z : G}
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hzp : z ^ p = 1) (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set G))) :
    CFSG.ABGLocalTools.IsPConstrained p (normalizer ((zpowers z : Subgroup G) : Set G)) := by
  classical
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hDP : D ≤ (P : Subgroup G) := hext.obstruction.2.1
  have hPN₀ : (P : Subgroup G) ≤ normalizer ((zpowers z : Subgroup G) : Set G) :=
    le_normalizer_zpowers_of_le_centralizer hzc
  have hCN₀ : centralizer (D : Set G) ≤ normalizer ((zpowers z : Subgroup G) : Set G) :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      (centralizer_singleton_le_normalizer_zpowers z)
  have hCM : centralizer (D : Set G) ≤ M := hCN₀.trans hN₀M
  have hzN₀ : z ∈ normalizer ((zpowers z : Subgroup G) : Set G) := le_normalizer (mem_zpowers z)
  have hcat : CFSG.AGLEmbedding.CatalogSimpleSections
      (normalizer ((zpowers z : Subgroup G) : Set G)) :=
    CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper _
      (hS.normalizer_zpowers_ne_top hz1)
  have hconf := Lemma212Config.of_extremal hS hp hext hPD hDab hzD hz1 hzc hzp hSyl hPN₀ hCN₀ hzN₀
  obtain ⟨g, hg⟩ := hext.exists_isPlaneDiagonal hS hD1 hp hPD hDab hCM hzD hz1 hzc hN₀M
  have hgN₀ : g ∈ normalizer ((zpowers z : Subgroup G) : Set G) := by
    obtain ⟨-, -, a, b, -, -, hga, -⟩ := hg
    exact mem_normalizer_zpowers_of_conj_mem (hga ▸ pow_mem (mem_zpowers z) a)
  have hg' := hg.subgroupOf (hDP.trans hPN₀) hzN₀ hgN₀
  rcases hK p hprime hodd _ hcat (P.subtype hPN₀) ⟨z, hzN₀⟩ (D.subgroupOf _) hconf ⟨_, hg'⟩
    with hc | hpc
  · exact isPConstrained_of_hasPrimeConstraint hc
  · exfalso
    set N₀ := normalizer ((zpowers z : Subgroup G) : Set G) with hN₀def
    set O : Subgroup N₀ := primeComplementCore (G := N₀) p with hOdef
    set π : N₀ →* N₀ ⧸ O := QuotientGroup.mk' O with hπ
    set zz : N₀ := ⟨z, hzN₀⟩ with hzzdef
    have hzzp : zz ^ p = 1 := Subtype.ext hzp
    have hzzord : orderOf zz = p := by
      rw [hzzdef, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hzp hz1
    have hz1' : π zz ≠ 1 := by
      intro h
      have hzO : zz ∈ O := (QuotientGroup.eq_one_iff zz).mp h
      have hdvd : p ∣ Nat.card O := hzzord ▸ Subgroup.orderOf_dvd_natCard O hzO
      have hcop := primeComplementCore_coprime (G := N₀) p
      exact hprime.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd)
    have hzn : (zpowers zz).Normal := normal_zpowers_subtype_mk z hzN₀
    have hnorm : (zpowers (π zz)).Normal := by
      rw [← MonoidHom.map_zpowers]
      exact hzn.map π (QuotientGroup.mk'_surjective O)
    have hpgrp : IsPGroup p (zpowers (π zz)) := by
      have hpow : (π zz) ^ p = 1 := by rw [← map_pow, hzzp, map_one]
      have hdvd : orderOf (π zz) ∣ p := orderOf_dvd_of_pow_eq_one hpow
      rcases (Nat.dvd_prime hprime).mp hdvd with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
    have hle : zpowers (π zz) ≤ CFSG.pCore p (N₀ ⧸ O) := le_sSup ⟨hnorm, hpgrp⟩
    rw [hpc, le_bot_iff, zpowers_eq_bot] at hle
    exact hz1' hle

theorem ExtremalObstruction.isPConstrained_normalizer_zpowers_of_inf_le (hS : Setting G)
    (hD1 : TheoremD1 G) (hK : KFactLemma212) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D) {z : G}
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hzp : z ^ p = 1) (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M)
    (hCP : (P : Subgroup G) ⊓ centralizer (D : Set G) ≤ D) :
    CFSG.ABGLocalTools.IsPConstrained p (normalizer ((zpowers z : Subgroup G) : Set G)) := by
  have hCM : centralizer (D : Set G) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)
  exact hext.isPConstrained_normalizer_zpowers hS hD1 hK hp hPD hDab hzD hz1 hzc hzp hN₀M
    ((hext.isSylowOf_centralizer_iff hS hD1 hp hPD hDab hCM hzD hz1 hzc hN₀M).mpr hCP)

end CFSG.LocalAnalysis.RankThreeTheoremC
