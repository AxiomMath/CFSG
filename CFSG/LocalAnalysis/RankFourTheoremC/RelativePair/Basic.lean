module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.Setting
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.Plane
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.Self
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem KFactSetting.normalizer_zpowers_ne_top {n : ℕ} (hS : KFactSetting n G) {z : G}
    (hz1 : z ≠ 1) : normalizer ((zpowers z : Subgroup G) : Set G) ≠ ⊤ := by
  intro htop
  have hn : (zpowers z).Normal := normalizer_eq_top_iff.1 htop
  have := hS.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers z) with h | h
  · exact hz1 (zpowers_eq_bot.1 h)
  · obtain ⟨a, b, hab⟩ := hS.nonab
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 (h ▸ mem_top a)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 (h ▸ mem_top b)
    exact hab ((Commute.zpow_zpow_self z i j).eq)

theorem ObstructionSetting.isSylowOf_centralizer (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hDab : IsMulCommutative D) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) :
    CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set G)) :=
  (hS.isSylowOf_centralizer_iff hD1 hp hext hPD hDab
    ((centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)) hzD hz1 hzc hN₀M).mpr
    (hS.inf_centralizer_le_self hD1 hp hext hPD hDab hzD hz1 hzc hN₀M)

theorem KFactSetting.isPConstrained_normalizer_zpowers {n : ℕ} (hS : KFactSetting n G)
    (hD1 : TheoremD1 G) (hK : KFactLemma212Ge n) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
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
  have hconf := Lemma212ConfigGe.of_extremal hS.obstruction hp hext (hS.le_pRank p hp P) hPD hDab
    hzD hz1 hzc hzp hSyl hPN₀ hCN₀ hzN₀
  obtain ⟨g, hg⟩ := hS.obstruction.exists_isPlaneDiagonal hD1 hp hext hPD hDab hCM hzD hz1 hzc
    hN₀M
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

theorem KFactSetting.isPConstrained_normalizer_zpowers_of_transitivity {n : ℕ}
    (hS : KFactSetting n G) (hD1 : TheoremD1 G) (hK : KFactLemma212Ge n) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hDab : IsMulCommutative D) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G)) (hzp : z ^ p = 1)
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) :
    CFSG.ABGLocalTools.IsPConstrained p (normalizer ((zpowers z : Subgroup G) : Set G)) :=
  hS.isPConstrained_normalizer_zpowers hD1 hK hp hext hPD hDab hzD hz1 hzc hzp hN₀M
    (hS.obstruction.isSylowOf_centralizer hD1 hp hext hPD hDab hzD hz1 hzc hN₀M)

end CFSG.LocalAnalysis.RankFourTheoremC
