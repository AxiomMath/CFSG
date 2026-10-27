module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Plane
public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Config
public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Embeds
public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Sylow
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ExtremalObstruction.le_pPrimeCoreIn_of_isSylow (hS : Setting G) (hD1 : TheoremD1 G)
    (hK : Bal3KFacts) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hab : IsMulCommutative D) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G)) (hzp : z ^ p = 1)
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M)
    (hcon : ¬ HasPrimeConstraint (G := M) p)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set G))) {T : Subgroup G}
    (hT : invariantTwoMaximalWithin D M T) : T ≤ CFSG.ABGTheoremB.pPrimeCoreIn p M := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hM, hDP, -, hDM⟩ := hext.obstruction
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hDM' : D ≤ M := hDP.trans hPM
  have hzM : z ∈ M := hDM' hzD
  have hCD : centralizer (D : Set G) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)
  have := hS.simple
  have hMtop : M ≠ ⊤ := CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hM.1.1
  have hcat : CFSG.AGLEmbedding.CatalogSimpleSections M :=
    CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper M hMtop
  have hconf := Lemma212Config.of_extremal hS hp hext hPD hab hzD hz1 hzc hzp hSyl hPM hCD hzM
  obtain ⟨g, hg⟩ := hext.exists_isPlaneDiagonal hS hD1 hp hPD hab hCD hzD hz1 hzc hN₀M
  have hgM : g ∈ M := by
    obtain ⟨-, -, a, b, -, -, hga, -⟩ := hg
    exact hN₀M (mem_normalizer_zpowers_of_conj_mem (hga ▸ pow_mem (mem_zpowers z) a))
  have hg' := hg.subgroupOf hDM' hzM hgM
  have hemb := CentralizerEmbeds.of_extremal hS hD1 hp hext hPD hab hCD hzD hz1 hzc hN₀M hzM
  rcases hK.lemma212 p hprime hodd M hcat (P.subtype hPM) ⟨z, hzM⟩ (D.subgroupOf M) hconf
    ⟨_, hg'⟩ with hc | hpc
  · exact absurd hc hcon
  · rcases hK.lemma213 p hprime hodd M hcat hcon hpc (P.subtype hPM) ⟨z, hzM⟩
      (D.subgroupOf M) hconf ⟨_, hg'⟩ hemb with h1 | h2
    ·
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hTM : T ≤ M := hT.1
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT.2.1
      have hTcop : p.Coprime (Nat.card (T.subgroupOf M)) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv, hk]
        exact ((Nat.coprime_primes hprime Nat.prime_two).mpr hodd).pow_right k
      have hDT : D.subgroupOf M ≤ normalizer ((T.subgroupOf M : Subgroup M) : Set M) := by
        rw [← Subgroup.subgroupOf_normalizer_eq hTM]
        exact Subgroup.comap_mono hT.2.2.1
      have hTO := h1 (T.subgroupOf M) hTcop hDT
      have hTle : T ≤ CFSG.ABGTheoremB.pPrimeCoreIn p M := by
        have := Subgroup.map_mono (f := M.subtype) hTO
        rwa [map_subgroupOf_eq_of_le hTM] at this
      exact hTle
    ·
      exfalso
      obtain ⟨g₀, hg₀N, hg₀M⟩ := IsConcreteLE.not_le_iff_exists.mp hDM
      have hyD : g₀ * z * g₀⁻¹ ∈ D := (mem_normalizer_iff.mp hg₀N z).mp hzD
      have hyM : g₀ * z * g₀⁻¹ ∈ M := hDM' hyD
      have hy : (⟨g₀ * z * g₀⁻¹, hyM⟩ : M) ∈ D.subgroupOf M := hyD
      have hy1 : (⟨g₀ * z * g₀⁻¹, hyM⟩ : M) ≠ 1 := by
        intro h1
        have h2 : g₀ * z * g₀⁻¹ = 1 := congrArg Subtype.val h1
        exact hz1 (by simpa [mul_inv_eq_one] using h2)
      obtain ⟨h, -, hzp⟩ := h2 _ hy hy1
      have hzG : zpowers (g₀ * z * g₀⁻¹) = zpowers ((h : G) * z * (h : G)⁻¹) := by
        have := congrArg (Subgroup.map M.subtype) hzp
        rw [MonoidHom.map_zpowers, Subgroup.map_map, MonoidHom.map_zpowers] at this
        exact this
      have hmem : g₀ * z * g₀⁻¹ ∈ zpowers ((h : G) * z * (h : G)⁻¹) := by
        rw [← hzG]
        exact mem_zpowers _
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
      have hx : (h : G)⁻¹ * g₀ ∈ normalizer ((zpowers z : Subgroup G) : Set G) := by
        apply mem_normalizer_zpowers_of_conj_mem
        rw [mem_zpowers_iff]
        refine ⟨k, ?_⟩
        have e1 : ((h : G) * z * (h : G)⁻¹) ^ k = (h : G) * z ^ k * (h : G)⁻¹ := conj_zpow
        calc z ^ k = (h : G)⁻¹ * ((h : G) * z * (h : G)⁻¹) ^ k * (h : G) := by rw [e1]; group
          _ = (h : G)⁻¹ * (g₀ * z * g₀⁻¹) * (h : G) := by rw [hk]
          _ = ((h : G)⁻¹ * g₀) * z * ((h : G)⁻¹ * g₀)⁻¹ := by group
      apply hg₀M
      have := M.mul_mem h.2 (hN₀M hx)
      simpa using this

theorem ExtremalObstruction.le_pPrimeCoreIn_of_inf_le (hS : Setting G) (hD1 : TheoremD1 G)
    (hK : Bal3KFacts) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hab : IsMulCommutative D) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G)) (hzp : z ^ p = 1)
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M)
    (hcon : ¬ HasPrimeConstraint (G := M) p)
    (hCP : (P : Subgroup G) ⊓ centralizer (D : Set G) ≤ D) {T : Subgroup G}
    (hT : invariantTwoMaximalWithin D M T) : T ≤ CFSG.ABGTheoremB.pPrimeCoreIn p M := by
  have hCM : centralizer (D : Set G) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)
  exact hext.le_pPrimeCoreIn_of_isSylow hS hD1 hK hp hPD hab hzD hz1 hzc hzp hN₀M hcon
    ((hext.isSylowOf_centralizer_iff hS hD1 hp hPD hab hCM hzD hz1 hzc hN₀M).mpr hCP) hT

theorem bal3_of_residue (hS : Setting G) (hD1 : TheoremD1 G) (hK : Bal3KFacts)
    (h : Bal3Residue G) : Bal3 G := by
  intro p hp P M D hext hPD hab z hzD hz1 hzc hzp hN₀M hcon T hT hbal
  by_cases hCP : (P : Subgroup G) ⊓ centralizer (D : Set G) ≤ D
  · exact (hext.le_pPrimeCoreIn_of_inf_le hS hD1 hK hp hPD hab hzD hz1 hzc hzp hN₀M hcon hCP
      hT).trans le_sup_left
  · exact h p hp P M D hext hPD hab z hzD hz1 hzc hzp hN₀M hcon hCP T hT hbal

end CFSG.LocalAnalysis.RankThreeTheoremC
