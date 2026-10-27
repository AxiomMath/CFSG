module

public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalance
import CFSG.LocalAnalysis.RankThreeTheoremC.HasPrimeConstraintBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityRank
import CFSG.LocalAnalysis.AGLEmbedding.Signalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem signalizer_le_glbPrimeCore_normalizer_zpowers_of_isPConstrained (hS : Setting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hDab : IsMulCommutative D) {z : G}
    (hzD : z ∈ D) (hzc : z ∈ centralizer (P : Set G))
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M)
    (hcon : CFSG.ABGLocalTools.IsPConstrained p (normalizer ((zpowers z : Subgroup G) : Set G)))
    {Y : Subgroup G}
    (hYN : Y ≤ normalizer ((zpowers z : Subgroup G) : Set G)) (hY : p.Coprime (Nat.card Y))
    (hDY : D ≤ normalizer (Y : Set G)) :
    Y ≤ GLBPrimeCore p (normalizer ((zpowers z : Subgroup G) : Set G)) := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hDP : D ≤ (P : Subgroup G) := hext.obstruction.2.1
  have hPN₀ : (P : Subgroup G) ≤ normalizer ((zpowers z : Subgroup G) : Set G) :=
    le_normalizer_zpowers_of_le_centralizer hzc
  have hCD : centralizer (D : Set G) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)
  exact CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains hprime hodd
    (hasPrimeConstraint_of_isPConstrained hcon) (P.isPGroup'.to_le hDP) (hDP.trans hPN₀)
    (fun y _ hyC hyo => hext.mem_of_mem_centralizer_of_isMulCommutative hS hD1 hp hDab hCD hyC
      (by rw [← hyo]; exact pow_orderOf_eq_one y)) hYN hY hDY

theorem inf_centralizer_le_glbPrimeCore_of_isPConstrained (hS : Setting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D) {z : G}
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hzc : z ∈ centralizer (P : Set G))
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M)
    (hcon : CFSG.ABGLocalTools.IsPConstrained p (normalizer ((zpowers z : Subgroup G) : Set G)))
    {T : Subgroup G} (hT : p.Coprime (Nat.card T)) (hDT : D ≤ normalizer (T : Set G)) {d : G}
    (hdD : d ∈ D) (hd1 : d ≠ 1) :
    T ⊓ centralizer ({d} : Set G) ≤
      GLBPrimeCore p (normalizer ((zpowers d : Subgroup G) : Set G)) := by
  have hCD : centralizer (D : Set G) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)
  obtain ⟨g, hgD, hgz⟩ := hext.exists_mem_normalizer_zpowers_eq hS hD1 hp hPD hDab hCD hzD hz1
    hzc hN₀M hdD hd1
  have hNd : normalizer ((zpowers d : Subgroup G) : Set G) =
      (normalizer ((zpowers z : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [hgz, Subgroup.map_equiv_normalizer_eq]
  have hdC : D ≤ centralizer ({d} : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr hDab).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hdD))
  rw [hNd]
  refine signalizer_le_glbPrimeCore_map_conj hgD (fun Y hYN hY hDY =>
    signalizer_le_glbPrimeCore_normalizer_zpowers_of_isPConstrained hS hD1 hp hext hDab hzD hzc
      hN₀M hcon hYN hY hDY) ?_ (hT.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left))
    (le_trans (le_inf hDT (hdC.trans le_normalizer)) inf_normalizer_le_normalizer_inf)
  rw [← hNd]
  exact inf_le_right.trans (centralizer_singleton_le_normalizer_zpowers d)

theorem inf_centralizer_le_pPrimeCoreIn_of_isPConstrained (hS : Setting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D) {z : G}
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hzc : z ∈ centralizer (P : Set G))
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M)
    (hcon : CFSG.ABGLocalTools.IsPConstrained p (normalizer ((zpowers z : Subgroup G) : Set G)))
    {T : Subgroup G} (hT : invariantTwoMaximalWithin D M T) {d : G} (hdD : d ∈ D) (hd1 : d ≠ 1) :
    T ⊓ centralizer ({d} : Set G) ≤
      CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers d : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT.2.1
  have hTcop : p.Coprime (Nat.card T) := by
    rw [hk]
    exact ((Nat.coprime_primes (sigmaA_prime p hp) Nat.prime_two).mpr (sigmaA_odd p hp)).pow_right k
  exact (inf_centralizer_le_glbPrimeCore_of_isPConstrained hS hD1 hp hext hPD hDab hzD hz1 hzc
    hN₀M hcon hTcop hT.2.2.1 hdD hd1).trans (glbPrimeCore_le_pPrimeCoreIn p _)

@[expose] def Bal3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    ¬ (P : Subgroup G) ≤ normalizer (D : Set G) → IsMulCommutative D →
      ∀ z ∈ D, z ≠ 1 → z ∈ centralizer (P : Set G) → z ^ p = 1 →
        normalizer ((zpowers z : Subgroup G) : Set G) ≤ M → ¬ HasPrimeConstraint (G := M) p →
        ∀ T : Subgroup G, invariantTwoMaximalWithin D M T →
          ((5 ≤ p ∨ CFSG.ABGLocalTools.IsPConstrained p
              (normalizer ((zpowers z : Subgroup G) : Set G))) →
            ∀ d ∈ D, d ≠ 1 → T ⊓ centralizer ({d} : Set G) ≤
              CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers d : Subgroup G) : Set G))) →
          T ≤ CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
            CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G))

theorem bal_of_bal3 (hS : Setting G) (hD1 : TheoremD1 G) (h : Bal3 G) :
    GL83InvariantTwoWithinNonConstrainedBal G := by
  intro p hp P M D hext hPD hab z hzD hz1 hzc hzp hN₀M hcon T hT hbal5
  refine h p hp P M D hext hPD hab z hzD hz1 hzc hzp hN₀M hcon T hT ?_
  rintro (h5 | hpc)
  · exact hbal5 h5
  · intro d hd hd1
    exact inf_centralizer_le_pPrimeCoreIn_of_isPConstrained hS hD1 hp hext hPD hab hzD hz1 hzc
      hN₀M hpc hT hd hd1

end CFSG.LocalAnalysis.RankThreeTheoremC
