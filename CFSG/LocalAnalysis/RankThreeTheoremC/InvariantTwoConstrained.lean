module

public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoWithin
public import CFSG.Open.GLBDefs
import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityCentralizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem glbPrimeCore_le_pPrimeCoreIn (p : ℕ) (H : Subgroup G) :
    GLBPrimeCore p H ≤ CFSG.ABGTheoremB.pPrimeCoreIn p H := by
  refine sSup_le ?_
  rintro N ⟨hNH, hnormal, hcop⟩
  have hle : N.subgroupOf H ≤ CFSG.pPrimeCore p H :=
    le_sSup ⟨hnormal, by rwa [Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv]⟩
  rw [← map_subgroupOf_eq_of_le hNH]
  exact map_mono hle

@[expose] def GL83InvariantTwoWithinNonConstrained (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    ¬ (P : Subgroup G) ≤ normalizer (D : Set G) → IsMulCommutative D →
      ∀ z ∈ D, z ≠ 1 → z ∈ centralizer (P : Set G) → z ^ p = 1 →
        normalizer ((zpowers z : Subgroup G) : Set G) ≤ M → ¬ HasPrimeConstraint (G := M) p →
        ∀ T : Subgroup G, invariantTwoMaximalWithin D M T →
          T ≤ CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
            CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G))

theorem gl83InvariantTwoWithin_of_nonConstrained (hS : Setting G) (hD1 : TheoremD1 G)
    (h : GL83InvariantTwoWithinNonConstrained G) : GL83InvariantTwoWithin G := by
  intro p hp P M D hext hPD hab z hzD hz1 hzc hzp hN₀M T hT
  by_cases hcon : HasPrimeConstraint (G := M) p
  · have hprime := sigmaA_prime p hp
    have hodd := sigmaA_odd p hp
    have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hext.obstruction.1).1
    have hDP : D ≤ (P : Subgroup G) := hext.obstruction.2.1
    have hCD : centralizer (D : Set G) ≤ M :=
      (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
        ((centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT.2.1
    have hTcop : p.Coprime (Nat.card T) := by
      rw [hk]
      exact ((Nat.coprime_primes hprime Nat.prime_two).mpr hodd).pow_right k
    have hTO := CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains hprime hodd hcon
      (P.isPGroup'.to_le hDP) (hDP.trans hPM)
      (fun y _ hyC hyo => hext.mem_of_mem_centralizer_of_isMulCommutative hS hD1 hp hab hCD hyC
        (by rw [← hyo]; exact pow_orderOf_eq_one y))
      hT.1 hTcop hT.2.2.1
    exact hTO.trans ((glbPrimeCore_le_pPrimeCoreIn p M).trans le_sup_left)
  · exact h p hp P M D hext hPD hab z hzD hz1 hzc hzp hN₀M hcon T hT

end CFSG.LocalAnalysis.RankThreeTheoremC
