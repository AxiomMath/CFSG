module

public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.Centralizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
import CFSG.LocalAnalysis.AGLEmbedding.Signalizer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.gl83InvariantTwoSylow_of_within (hS : ObstructionSetting G)
    (hR : TransitivityReduction G) (h : GL83InvariantTwoWithin G) : GL83InvariantTwoSylow G := by
  intro p hp P M D hext hPD hab z hzD hz1 hzc hzp T hT
  have hprime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hN₀M := hR p hp P M D hext hPD z hzD hz1 hzc hzp
  have hTX := h p hp P M D hext hPD hab z hzD hz1 hzc hzp hN₀M T hT
  have hDP : D ≤ (P : Subgroup G) := hext.obstruction.2.1
  have hPM : (P : Subgroup G) ≤ M := hS.sylow_le hp hext.obstruction.1
  have hDN₀ : D ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    refine le_centralizer_iff.mp (zpowers_le.mpr (mem_centralizer_iff.mpr fun d hd => ?_))
    exact congrArg Subtype.val (hab.is_comm.comm ⟨d, hd⟩ ⟨z, hzD⟩)
  have hXM : CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔ CFSG.ABGTheoremB.pPrimeCoreIn p
      (normalizer ((zpowers z : Subgroup G) : Set G)) ≤ M :=
    sup_le (CFSG.ABGTheoremB.pPrimeCoreIn_le p M)
      ((CFSG.ABGTheoremB.pPrimeCoreIn_le p _).trans hN₀M)
  exact isSylowOf_of_invariantTwoMaximalWithin hprime (P.isPGroup'.to_le hDP) hXM
    (coprime_card_pPrimeCoreIn_sup hN₀M)
    (le_normalizer_pPrimeCoreIn_sup (hDP.trans hPM) hDN₀) hT hTX

theorem ObstructionSetting.gl83InvariantTwoWithin_of_nonConstrained (hS : ObstructionSetting G)
    (hD1 : TheoremD1 G) (h : GL83InvariantTwoWithinNonConstrained G) :
    GL83InvariantTwoWithin G := by
  intro p hp P M D hext hPD hab z hzD hz1 hzc hzp hN₀M T hT
  by_cases hcon : HasPrimeConstraint (G := M) p
  · have hprime := sigmaA_prime p hp
    have hodd := sigmaA_odd p hp
    have hPM : (P : Subgroup G) ≤ M := hS.sylow_le hp hext.obstruction.1
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
      (fun y _ hyC hyo => hS.mem_of_mem_centralizer_of_isMulCommutative hD1 hp hext hab hCD hyC
        (by rw [← hyo]; exact pow_orderOf_eq_one y))
      hT.1 hTcop hT.2.2.1
    exact hTO.trans ((glbPrimeCore_le_pPrimeCoreIn p M).trans le_sup_left)
  · exact h p hp P M D hext hPD hab z hzD hz1 hzc hzp hN₀M hcon T hT

end CFSG.LocalAnalysis.RankFourTheoremC
