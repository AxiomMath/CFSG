module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Cor47
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Core

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0)

variable {G : Type} [Group G] [Finite G]

theorem prop31_rank_le_one (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G) {p : ℕ}
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) (hp : p ∈ rankThreeSigmaA G) {u : G}
    (hgen : IsGenericPoint p P M u) {J : Subgroup G}
    (hJC : J ≤ Subgroup.centralizer ({u} : Set G))
    (hCJ : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G)) (hJM : ¬ J ≤ M)
    {R : Subgroup G} (hRP : R ≤ (P : Subgroup G)) (hRC : R ≤ Subgroup.centralizer ({u} : Set G))
    (hcomm : ∀ r ∈ R, ∀ j ∈ J, r * j * r⁻¹ * j⁻¹ ∈ rankThreePrimeCore p J) :
    ¬ 2 ≤ CFSG.Open.pRank p R := by
  intro h2
  haveI : Fact (Nat.Prime p) := ⟨sigmaA_prime p hp⟩
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hRp : IsPGroup p R := P.isPGroup'.to_le hRP
  have hNR : Subgroup.normalizer (R : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hRp (hRP.trans hPM) h2
  have hOM : rankThreePrimeCore p J ≤ M := (u3main_core_facts hS hD1 hp hM hgen hJC hCJ).1
  have hOJ : rankThreePrimeCore p J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hcop : p.Coprime (Nat.card (rankThreePrimeCore p J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hJN : J ≤ Subgroup.normalizer ((rankThreePrimeCore p J : Subgroup G) : Set G) :=
    (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p J).2.1
  have hRN : R ≤ Subgroup.normalizer ((rankThreePrimeCore p J : Subgroup G) : Set G) :=
    hRC.trans (hCJ.trans (sps_normalizer_core J))
  exact hJM (sps_frattini hOJ hJN hRN hcop hRp hcomm hOM hNR)

theorem point_prop31_ii (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
    {J : Subgroup G} (hc : PointConfig Typ G p P M x J) :
    IsCyclic ↥(u3S P x ⊓ u3K0 p x J) ∧
      ∀ k ∈ u3K0 p x J, Nat.Coprime p (orderOf k) →
        k ∈ CFSG.ABGTheoremB.pPrimeCoreIn p (Subgroup.centralizer ({x} : Set G)) := by
  have hp : p.Prime := hc.prime
  have hp2 : p ≠ 2 := by have := hc.five; omega
  have hDP : u3S P x ⊓ u3K0 p x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hDC : u3S P x ⊓ u3K0 p x J ≤ Subgroup.centralizer ({x} : Set G) :=
    inf_le_left.trans inf_le_right
  have hDp : IsPGroup p ↥(u3S P x ⊓ u3K0 p x J) := P.isPGroup'.to_le hDP
  have hcyc : IsCyclic ↥(u3S P x ⊓ u3K0 p x J) := by
    by_contra hnc
    have h2 := two_le_pRank_of_not_isCyclic hp hp2 hDp hnc
    exact prop31_rank_le_one hS hU0 hD1 hc.core hc.sigma hc.generic hc.le_cent hc.cent_le hc.not_le
      hDP hDC (fun r hr j hj => hr.2.2.2 j hj) h2
  exact ⟨hcyc, CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.k0_coprime_mem_pPrimeCoreIn hcyc hc⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
