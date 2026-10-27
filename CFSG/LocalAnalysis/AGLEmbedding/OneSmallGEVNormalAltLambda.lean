module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltPCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVAltLambdaCore
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVAltBlockCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1SmallAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem le_zpowers_zbar (hc : D1SmallAltConfig p P M H R Rbar K z) (hΓ : KFactAltTwoPGamma)
    {Λ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hΛp : ∀ x ∈ Λ, ∃ k : ℕ, x ^ p ^ k = 1)
    (hΛC : Λ ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hΛn : ∀ g : ↥M, (g : G) * z = z * g → QuotientGroup.mk' (CFSG.pCore 2 ↥M) g ∈
      Subgroup.normalizer (Λ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    Λ ≤ Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩) :=
  hc.data.le_zpowers_zbar_of hc.elt hc.phase hc.cz_le
    (fun hNp hNX hNn _ => hc.le_zpowers_of_isPGroup hΓ hNp hNX hNn) hΛp hΛC hΛn

theorem orderOf_zbar (hc : D1SmallAltConfig p P M H R Rbar K z) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩) = p := by
  have : Fact p.Prime := ⟨hc.prime⟩
  refine orderOf_eq_prime hc.zbar_pow fun h1 => hc.data.cfg.red.ne_two ?_
  have h2 := coe_mem_pCoreOf_two_of_mk_eq_one _ h1
  have h3 := Subgroup.orderOf_dvd_natCard _ h2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
  rw [hk, hc.elt.2.1] at h3
  exact (Nat.prime_dvd_prime_iff_eq hc.prime Nat.prime_two).mp (hc.prime.dvd_of_dvd_pow h3)

theorem zbar_mem_block (hc : D1SmallAltConfig p P M H R Rbar K z) (hB : D1AltBlockInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈ barM M L :=
  hc.data.zbar_mem_block_of hc.elt hc.phase hc.cz_le
    (fun hΛp hΛC hΛn => hc.le_zpowers_zbar hB.hΓ hΛp hΛC hΛn) hL (hc.zbar_mem_sup hB hL)
    hc.orderOf_zbar (hc.zbar_not_mem_centralizer hL)

end D1SmallAltConfig

end CFSG.AGLEmbedding
