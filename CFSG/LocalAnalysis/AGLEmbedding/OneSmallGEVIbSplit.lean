module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVOuterSup
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVZCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem rPart_inv (hc : D1IbConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {X : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hX : Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (X : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∀ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z →
      (∀ t ∈ d1LiftX p H R K, n * t * n⁻¹ ∈ d1LiftX p H R K) →
        ∀ b ∈ rPart M R X, n * b * n⁻¹ ∈ rPart M R X :=
  rPart_inv_of hc.phase.le_M hc.phase.normalizer_le hc.mem_M
    (hc.mem_normalizer_of_commute hL) hX

theorem sizes_of_invSubset (hc : D1IbConfig p P M H R Rbar K z) (hOrb : KFactSmallOrbits)
    {S : Set G} (hS : D1InvSubset p H R K z S) :
    S.ncard = 0 ∨ S.ncard = p ^ 2 - 1 ∨ 2 * S.ncard = p ^ 2 - 1 ∨ S.ncard = 2 * (p - 1) ∨
      S.ncard = (p - 1) ^ 2 :=
  hc.toZCore.sizes_of_invSubset hOrb hS

theorem invSubset_ncard_ne (hc : D1IbConfig p P M H R Rbar K z) (hOrb : KFactSmallOrbits)
    {S : Set G} (hS : D1InvSubset p H R K z S) : S.ncard ≠ 1 ∧ S.ncard ≠ p - 1 :=
  D1SmallAltConfig.ne_one_and_ne_of_sizes hc.five_le (hc.sizes_of_invSubset hOrb hS)

theorem inv_subgroup (hc : D1IbConfig p P M H R Rbar K z) (hOrb : KFactSmallOrbits)
    {B : Subgroup G} (hBR : B ≤ R)
    (hBinv : ∀ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z →
      (∀ t ∈ d1LiftX p H R K, n * t * n⁻¹ ∈ d1LiftX p H R K) → ∀ b ∈ B, n * b * n⁻¹ ∈ B) :
    (d1LiftX p H R K ≤ B ∨ B ⊓ d1LiftX p H R K = ⊥) ∧
      (B ⊓ d1LiftX p H R K = ⊥ → B ≤ Subgroup.zpowers z ∧ (z ∉ B → B = ⊥)) :=
  inv_subgroup_of hc.prime hc.elt.2.1 hc.card_d1LiftX.1 hc.dec
    (hc.invSubset_ncard_ne hOrb) hBR hBinv

theorem exists_conj_rPart (hc : D1IbConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {y : ↥M ⧸ CFSG.pCore 2 ↥M} (hyL : y ∈ barM M L)
    (hyz : y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * y) {k : ℕ} (hy : y ^ p ^ k = 1) :
    ∃ g : ↥M, QuotientGroup.mk' (CFSG.pCore 2 ↥M) g = y ∧ ∃ a : G, a ∈ M ∧
      a * z = z * a ∧ a⁻¹ * (g : G) * a ∈ rPart M R (barM M L) :=
  exists_conj_rPart_of hc.prime hc.phase.le_M hc.mem_M hc.elt.2.1 hc.coprime_twoCore
    hc.le_centralizer hc.b0 hc.phase.isPGroup (hc.mem_normalizer_of_commute hL) hyL hyz hy

end D1IbConfig

end CFSG.AGLEmbedding
