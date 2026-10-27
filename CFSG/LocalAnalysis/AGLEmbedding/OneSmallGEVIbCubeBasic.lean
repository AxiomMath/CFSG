module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCubeDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem D1IbCore.toIbCubeConfig {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}
    (hc : D1IbCore p P M H R Rbar K z)
    (hT : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)) = p ^ 3) :
    D1IbCubeConfig p P M H R Rbar K z :=
  ⟨hc.data, hc.elt, hc.b0, hc.cz_le, hc.five_le, hc.not_fi22, hc.phase, hc.dec, hc.exp, hT, hc.perf,
    hc.uniq, hc.cover⟩

namespace D1IbCubeConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem toIbCore (hc : D1IbCubeConfig p P M H R Rbar K z) : D1IbCore p P M H R Rbar K z :=
  ⟨hc.data, hc.elt, hc.b0, hc.cz_le, hc.five_le, hc.not_fi22, hc.phase, hc.dec, hc.exp, hc.perf,
    hc.uniq, hc.cover⟩

theorem prime (hc : D1IbCubeConfig p P M H R Rbar K z) : p.Prime :=
  hc.toIbCore.prime

theorem mem_M (hc : D1IbCubeConfig p P M H R Rbar K z) : z ∈ M :=
  hc.toIbCore.mem_M

theorem le_centralizer (hc : D1IbCubeConfig p P M H R Rbar K z) :
    R ≤ Subgroup.centralizer ({z} : Set G) :=
  hc.toIbCore.le_centralizer

theorem card_d1LiftX (hc : D1IbCubeConfig p P M H R Rbar K z) :
    Nat.card (d1LiftX p H R K) = p ^ 3 ∧ z ∉ d1LiftX p H R K := by
  obtain ⟨hzT, hT⟩ := hc.data.d1LiftX_facts hc.elt
  exact ⟨hT.trans hc.card_T, hzT⟩

theorem coprime_twoCore (hc : D1IbCubeConfig p P M H R Rbar K z) :
    p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) :=
  hc.toIbCore.coprime_twoCore

theorem zbar_pow (hc : D1IbCubeConfig p P M H R Rbar K z) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ^ p = 1 :=
  hc.toIbCore.zbar_pow

theorem zbar_fixed_le (hc : D1IbCubeConfig p P M H R Rbar K z) (L : Subgroup G) :
    ∀ l ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * l *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩)⁻¹ = l →
      l ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) :=
  hc.toIbCore.zbar_fixed_le L

theorem zbar_not_mem_centralizer (hc : D1IbCubeConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∉
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  hc.toIbCore.zbar_not_mem_centralizer hL

theorem perf_block (hc : D1IbCubeConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    IbPerfectSections p (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) :=
  hc.toIbCore.perf_block hL

theorem mem_normalizer_of_commute (hc : D1IbCubeConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {y : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hy : y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * y) :
    y ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  hc.toIbCore.mem_normalizer_of_commute hL hy

theorem exists_cover_block (hc : D1IbCubeConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧
      V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      V ≤ Subgroup.normalizer (barM M (pCoreOf 2 H ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈ V :=
  hc.toIbCore.exists_cover_block hL

theorem zbar_mem_sup (hc : D1IbCubeConfig p P M H R Rbar K z) (hB : D1IbBlockInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  hc.toIbCore.zbar_mem_sup hB hL

end D1IbCubeConfig

end CFSG.AGLEmbedding
