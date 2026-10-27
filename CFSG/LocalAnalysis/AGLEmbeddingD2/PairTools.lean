module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Data
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Closure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPhaseThree
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPairBlockRank

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem exists_weakSBlock_or_le_inf (h : AGLPair p M H R)
    {Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hL : IsComponentOf Lbar ⊤) :
    ∃ L : Subgroup G, IsTwoPrimeComponent M L ∧ barM M L = Lbar ∧
      (IsWeakSBlock M (pCoreOf 2 H) L ∨ L ≤ H ⊓ M) :=
  h.toTwoLocalPair.exists_weakSBlock_or_le_inf hL

theorem card_le_pRank_three_of_blocks (h : AGLPair p M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {ι : Type} [Finite ι] (L : ι → Subgroup G) (hL : ∀ i, IsWeakSBlock M (pCoreOf 2 H) (L i))
    (hinj : Function.Injective L) : Nat.card ι ≤ Open.pRank 3 (H ⊓ M) :=
  h.toTwoLocalPair.card_le_pRank_three_of_blocks hB3 L hL hinj

theorem le_pRank_three_of_not_mem_normalizer (h : AGLPair p M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {r : ℕ} [Fact r.Prime] {g : G} (hgK : g ∈ H ⊓ M) (hg : IsPGroup r (Subgroup.zpowers g))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hgL : g ∉ Subgroup.normalizer (L : Set G)) : r ≤ Open.pRank 3 (H ⊓ M) :=
  h.toTwoLocalPair.le_pRank_three_of_not_mem_normalizer hB3 hgK hg hL hgL

theorem mem_normalizer_weakSBlock (hD1 : D1For G) (h : AGLPair p M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) {g : G} (hgK : g ∈ H ⊓ M)
    (hg : IsPGroup r (Subgroup.zpowers g)) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : g ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hgL
  have : Fact r.Prime := ⟨hr⟩
  have hle := h.le_pRank_three_of_not_mem_normalizer hB3 hgK hg hL hgL
  exact h.false_of_four_le_pRank hD1 Nat.prime_three (by decide) (by omega)

theorem le_barM_inf_of_le_centralizer (h : AGLPair p M H R)
    {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hT : T ≤ Subgroup.centralizer (barM M (pCoreOf 2 H) : Set _)) : T ≤ barM M (H ⊓ M) :=
  h.toTwoLocalPhaseThree.le_barM_inf_of_le_centralizer hT

theorem normal_sup_of_le_pCore (h : AGLPair p M H R) (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G)
    (hR : barM M R ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)) :
    ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal := by
  have hRY : R ≤ pCorePreimage p M := fun x hx =>
    ⟨⟨x, h.le_M hx⟩, hR (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)), rfl⟩
  have heq := h.inf_sup_twoCore_eq h84 hD2
  rw [inf_of_le_left hRY] at heq
  rw [heq, pCorePreimage_subgroupOf]
  exact Subgroup.Normal.comap inferInstance _

end AGLPair

namespace D2L2Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {M H R X : Subgroup G}

theorem isElemAbelian (h : D2L2Data p M H R X) : IsElemAbelian p X := by
  obtain ⟨φ, -⟩ := h.torus
  exact isElemAbelian_of_mulEquiv_galoisField φ

theorem card_eq (h : D2L2Data p M H R X) : Nat.card X = p ^ 2 := by
  obtain ⟨φ, -⟩ := h.torus
  rw [← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
    GaloisField.card p 2 (by norm_num)]

theorem le_inf_normalizer (h : D2L2Data p M H R X) :
    X ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  h.pair.inf_eq_inf_normalizer_twoCore ▸ h.eq_R.le.trans h.pair.R_le_inf

theorem coprime_of_perfect (h : D2L2Data p M H R X) :
    ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) → ⁅Y, Y⁆ = Y →
      p.Coprime (Nat.card Y) := by
  intro Y hY hperf
  have hYN := h.perfect_le Y (h.pair.inf_eq_inf_normalizer_twoCore ▸ hY) hperf
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hYN)
    (glbPrimeCore_coprime p H)

theorem isElemAbelian_barM (h : D2L2Data p M H R X) : IsElemAbelian p (barM M X) :=
  CFSG.AGLEmbedding.isElemAbelian_barM_of_isElemAbelian h.isElemAbelian

theorem card_barM (h : D2L2Data p M H R X) : Nat.card (barM M X) = p ^ 2 :=
  (card_barM_eq_of_isElemAbelian Fact.out h.pair.ne_two h.isElemAbelian
    (h.eq_R.le.trans h.pair.le_M)).trans h.card_eq

theorem le_normalizer_weakSBlock (hD1 : D1For G) (h : D2L2Data p M H R X) (hp5 : 5 ≤ p)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    X ≤ Subgroup.normalizer (L : Set G) := fun x hxX =>
  h.pair.mem_normalizer_weakSBlock hD1 hB3 h.pair.prime hp5 (h.pair.R_le_inf (h.eq_R ▸ hxX))
    (isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using h.isElemAbelian.2 x hxX)) hL

end D2L2Data

namespace D2L2Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {M H R X : Subgroup G}

theorem le_pCore_of_forall_le_centralizer (h : D2L2Data p M H R X) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G)
    (hcomp : ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M X ≤ Subgroup.centralizer (Lbar : Set _))
    (hodd : ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p → barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)) :
    barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) :=
  h.pair.toTwoLocalPhaseThree.le_pCore_of_forall_le_centralizer h.pair.isKGroup.1 h.pair.ne_two
    h.normal_dichotomy h.isElemAbelian_barM h84 hD2 hcomp hodd

end D2L2Data

end CFSG.AGLEmbeddingD2
