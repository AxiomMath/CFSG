module

public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockData
import CFSG.LocalAnalysis.AGLEmbedding.BlockThree
import CFSG.LocalAnalysis.AGLEmbedding.MSideAtBlocks
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank
import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockClose
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactBlockAutPrimeInner : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card L →
    (IsOrthogonalTwo ↥L ∨
      (∃ m : ℕ, Nonempty (↥L ≃* alternatingGroup (Fin m)) ∨
        Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin m))) ∨
      (IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) ∧ IsParabolicTwo L J ∧ J ≠ L)) →
    ∀ x ∈ Subgroup.normalizer (L : Set Y), x ∈ Subgroup.normalizer (J : Set Y) → x ^ p = 1 →
      (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) → x ∈ L ⊔ Subgroup.centralizer (L : Set Y)

section Five

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.barM_ne_of_isWeakSBlock (h : D1PhaseThree p P M H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ≠ barM M L :=
  h.toMSideAt.barM_ne_of_isWeakSBlock hL

theorem D1PhaseThree.blockAutType (h : D1PhaseThree p P M H R) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    IsOrthogonalTwo ↥(barM M L) ∨
      (∃ m : ℕ, Nonempty (↥(barM M L) ≃* alternatingGroup (Fin m)) ∨
        Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m))) ∨
      (IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
        IsParabolicTwo (barM M L) (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ∧
        barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ≠ barM M L) := by
  have hn1 := h.nineThree_not_one h85 hD2 hL
  rcases h.nineThree h93 hL with h1 | ⟨hcl, hpar, -⟩ | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hn1.1
  · exact Or.inr (Or.inr ⟨hcl, hpar, h.barM_ne_of_isWeakSBlock hL⟩)
  · exact Or.inl h3.2.1
  · exact Or.inr (Or.inl ⟨6, Or.inr h4.2.2.1⟩)
  · exact Or.inr (Or.inl ⟨7, Or.inl h5.2.1⟩)
  · obtain ⟨-, n, he, -⟩ := h6
    exact Or.inr (Or.inl ⟨2 * n, Or.inr he⟩)
  · obtain ⟨-, n, he, -⟩ := h7
    exact Or.inr (Or.inl ⟨4 * n, Or.inl he⟩)
  · obtain ⟨-, N, r, -, -, -, -, -, he, -⟩ := h8
    exact Or.inr (Or.inl ⟨N, Or.inl he⟩)

theorem D1PhaseThree.mem_normalizer_block_of_five_of_pRank
    (h : D1PhaseThree p P M H R) (hrk3 : Open.pRank 3 (H ⊓ M) ≤ 3) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hp5 : 5 ≤ p) {z : G} (hzK : z ∈ H ⊓ M)
    (hzp : orderOf z = p) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    z ∈ Subgroup.normalizer (L : Set G) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hzpg : IsPGroup p (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzp, pow_one])
  have hB3 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      BlockHasThree M (pCoreOf 2 H) L' :=
    fun L' hL' => stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3' hK5' h hL'
  by_contra hzL
  have hle := h.le_pRank_three_of_not_mem_normalizer' stmtComponentRank stmtBarPRankLift hB3
    (r := p) hzK hzpg hL hzL
  omega

theorem D1PhaseThree.mem_normalizer_block_of_five (h : D1PhaseThree p P M H R)
    (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hp5 : 5 ≤ p) {z : G} (hzK : z ∈ H ⊓ M)
    (hzp : orderOf z = p) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    z ∈ Subgroup.normalizer (L : Set G) := by
  have hrk3 : Open.pRank 3 (H ⊓ M) ≤ 3 := by
    by_contra hc
    exact h.false_of_four_le_pRank' hind Nat.prime_three (by decide) (by omega) (by omega)
  exact h.mem_normalizer_block_of_five_of_pRank hrk3 h85 h86 h93 hD2 hK2 hC3' hK5' hp5 hzK hzp hL

omit [Finite G] in
theorem zbar_mem_normalizer_PL {z : G} (hzK : z ∈ H ⊓ M) {L : Subgroup G}
    (hzL : z ∈ Subgroup.normalizer (L : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzK.2⟩ ∈ Subgroup.normalizer
      (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  mem_normalizer_barM hzK.2 (Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer (localGroup_le_normalizer_pCoreOf 2 H hzK.1), hzL⟩)

theorem D1PhaseThree.dvd_card_of_centralizer_le (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hInn : KFactBlockAutPrimeInner) (hp5 : 5 ≤ p)
    {z : G} (hzK : z ∈ H ⊓ M) (hzp : orderOf z = p)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hzL : z ∈ Subgroup.normalizer (L : Set G)) :
    p ∣ Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hzM : z ∈ M := hzK.2
  set zb := mk ⟨z, hzM⟩
  have hzpg : IsPGroup p (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzp, pow_one])
  by_contra hndP
  have hPL : p.Coprime (Nat.card (barM M (Subgroup.normalizer (S : Set G) ⊓ L))) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hndP
  have hfix := h.fixed_le_barM_normalizer_inf hp h.ne_two hzM hzpg hCz (L := L)
  have hzbL : zb ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM hzM hzL
  have hzbp : zb ^ p = 1 := by
    have : (⟨z, hzM⟩ : M) ^ p = 1 := Subtype.ext (by simp [← hzp, pow_orderOf_eq_one])
    rw [show zb = mk ⟨z, hzM⟩ from rfl, ← map_pow, this, map_one]
  have hzbpg : IsPGroup p (Subgroup.zpowers zb) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one]; exact hzbp)
  have hnd : ¬ p ∣ Nat.card (barM M L) :=
    not_dvd_card_of_fixed_le hp hzbL hzbpg hPL fun l hl hl' => hfix l hl hl'
  have hin := hInn _ (barM M L) (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) hL.component p hp
    hp5 hnd (h.blockAutType h85 h93 hD2 hL) zb hzbL (zbar_mem_normalizer_PL hzK hzL) hzbp
    fun l hl hl' => hfix l hl hl'
  have hzS : z ∈ Subgroup.normalizer (S : Set G) := localGroup_le_normalizer_pCoreOf 2 H hzK.1
  have hzc := h.mem_centralizer_of_mem_sup h84 h86 hD2 hL hPL hin (mem_normalizer_barM hzM hzS)
    (k := 1) (by rw [pow_one]; exact hzbp)
  apply h.barM_ne_of_isWeakSBlock hL
  refine le_antisymm (barM_mono inf_le_right) fun l hl => hfix l hl ?_
  change zb * l * zb⁻¹ = l
  rw [← Subgroup.mem_centralizer_iff.mp hzc l hl, mul_inv_cancel_right]

theorem D1PhaseThree.false_of_centralizer_le_five_of_pRank
    (h : D1PhaseThree p P M H R) (hrk3 : Open.pRank 3 (H ⊓ M) ≤ 3) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hK2 : KFactParabolicThree)
    (hC3' : CitedBlockThreeTransvection) (hK5' : KFactBlockThreeAltSeven)
    (hInn : KFactBlockAutPrimeInner) (hp5 : 5 ≤ p)
    (hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → p.Coprime (Nat.card U))
    {z : G} (hzK : z ∈ H ⊓ M) (hzp : orderOf z = p)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) : False := by
  have hp := h.prime
  obtain ⟨L, hL⟩ := h.exists_weakSBlock h84 hD2
  have hzL := h.mem_normalizer_block_of_five_of_pRank hrk3 h85 h86 h93 hD2 hK2 hC3' hK5' hp5 hzK
      hzp hL
  have hLK : Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ H ⊓ M := by
    rw [h.normalizer_twoCore_H]
    exact inf_le_inf_left H hL.le
  have hPL := h.coprime_card_barM_normalizer_inf h85 h93 hD2 hKP hC3 hK5 hL hp hp5 fun V hV hVp =>
    coprime_card_of_le_barM_of_perfect inf_le_right hperf (hV.trans (barM_mono hLK)) hVp
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp hPL
    (h.dvd_card_of_centralizer_le h84 h85 h86 h93 hD2 hInn hp5 hzK hzp hCz hL hzL)

theorem D1PhaseThree.false_of_centralizer_le_five (h : D1PhaseThree p P M H R)
    (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hK2 : KFactParabolicThree)
    (hC3' : CitedBlockThreeTransvection) (hK5' : KFactBlockThreeAltSeven)
    (hInn : KFactBlockAutPrimeInner) (hp5 : 5 ≤ p)
    (hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → p.Coprime (Nat.card U))
    {z : G} (hzK : z ∈ H ⊓ M) (hzp : orderOf z = p)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) : False := by
  have hrk3 : Open.pRank 3 (H ⊓ M) ≤ 3 := by
    by_contra hc
    exact h.false_of_four_le_pRank' hind Nat.prime_three (by decide) (by omega) (by omega)
  exact h.false_of_centralizer_le_five_of_pRank hrk3 h84 h85 h86 h93 hD2 hKP hC3 hK5 hK2 hC3' hK5'
      hInn
    hp5 hperf hzK hzp hCz

end Five

end CFSG.AGLEmbedding
