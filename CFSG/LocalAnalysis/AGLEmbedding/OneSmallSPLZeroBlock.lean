module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalFive
public import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockClose
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer

public section


namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactBlockOuterPerfectCent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p.Coprime (Nat.card J) →
    ∀ x ∈ Subgroup.normalizer (L : Set Y), x ∈ Subgroup.normalizer (J : Set Y) → x ^ p = 1 →
      x ∉ L ⊔ Subgroup.centralizer (L : Set Y) →
      ∃ D : Subgroup Y, D ≤ L ∧ D ≠ ⊥ ∧ ⁅D, D⁆ = D ∧ D ≤ Subgroup.centralizer ({x} : Set Y)

section Block

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.false_of_coprime_block (h : D1PhaseThree p P M H R)
    (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hOP : KFactBlockOutPrime)
    (hBO : KFactBlockOuterPerfectCent) (hp5 : 5 ≤ p) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hPL : p.Coprime (Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))))
    {z : G} (hzK : z ∈ H ⊓ M) (hzp : orderOf z = p)
    (hZ : ∀ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅D, D⁆ = D →
      D ≤ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzK.2⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        D = ⊥) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hzL := h.mem_normalizer_block_of_five hind h85 h86 h93 hD2 hK2 hC3' hK5' hp5 hzK hzp hL
  set zb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzK.2⟩ with hzb
  have hzS : z ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 H hzK.1
  have hzbS := mem_normalizer_barM hzK.2 hzS
  have hzbL : zb ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM hzK.2 hzL
  have hzbp : zb ^ p = 1 := by
    have h1 : (⟨z, hzK.2⟩ : ↥M) ^ p = 1 := Subtype.ext (by simp [← hzp, pow_orderOf_eq_one])
    rw [hzb, ← map_pow, h1, map_one]
  have hLbot : barM M L ≠ ⊥ := fun hbot => h.barM_ne_of_isWeakSBlock hL (by
    have h1 : barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ≤ barM M L :=
      barM_mono inf_le_right
    rw [hbot] at h1 ⊢
    exact le_bot_iff.mp h1)
  have hLperf : ⁅barM M L, barM M L⁆ = barM M L :=
    Subgroup.isPerfect_iff.mp (⟨hL.component.2.2.1⟩ : Group.IsPerfect ↥(barM M L))
  have hinner : zb ∉ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro hin
    have hc := h.mem_centralizer_of_mem_sup h84 h86 hD2 hL hPL hin hzbS (k := 1)
      (by rw [pow_one]; exact hzbp)
    refine hLbot (hZ _ hLperf fun l hl => ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hc l hl
  rcases blockType_ib h h85 h93 hD2 hL with htype | ⟨hcl, hpar, hne, hnB⟩
  · exact hinner (hOP _ (barM M L) hL.component p hp hp5 htype zb hzbL hzbp)
  · obtain ⟨D, -, hD1, hDp, hDz⟩ := hBO _ (barM M L) _ hL.component hcl hpar hne hnB p hp hp5
      hPL zb hzbL (zbar_mem_normalizer_PL hzK hzL) hzbp hinner
    exact hD1 (hZ D hDp hDz)

theorem D1PhaseThree.exists_perfect_dvd_of_perfect_centralizer (h : D1PhaseThree p P M H R)
    (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hK2 : KFactParabolicThree)
    (hC3' : CitedBlockThreeTransvection) (hK5' : KFactBlockThreeAltSeven)
    (hOP : KFactBlockOutPrime) (hBO : KFactBlockOuterPerfectCent) (hp5 : 5 ≤ p)
    {z : G} (hzK : z ∈ H ⊓ M) (hzp : orderOf z = p)
    (hZ : ∀ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅D, D⁆ = D →
      D ≤ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzK.2⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        D = ⊥) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ∧ ⁅V, V⁆ = V ∧
        p ∣ Nat.card V := by
  have hp := h.prime
  by_contra hno
  push Not at hno
  exact h.false_of_coprime_block hind h84 h85 h86 h93 hD2 hK2 hC3' hK5' hOP hBO hp5 hL
    (h.coprime_card_barM_normalizer_inf h85 h93 hD2 hKP hC3 hK5 hL hp hp5
      fun V hVP hVp => (Nat.Prime.coprime_iff_not_dvd hp).mpr (hno V hVP hVp)) hzK hzp hZ

theorem D1PhaseThree.false_of_perfect_centralizer (h : D1PhaseThree p P M H R)
    (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hK2 : KFactParabolicThree)
    (hC3' : CitedBlockThreeTransvection) (hK5' : KFactBlockThreeAltSeven)
    (hOP : KFactBlockOutPrime) (hBO : KFactBlockOuterPerfectCent) (hp5 : 5 ≤ p)
    (hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → p.Coprime (Nat.card U))
    {z : G} (hzK : z ∈ H ⊓ M) (hzp : orderOf z = p)
    (hZ : ∀ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅D, D⁆ = D →
      D ≤ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzK.2⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        D = ⊥) : False := by
  have hp := h.prime
  obtain ⟨L, hL⟩ := h.exists_weakSBlock h84 hD2
  have hLK : Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ H ⊓ M := by
    rw [h.normalizer_twoCore_H]
    exact inf_le_inf_left H hL.le
  obtain ⟨V, hVP, hVp, hpV⟩ := h.exists_perfect_dvd_of_perfect_centralizer hind h84 h85 h86 h93
    hD2 hKP hC3 hK5 hK2 hC3' hK5' hOP hBO hp5 hzK hzp hZ hL
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp
    (coprime_card_of_le_barM_of_perfect inf_le_right hperf (hVP.trans (barM_mono hLK)) hVp) hpV

end Block

end CFSG.AGLEmbedding
