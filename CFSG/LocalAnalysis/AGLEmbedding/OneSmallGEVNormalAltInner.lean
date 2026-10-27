module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltSections
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalFive
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

structure D1AltBlockInputs : Prop where
  h84 : Asc81bEightFour
  h85 : Asc81bEightFive
  h86 : Asc81bEightSix
  h93 : Asc81bNineThree
  hD2 : D1NoXBlock
  hK2 : KFactParabolicThree
  hC3 : CitedBlockThreeTransvection
  hK5 : KFactBlockThreeAltSeven
  hΓ : KFactAltTwoPGamma
  hOP : KFactBlockOutPrime
  hAI : KFactBlockAutAltInner
  hOR : KFactBlockOutRankAlt
  hTA : KFactBlockToralAlt
  hC3T : CitedBlockThreeToralAlt

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ne_inf_normalizer_of_nineThreeTwo {M S L : Subgroup G} (h2 : NineThreeTwo M S L)
    (hn : ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L)) :
    ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsSylowTwoOf T (barM M L) →
      barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≠
        barM M L ⊓ Subgroup.normalizer (T : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  intro T hT heq
  set J := barM M (Subgroup.normalizer (S : Set G) ⊓ L)
  have hTJ : T ≤ J := heq ▸ le_inf hT.1 Subgroup.le_normalizer
  have hJL : J ≤ barM M L := heq ▸ inf_le_left
  have hTsyl : IsSylowTwoOf T J := by
    refine ⟨hTJ, hT.2.1, fun h2J => hT.2.2 ?_⟩
    have := Subgroup.relIndex_mul_relIndex T J (barM M L) hTJ hJL
    exact h2J.trans (Dvd.intro _ this)
  have hle : pCoreOf 2 J ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl
  have hge : T ≤ pCoreOf 2 J := normal_pGroup_le_pCoreOf 2 T J hTJ
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hTJ).mpr (heq ▸ inf_le_right)) hT.2.1
  apply hn
  rw [h2.2.2, le_antisymm hle hge]
  exact hT

theorem D1PhaseThree.blockType_alt {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) (hB : D1AltBlockInputs) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    (IsOrthogonalTwo ↥(barM M L) ∨ ∃ m : ℕ, Nonempty (↥(barM M L) ≃* alternatingGroup (Fin m)) ∨
        Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m))) ∨
      (IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
        IsParabolicTwo (barM M L) (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ∧
        barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ≠ barM M L ∧
        ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsSylowTwoOf T (barM M L) →
          barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ≠
            barM M L ⊓ Subgroup.normalizer (T : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := by
  have hn1 := h.nineThree_not_one hB.h85 hB.hD2 hL
  rcases h.nineThree hB.h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hn1.1
  · exact Or.inr ⟨h2.1, h2.2.1, h.barM_ne_of_isWeakSBlock hL,
      ne_inf_normalizer_of_nineThreeTwo h2 (hn1.2 h2)⟩
  · exact Or.inl (Or.inl h3.2.1)
  · exact Or.inl (Or.inr ⟨6, Or.inr h4.2.2.1⟩)
  · exact Or.inl (Or.inr ⟨7, Or.inl h5.2.1⟩)
  · obtain ⟨-, n, he, -⟩ := h6
    exact Or.inl (Or.inr ⟨2 * n, Or.inr he⟩)
  · obtain ⟨-, n, he, -⟩ := h7
    exact Or.inl (Or.inr ⟨4 * n, Or.inl he⟩)
  · obtain ⟨-, N, r, -, -, -, -, -, he, -⟩ := h8
    exact Or.inl (Or.inr ⟨N, Or.inl he⟩)

namespace D1SmallAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem zbar_pow (hc : D1SmallAltConfig p P M H R Rbar K z) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ^ p = 1 := by
  have : (⟨z, hc.mem_M⟩ : M) ^ p = 1 :=
    Subtype.ext (by simp [← hc.elt.2.1, pow_orderOf_eq_one])
  rw [← map_pow, this, map_one]

theorem isPGroup_zpowers (hc : D1SmallAltConfig p P M H R Rbar K z) :
    IsPGroup p (Subgroup.zpowers z) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc.elt.2.1, pow_one])

theorem zbar_mem_normalizer (hc : D1SmallAltConfig p P M H R Rbar K z) (hB : D1AltBlockInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  mem_normalizer_barM hc.mem_M (hc.phase.mem_normalizer_block_of_five hc.data.cfg.ind hB.h85
    hB.h86 hB.h93 hB.hD2 hB.hK2 hB.hC3 hB.hK5 hc.five_le ⟨hc.elt.2.2.1, hc.mem_M⟩ hc.elt.2.1 hL)

theorem zbar_fixed_le (hc : D1SmallAltConfig p P M H R Rbar K z) (L : Subgroup G) :
    ∀ l ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * l *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩)⁻¹ = l →
      l ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) :=
  hc.phase.fixed_le_barM_normalizer_inf hc.prime hc.data.cfg.red.ne_two hc.mem_M
    hc.isPGroup_zpowers hc.cz_le

theorem zbar_not_mem_centralizer (hc : D1SmallAltConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∉
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  intro hzc
  apply hc.phase.barM_ne_of_isWeakSBlock hL
  refine le_antisymm (barM_mono inf_le_right) fun l hl => hc.zbar_fixed_le L l hl ?_
  rw [← Subgroup.mem_centralizer_iff.mp hzc l hl, mul_inv_cancel_right]

theorem zbar_mem_sup (hc : D1SmallAltConfig p P M H R Rbar K z) (hB : D1AltBlockInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hN := hc.zbar_mem_normalizer hB hL
  have hzK : z ∈ H ⊓ M := ⟨hc.elt.2.2.1, hc.mem_M⟩
  have hzL : z ∈ Subgroup.normalizer (L : Set G) :=
    hc.phase.mem_normalizer_block_of_five hc.data.cfg.ind hB.h85 hB.h86 hB.h93 hB.hD2 hB.hK2
      hB.hC3 hB.hK5 hc.five_le hzK hc.elt.2.1 hL
  rcases hc.phase.blockType_alt hB hL with htype | ⟨hcl, hpar, hne, hnB⟩
  · exact hB.hOP _ (barM M L) hL.component p hc.prime hc.five_le htype _ hN hc.zbar_pow
  · exact hB.hAI _ (barM M L) _ hL.component p hc.prime57 hcl hpar hne hnB
      (hc.perfectSectionsAltSq_block hB.hΓ hL) _ hN (zbar_mem_normalizer_PL hzK hzL)
      hc.zbar_pow (hc.zbar_fixed_le L)

end D1SmallAltConfig

end CFSG.AGLEmbedding
