module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltData
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.ComponentsK
import CFSG.LocalAnalysis.AGLEmbeddingD2.PairBlocksMore
import CFSG.LocalAnalysis.AGLEmbeddingD2.PairTools
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem isCatalogGroup_center_quotient_component (h : AGLPair p M H R)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤) :
    IsCatalogGroup (↥Lb ⧸ Subgroup.center ↥Lb) :=
  have hMtop : M ≠ ⊤ := fun hM => h.not_le (hM ▸ le_top)
  ((catalogSimpleSections_of_isKProper h.glob.kProper M hMtop).quotient _
    ).isCatalogGroup_center_quotient hLb

theorem isSolvable_outer_component (h : AGLPair p M H R) (hSch : KFactCatalogSchreier)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤) :
    Group.IsSolvable (Outer Lb) := by
  have : Group.IsPerfect Lb := ⟨hLb.2.2.1⟩
  have : Group.IsSolvable (Outer (↥Lb ⧸ Subgroup.center ↥Lb)) :=
    hSch _ hLb.2.2.2 (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      _ hLb.2.2) (h.isCatalogGroup_center_quotient_component hLb)
  exact solvable_of_centerQuotient Lb

theorem le_normalizer_component (h : AGLPair p M H R) (hD1 : D1For G) (hα : KFactThreeOrFiveDvd)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {W : Subgroup G} (hWK : W ≤ H ⊓ M) (hW : ⁅W, W⁆ = W)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤) :
    barM M W ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨L, hL2, rfl, hL⟩ := h.exists_weakSBlock_or_le_inf hLb
  rcases hL with hw | hLK
  ·
    have hidx := h.relIndex_le_pRank_three hB3 hWK hw
    have hWN : W ≤ Subgroup.normalizer (L : Set G) := by
      refine le_of_relIndex_le_four_of_perfect hW ?_
      rw [← Subgroup.inf_relIndex_left]
      exact hidx.trans ((h.pRank_inf_le_three hD1 Nat.prime_three (by decide)).trans (by norm_num))
    exact barM_le_normalizer_barM hWN
  ·
    have hLcat := h.isCatalogGroup_center_quotient_component hLb
    obtain ⟨q, hq, hq2, hqdvd⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
        q ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
      rcases hα _ hLb.2.2.2 (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
        _ hLb.2.2) hLcat with h3d | h5d
      · exact ⟨3, Nat.prime_three, by decide, h3d⟩
      · exact ⟨5, Nat.prime_five, by decide, h5d⟩
    obtain ⟨y, hyL, hyq, l, hlL, hyl⟩ := exists_qElement_not_central hq hqdvd
    obtain ⟨g, hg, hinj⟩ := exists_injective_conj_relIndex (barM M W) (barM M L)
    have hidx := le_pRank_of_injective_conj_of_normalizer inf_le_right hq hq2 hLb
      (barM_mono hLK) hyL hyq hlL hyl g
      (fun j => Subgroup.le_normalizer (barM_mono hWK (hg j))) hinj
    exact le_of_relIndex_le_four_of_perfect (commutator_barM_eq_self (hWK.trans inf_le_right) hW)
      (hidx.trans ((h.pRank_inf_le_three hD1 hq hq2).trans (by norm_num)))

theorem le_sup_centralizer_component (h : AGLPair p M H R) (hD1 : D1For G)
    (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {W : Subgroup G} (hWK : W ≤ H ⊓ M) (hW : ⁅W, W⁆ = W)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤) :
    barM M W ≤ Lb ⊔ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  perfect_le_sup_centralizer_of_outer (h.isSolvable_outer_component hSch hLb)
    (commutator_barM_eq_self (hWK.trans inf_le_right) hW)
    (h.le_normalizer_component hD1 hα hB3 hWK hW hLb)

end AGLPair

theorem exists_not_le_centralizer_of_pCore_eq_bot {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hO2 : CFSG.pCore 2 Y = ⊥) (hOp : CFSG.pCore p Y = ⊥) {U : Subgroup Y} (hU : IsPGroup p U)
    (hodd : ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p →
      U ≤ Subgroup.centralizer (CFSG.pCore s Y : Set Y)) (hU1 : U ≠ ⊥) :
    ∃ Lb : Subgroup Y, IsComponentOf Lb ⊤ ∧ ¬ U ≤ Subgroup.centralizer (Lb : Set Y) := by
  by_contra hcon
  push Not at hcon
  refine hU1 (le_bot_iff.mp ?_)
  rw [← hOp]
  refine le_pCore_of_le_centralizer_components hU hcon fun l hl => ?_
  by_cases hl2 : l = 2
  · rw [hl2, hO2]
    exact Subgroup.le_centralizer_iff.mp bot_le
  by_cases hlp : l = p
  · rw [hlp, hOp]
    exact Subgroup.le_centralizer_iff.mp bot_le
  exact hodd l hl hl2 hlp

namespace D2AltData

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {M H R X : Subgroup G}

private theorem isPGroup_barM_X (h : D2AltData p M H R X) : IsPGroup p (barM M X) := by
  have hXp : IsPGroup p X := by
    rw [h.eq_R]
    exact h.pair.isPGroup_R
  exact (hXp.comap_of_injective M.subtype M.subtype_injective).map _

theorem le_normalizer_component (h : D2AltData p M H R X) (hD1 : D1For G)
    (hα : KFactThreeOrFiveDvd)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {W : Subgroup G} (hWK : W ≤ H ⊓ M) (hW : ⁅W, W⁆ = W)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤) :
    barM M W ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  h.pair.le_normalizer_component hD1 hα hB3 hWK hW hLb

theorem exists_not_le_centralizer (h : D2AltData p M H R X) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G)
    (hodd : ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p → barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _))
    {U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hUX : U ≤ barM M X) (hU : U ≠ ⊥) :
    ∃ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ ∧
      ¬ U ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  exists_not_le_centralizer_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot' 2)
    (h.pCore_eq_bot h84 hD2) (h.isPGroup_barM_X.to_le hUX)
    (fun s hs hs2 hsp => hUX.trans (hodd s hs hs2 hsp)) hU

end D2AltData

end CFSG.AGLEmbeddingD2
