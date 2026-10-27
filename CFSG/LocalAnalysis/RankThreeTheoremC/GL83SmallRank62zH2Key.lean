module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zLayer
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH2Rank
import CFSG.HardMathSupport.Timmesfeld.Proving.ElemAbelianSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem k631b_key {f : ℕ} {X Q J : Subgroup G} (hf : f.Prime)
    (hrank : rankThreeLocalRank f G ≤ 3) (hL : LayerHyp f X Q)
    (hJ : GLAPComponent f X J) (hpr : 2 ≤ CFSG.Open.pRank f (Q ⊓ J))
    {A W : Subgroup G} (hA : IsElemAbelian f A) (hAc : Nat.card A = f ^ 2) (hAQ : A ≤ Q)
    (hAT : A ≤ k631Triv (GLAPPrimeCoreOf f X) J) (hW1 : W ≠ ⊥) (hW2 : IsPGroup 2 W)
    (hWL : W ≤ GLAPLayer f X) (hAW : A ≤ normalizer (W : Set G)) (hWA : ⁅W, A⁆ = W) :
    False := by
  have hf1 : 1 < f := hf.one_lt
  obtain ⟨D, hDle, hDp, hDi, hDc⟩ := k631_centralizing_sylow hL hJ hW2 hWL hAQ hAT hAW hWA
  have hDJ : D ≤ J := hDle.trans inf_le_left
  have hD2 : 2 ≤ CFSG.Open.pRank f D := by
    have h1 : CFSG.Open.pRank f (Q ⊓ J) ≤ CFSG.Open.pRank f J :=
      CFSG.SectionRank.pRank_mono hf1 inf_le_right
    have h2 : CFSG.Open.pRank f J ≤ CFSG.Open.pRank f D :=
      k631b_pRank_le_of_sylow hf hDJ hDp hDi
    omega
  obtain ⟨B, hBD, hBe, hBc⟩ := CFSG.SectionRank.exists_pRank hf1 D
  obtain ⟨D₀, hD₀B, hD₀e, hD₀c⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.exists_elemAbelian_subgroup_card_pow hf hBe hD2 hBc
  have hD₀D : D₀ ≤ D := hD₀B.trans hBD
  have hinf : A ⊓ D₀ = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hx1 : x ∈ Q ⊓ J ⊓ k631Triv (GLAPPrimeCoreOf f X) J :=
      ⟨⟨hAQ hx.1, hDJ (hD₀D hx.2)⟩, hAT hx.1⟩
    rw [k631_comp_triv_inf hL hJ] at hx1
    exact hx1
  obtain ⟨hJe, hJc⟩ :=
    k631b_join_elem (fun a ha d hd => hDc a ha d (hD₀D hd)) hinf hA hD₀e
  have hDW : D ≤ normalizer (W : Set G) :=
    hDle.trans (inf_le_right.trans (centralizer_le_normalizer _))
  have hle : A ⊔ D₀ ≤ normalizer (W : Set G) := sup_le hAW (hD₀D.trans hDW)
  have h4 : 2 + 2 ≤ CFSG.Open.pRank f (normalizer (W : Set G)) := by
    refine CFSG.SectionRank.le_pRank hf1 hle hJe ?_
    rw [hJc, hAc, hD₀c, ← pow_add]
  have h5 := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_localRank f hf1
    (normalizer (W : Set G)) ⟨W, hW1, hW2, rfl⟩
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
