module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zLayer
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH2Local
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH2Plane
import CFSG.HardMathSupport.Timmesfeld.Proving.ElemAbelianSubgroup
import CFSG.LocalAnalysis.GLTheoremB.BaseCase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem k631b_round1 (hInn : KFactInnerAction) {f : ℕ} {E F : Subgroup G}
    (ctx : k631b_Ctx f E F) (hchar : IsCharTwoType G)
    (hKG : ∀ a : G, a ≠ 1 → IsKGroup ↥(centralizer ({a} : Set G)))
    (hrank : rankThreeLocalRank f G ≤ 3) {t : G} (ht : t ^ 2 = 1) (ht1 : t ≠ 1)
    {U : Subgroup G} (hUF : U ≤ F) (hUt : U ≤ centralizer ({t} : Set G))
    (hU2 : Nat.card U = f ^ 2) :
    ∃ u ∈ F, u ≠ 1 ∧ ∃ J₁ : Subgroup G, GLAPComponent f (centralizer ({u} : Set G)) J₁ ∧
      1 ≤ CFSG.Open.pRank f
        (E ⊓ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁) ∧
      CFSG.Open.pRank f
        (E ⊓ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁) ≤ 2 ∧
      CFSG.Open.pRank f (E ⊓ J₁) + CFSG.Open.pRank f
        (E ⊓ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁) = 4 := by
  have hf := ctx.prime
  have hf1 : 1 < f := hf.one_lt
  have : Fact f.Prime := ⟨hf⟩
  have hUe : IsElemAbelian f U :=
    CFSG.HardMathSupport.Timmesfeld.Proving.isElemAbelian_of_le ctx.elem hUF
  obtain ⟨u, huU, hu1, Y, hY1, hY2, hYu, hUY, hYU⟩ :=
    k631b_plane_Y hchar hf ctx.ne_two ht ht1 hUt hUe hU2
  have huF : u ∈ F := hUF huU
  have hL := k631b_layerHyp ctx hKG hrank huF hu1
  obtain ⟨J₁, hJ₁, Y₁, hY₁1, hY₁2, ⟨e, heQJ, he1, heY⟩, hTY⟩ :=
    k631_project hInn hL hYu hY2 hY1 (hUF.trans ctx.le) hUY hYU
  have hinfJT := k631_comp_triv_inf hL hJ₁
  have huT : u ∈ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁ :=
    k631b_mem_triv (CFSG.LocalAnalysis.GLTheoremB.le_normalizer_glaPPrimeCoreOf f _
      (mem_centralizer_singleton_iff.mpr rfl)) hJ₁.1
  have hlo : 1 ≤ CFSG.Open.pRank f
      (E ⊓ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁) := by
    have hu1' : u ^ f = 1 := ctx.elem.2 u huF
    have huEQ : u ∈ E ⊓ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁ :=
      ⟨ctx.le huF, huT⟩
    refine CFSG.SectionRank.le_pRank hf1 (E := zpowers u)
      (zpowers_le.mpr huEQ) (k631b_isElemAbelian_zpowers hu1') ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hu1' hu1, pow_one]
  have hhi : CFSG.Open.pRank f
      (E ⊓ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁) ≤ 2 := by
    obtain ⟨B, hBle, hBe, hBc⟩ := CFSG.SectionRank.exists_pRank hf1
      (E ⊓ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁)
    obtain ⟨x, hxe, hxf, hx1⟩ := k631b_exists_order_f hf ctx.pgroup heQJ.1 he1
    have hxN : x ∈ normalizer (Y₁ : Set G) := (zpowers_le.mpr heY) hxe
    have hxEJ : x ∈ E ⊓ J₁ := (zpowers_le.mpr heQJ) hxe
    have hxB : x ∉ B := by
      intro hxB
      have hx' : x ∈ E ⊓ J₁ ⊓ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁ :=
        ⟨hxEJ, (hBle hxB).2⟩
      rw [hinfJT, Subgroup.mem_bot] at hx'
      exact hx1 hx'
    have h3 := k631b_succ_rank hf hBe hBc (hBle.trans hTY) hxN hxf hxB
      (fun b hb => ctx.mul_comm (hBle hb).1 hxEJ.1)
    have h4 := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_localRank f hf1
      (normalizer (Y₁ : Set G)) ⟨Y₁, hY₁1, hY₁2, rfl⟩
    omega
  have hsum : CFSG.Open.pRank f (E ⊓ J₁) + CFSG.Open.pRank f
      (E ⊓ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁) = 4 := by
    refine ctx.rank_split inf_le_left inf_le_left ?_ (k631_decomp hInn hL hJ₁)
    refine eq_bot_iff.mpr fun x hx => ?_
    have hx' : x ∈ E ⊓ J₁ ⊓ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁ :=
      ⟨hx.1, hx.2.2⟩
    rwa [hinfJT] at hx'
  exact ⟨u, huF, hu1, J₁, hJ₁, hlo, hhi, hsum⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
