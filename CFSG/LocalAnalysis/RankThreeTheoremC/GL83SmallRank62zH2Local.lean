module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH2Rank
import CFSG.LocalAnalysis.GLTheoremB.BaseCase
import CFSG.HardMathSupport.Solomon.LocalBalance.TwoLocalTools
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem k631b_mem_triv_iff {O J : Subgroup G} {q : G} :
    q ∈ k631Triv O J ↔ q ∈ normalizer (O : Set G) ∧ q ∈ normalizer (J : Set G) ∧
      ∀ j ∈ J, ⁅q, j⁆ ∈ O :=
  Iff.rfl

theorem k631b_mem_triv {O J : Subgroup G} {q : G} (hq : q ∈ normalizer (O : Set G))
    (hJ : J ≤ centralizer ({q} : Set G)) : q ∈ k631Triv O J := by
  have hqc : q ∈ centralizer (J : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    exact mem_centralizer_singleton_iff.mp (hJ hh)
  refine k631b_mem_triv_iff.mpr ⟨hq, centralizer_le_normalizer _ hqc, fun j hj => ?_⟩
  have h1 : j * q = q * j := mem_centralizer_iff.mp hqc j hj
  have h2 : ⁅q, j⁆ = 1 := by
    rw [commutatorElement_def, ← h1]
    group
  rw [h2]
  exact O.one_mem

variable [Finite G]

theorem k631b_Ctx.le_centralizer {f : ℕ} {E F : Subgroup G} (ctx : k631b_Ctx f E F) {u : G}
    (huF : u ∈ F) : E ≤ centralizer ({u} : Set G) := fun _ hx =>
  mem_centralizer_singleton_iff.mpr (ctx.mul_comm hx (ctx.le huF))

theorem k631b_odd_core {f : ℕ} {E F : Subgroup G} (ctx : k631b_Ctx f E F)
    (hrank : rankThreeLocalRank f G ≤ 3) {u : G} (huF : u ∈ F) :
    Odd (Nat.card ↥(GLAPPrimeCoreOf f (centralizer ({u} : Set G)))) := by
  by_contra hodd
  have heven : Even (Nat.card ↥(GLAPPrimeCoreOf f (centralizer ({u} : Set G)))) :=
    Nat.not_odd_iff_even.mp hodd
  have hEn : E ≤ normalizer (GLAPPrimeCoreOf f (centralizer ({u} : Set G)) : Set G) :=
    (ctx.le_centralizer huF).trans
      (CFSG.LocalAnalysis.GLTheoremB.le_normalizer_glaPPrimeCoreOf f _)
  obtain ⟨T, hT1, -, hT2, hET⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.exists_twoGroup_normalized_of_coprime_even
      ctx.prime ctx.ne_two ctx.pgroup hEn
      (CFSG.LocalAnalysis.GLTheoremB.not_dvd_card_glaPPrimeCoreOf ctx.prime _) heven
  have h1 := CFSG.SectionRank.pRank_mono ctx.prime.one_lt hET
  have h2 := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_localRank f ctx.prime.one_lt
    (normalizer (T : Set G)) ⟨T, hT1, hT2, rfl⟩
  rw [ctx.rank] at h1
  omega

theorem k631b_layerHyp {f : ℕ} {E F : Subgroup G} (ctx : k631b_Ctx f E F)
    (hKG : ∀ a : G, a ≠ 1 → IsKGroup ↥(centralizer ({a} : Set G)))
    (hrank : rankThreeLocalRank f G ≤ 3) {u : G} (huF : u ∈ F) (hu1 : u ≠ 1) :
    LayerHyp f (centralizer ({u} : Set G)) E where
  prime := ctx.prime
  ne_two := ctx.ne_two
  kgroup := hKG u hu1
  le := ctx.le_centralizer huF
  pgroup := ctx.pgroup
  sylow := fun hdvd =>
    ctx.sylow (hdvd.trans (Subgroup.relIndex_dvd_index_of_le (ctx.le_centralizer huF)))
  comm := ctx.comm
  odd := k631b_odd_core ctx hrank huF

end CFSG.LocalAnalysis.RankThreeTheoremC
