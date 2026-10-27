module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenFiveDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenFivePkg
import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocksAux2
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedNext3Heis
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Action
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Rank
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (D1Extremal D1Escape D1PhaseThree Asc81bEightFour Asc81bEightFive
  Asc81bEightSix Asc81bNineThree D1NoXBlock IsWeakSBlock KFactOutElemRank barM
  catalogSimpleSections_of_isKProper stmtBarPRankLift)

variable {G : Type} [Group G] [Finite G]

theorem kl5_inf_preimage_eq_bot {p : ℕ} [Fact p.Prime] {M L R X : Subgroup G} {σ z : G}
    (h : D1KlingenFivePkg p R X σ z) (hR : IsPGroup p R) (hRM : R ≤ M)
    (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hnot : ¬ ∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hRM (h.le_R h.z_mem)⟩ * y =
      y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hRM (h.le_R h.z_mem)⟩) :
    R ⊓ ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype = ⊥ := by
  have hzR : z ∈ R := h.le_R h.z_mem
  have hz : orderOf z = p := orderOf_eq_prime (h.elem.2 z h.z_mem) h.z_ne
  obtain ⟨φ, hφ⟩ := exists_action_barM hRM hRL
  have hinj := injective_action_barM hR hRM hzR hz
    (fun y hyC hyR _ => h.center_le y hyR hyC) hφ hnot
  rw [eq_bot_iff]
  rintro x ⟨hxP, m, hm, rfl⟩
  have h1 : φ ⟨(m : G), hxP⟩ = 1 := (hφ _).mpr fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hm y hy).symm
  have h2 := hinj (h1.trans (map_one φ).symm)
  exact Subgroup.mem_bot.mpr (congrArg (Subtype.val : ↥R → G) h2)

theorem kl5_false_of_weakSBlock {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hK7 : KFactBlockHeisenbergInner) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) {P : Sylow p G}
    {M H R X : Subgroup G} {σ z : G} (hph : D1PhaseThree p P M H R) (hrank : evenRank G = 3)
    (hpkg : D1KlingenFivePkg p R X σ z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hfaith : R ⊓ ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype = ⊥) : False := by
  have hRM : R ≤ M := hph.le_M
  have hyps : BlockL28Hyps M (pCoreOf 2 H) L :=
    ⟨hph.isKGroup.1, hph.asc81bHyp, hL, hph.nineThree h93 hL,
      (hph.nineThree_not_one h85 hD2 hL).1, hph.not_isSylowTwoOf_inf h85 hD2 hL⟩
  have hQS : pCoreOf 2 M ≤ pCoreOf 2 H := hph.twoCore_M_le hph.twoCore_inf
  have hLbM : barM M L ≤ barM M M := by
    rintro _ ⟨a, -, rfl⟩
    exact ⟨a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  have hrk : ∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3 := by
    intro q hq hq2
    have h1 : Open.pRank q (barM M L) ≤ Open.pRank q (barM M M) :=
      CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono q hq.one_lt hLbM
    have h2 := stmtBarPRankLift hq hq2 M M le_rfl
    have h3 := local_pRank_le_localRank q hq.one_lt M hph.maxTwoLocal_M.1
    have h4 := rankThreeLocalRank_le_evenRank (G := G) q hq hq2
    rw [hrank] at h4
    omega
  refine hK7 G M (pCoreOf 2 H) L hyps hQS hrk p Fact.out hp5 (barM M R)
    (barM_le_normalizer le_rfl hRM hRL) (barM_inf_centralizer_eq_bot le_rfl hfaith)
    ((card_barM_of_faithful le_rfl hRM hfaith).trans hpkg.card_R) ?_ ?_
  · obtain ⟨E, hER, hEc, hEe, a, ha, b, hb, hab⟩ := hpkg.heis
    refine ⟨barM M E, ?_, (card_barM_of_faithful hER hRM hfaith).trans hEc,
      pow_eq_one_of_mem_barM hEe, ?_⟩
    · rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, Subgroup.mem_subgroupOf.mpr (hER (Subgroup.mem_subgroupOf.mp hm)), rfl⟩
    · exact exists_noncomm_barM hER hRM hfaith ⟨a, ha, b, hb, hab⟩
  · rintro _ ⟨l, hl, rfl⟩ ⟨_, ⟨x, hx, rfl⟩, hxl⟩
    exact hph.mk_mem_barM_of_mul_inv_mem h84 h86 hD2 hL (x := x) (l := l)
      (hph.le_inf (Subgroup.mem_subgroupOf.mp hx)) (Subgroup.mem_subgroupOf.mp hl) hxl

end CFSG.LocalAnalysis.RankThreeTheoremC
