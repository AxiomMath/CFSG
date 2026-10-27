module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineFieldIndexWDispatch
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FourSixteenRank
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FourSixteenUnitary
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLie
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
import CFSG.GroupTheory.SteinbergBSQuotientLifting
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisAltSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamA
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamARank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamB
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamD
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamU
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamURank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisG2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisReduce

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
open Subgroup
open scoped commutatorElement

namespace FourSixteen

theorem not_dvd_card_center_of_compParab
    (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    {L P : Subgroup Y} (hCP : CompParab L P)
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q L ≤ 3) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) : ¬ p ∣ Nat.card (Subgroup.center ↥L) := by
  have hcomp : CFSG.Open.IsQuasisimple ↥L := hCP.comp.2.2
  have hperf : Group.IsPerfect ↥L := ⟨hcomp.1⟩
  have hsimp : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hcomp.2
  have hrk : OddRankLeThree ↥L := oddRankLeThree_of_pRank _ hrank
  have hodd := hCP.odd
  have hrest : IsRestTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → ¬ p ∣ Nat.card (Subgroup.center ↥L) :=
    fun h => not_dvd_card_center_rest (oddCenterRest_of_griess hGA) hCP.comp hodd h hp hp5
  rcases isClassicalTwoOrG2_family_cases hCP.type with ⟨d, hd, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩ |
      h | h | h | h | h
  · obtain ⟨n, f, hn, hf, -, ⟨eX⟩⟩ := heisFamA_model d hd e
    exact (heisARankFacts_holds hGA ↥L hperf hodd hrk hsimp n f (GaloisField 2 f)
      (GaloisField.card 2 f (by omega)) hn hf eX p hp hp5).2.2
  · obtain ⟨d, hv⟩ := d
    cases d with
    | twistedA r q =>
      change q.p = 2 at hd
      have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
      rw [hd] at hc
      obtain ⟨⟨-, hf, hn3, -⟩, K, _, _, hK, ⟨eK⟩⟩ := hc
      rcases heisURankFacts_holds ↥L hperf hodd hrk hsimp (r + 1) q.exponent K hK hn3 hf eK p hp
        hp5 with ⟨-, -, hZ⟩ | ⟨-, -, -, hbot⟩
      · exact hZ
      · rw [hbot, Subgroup.card_bot]
        exact hp.not_dvd_one
    | _ => exact hd.elim
  · exact hrest (Or.inl h)
  · exact hrest (Or.inr (Or.inl h))
  · exact hrest (Or.inr (Or.inr (Or.inl h)))
  · exact hrest (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact hrest (Or.inr (Or.inr (Or.inr (Or.inr h))))

end FourSixteen

variable {G : Type} [Group G] [Finite G]

theorem agl81FourSixteenAt_holds
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hNX : NoXBlockFor G)
    (h98 : AGL81NineEightFour G) : AGL81FourSixteenAt G := by
  intro hS P M H Q K L W a₀ x hd _ _ _ D hDM hD hDc
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hGA := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  obtain ⟨hp, hp2, hyps, -, hLn, hrk, hdvd, hrkW, a, hap, haJ, hnon⟩ :=
    hd.blockFieldIndexW_hyps hS h85 h93 hNX h98
  have h2 := nineThreeTwo_of_not_inner_wPre hp hp2 hyps hrk hdvd hrkW hap haJ hnon
  have hCP := compParab_of_blockHyps hyps h2
  obtain ⟨H₁, R₁, hesc⟩ := hd.data.escape
  have hrank : Open.pRank 5 M = 3 := by
    refine le_antisymm ?_ (hesc.three_le_pRank.trans
      (CFSG.SectionRank.pRank_mono (by norm_num) hesc.le_M))
    have h1 := local_pRank_le_evenRank 5 (by norm_num) (by norm_num) M hesc.maxTwoLocal_M.1
    rw [hS.rank] at h1
    exact h1
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  set N := barM M L with hNdef
  haveI hNn : N.Normal := hLn.map π (QuotientGroup.mk'_surjective _)
  set C := centralizer (N : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCdef
  have hN2 : ¬ 5 ∣ Nat.card (CFSG.pCore 2 ↥M) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow hp h
    omega
  have hJL : blockPL M (pCoreOf 2 H) L ≤ N :=
    fun x ⟨y, hy, hyx⟩ => ⟨y, (Subgroup.mem_inf.1 hy).2, hyx⟩
  have hpN : 5 ∣ Nat.card N :=
    hdvd.trans (Subgroup.card_dvd_of_le ((wPre_le _).trans hJL))
  have hNC : ¬ 5 ∣ Nat.card (N ⊓ C : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 5 h
    have hzN : (z : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ N := (Subgroup.mem_inf.1 z.2).1
    have hzc : (⟨(z : ↥M ⧸ CFSG.pCore 2 ↥M), hzN⟩ : N) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (mem_centralizer_iff.1 (Subgroup.mem_inf.1 z.2).2 g g.2)
    apply FourSixteen.not_dvd_card_center_of_compParab hGA hCP hrk hp le_rfl
    have h1 := Subgroup.orderOf_dvd_natCard (Subgroup.center N) hzc
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hz] at h1
  have hrkY : 3 ≤ Open.pRank 5 (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have h1 := pRank_top_eq_of_coprime_kernel 5 hp π (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hN2)
    rw [← h1, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup M, hrank]
  have hheis : ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Nat.card E = 5 ^ 3 →
      (∀ e ∈ E, e ^ 5 = 1) → (∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a) → E ⊓ C ≠ ⊥ := by
    intro E hEc hEe hEn hEC
    refine heis_dispatch heisCoreAlt_holds heisCoreSmall_holds
      (heisCoreOn_idxA_of_rank_facts (heisARankFacts_holds hGA))
      (heisCoreOn_idxTwistedA_of_rank_facts heisURankFacts_holds) (heisCoreOn_idxB hGA)
      (heisCoreOn_idxD hGA) (heisCoreOn_idxTwistedD hGA) (heisCoreOn_g2 hGA) hyps hrk hp le_rfl
      ?_ hEC hEc hEe hEn ?_
    · rw [Subgroup.normalizer_eq_top N]
      exact le_top
    · rintro hCP' d e ⟨-, -, q, hdq, hq4⟩
      exact FieldIndexW.false_of_twistedA_card_four 5 hCP' d e hdq (by norm_num) hq4 hrk hrkW hap
        haJ hnon
  set D' : Subgroup ↥M := D.subgroupOf M
  haveI := hD.1
  have hD' : IsElemAbelian 5 D' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · change ((a : ↥M) : G) * ((b : ↥M) : G) = ((b : ↥M) : G) * ((a : ↥M) : G)
      exact congrArg Subtype.val
        (mul_comm' (⟨_, mem_subgroupOf.mp a.2⟩ : D) ⟨_, mem_subgroupOf.mp b.2⟩)
    · simpa using hD.2 _ (mem_subgroupOf.mp hx)
  have hD'p : IsPGroup 5 D' := fun x => ⟨1, Subtype.ext (by simpa using hD'.2 _ x.2)⟩
  have hinj := CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype hN2 hD'p
  have hcard : Nat.card (D'.map π) = 5 ^ 2 := by
    have hrange : D'.map π = (π.comp D'.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv, hDc]
    norm_num
  have key := FourSixteen.three_le_pRank_centralizer_of_heis (by norm_num) hpN hNC hrkY hheis
    (CFSG.SectionRank.isElemAbelian_map hD' π) hcard
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hN2 hD'p] at key
  have h1 := TenElevenOneLie.pRank_map_le hp π (by rwa [QuotientGroup.ker_mk'])
    (centralizer (D' : Set ↥M))
  have h2 := CFSG.SectionRank.pRank_le_map (p := 5) (by norm_num) M.subtype
    M.subtype_injective (centralizer (D' : Set ↥M))
  have h3 : (centralizer (D' : Set ↥M)).map M.subtype ≤ centralizer (D : Set G) ⊓ M := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨mem_centralizer_iff.mpr fun e he => ?_, y.2⟩
    have := mem_centralizer_iff.mp hy ⟨e, hDM he⟩ (mem_subgroupOf.mpr he)
    exact congrArg Subtype.val this
  have h4 := CFSG.SectionRank.pRank_mono (p := 5) (by norm_num) h3
  exact key.trans (h1.trans (h2.trans h4))

end CFSG.LocalAnalysis.RankThreeTheoremC
