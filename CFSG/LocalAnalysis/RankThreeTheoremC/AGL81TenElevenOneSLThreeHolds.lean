module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineFieldIndexW
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLie
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneSLThreeOdd
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneSLThreeField
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneSLThreeRank
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneSLThreeE27
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineFieldIndexWDispatch
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineFieldIndexOf
import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterMain
import CFSG.GroupTheory.SteinbergBSQuotientLifting
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsGlue
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.RankThree.PartTwo.Sec4 Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
open scoped commutatorElement

@[expose] def KFactTenOneEight : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (M S L : Subgroup A), BlockL28Hyps M S L →
    pCoreOf 2 M ≤ S → ∀ n : ℕ,
    IsLieOver (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) (.A 2) 2 n →
    Nonempty (↥(barM M L) ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n))

variable {G : Type} [Group G] [Finite G]

theorem AGL81ElevenNineData.mk_normalizer_not_inner_wPre (hS : Setting G)
    (h98 : AGL81NineEightFour G) {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {L W : Subgroup G} {a₀ : G}
    (hd : AGL81ElevenNineData p P M H Q K L W a₀) :
    ∃ ha : a₀ ∈ M,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a₀, ha⟩ ∈
        Subgroup.normalizer (blockPL M (pCoreOf 2 H) L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      ¬ ∃ v ∈ wPre (blockPL M (pCoreOf 2 H) L), ∀ w ∈ wPre (blockPL M (pCoreOf 2 H) L),
        ⁅QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a₀, ha⟩ * v, w⁆ ∈
          pCoreOf 2 (blockPL M (pCoreOf 2 H) L) := by
  have hT := hd.data.toTwoLocalPhaseThree' hS h98
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  set S := pCoreOf 2 H with hSdef
  have ha₀HM := hd.sylow.2.1 hd.mem
  have ha₀S : a₀ ∈ Subgroup.normalizer (S : Set G) := hNH.symm ▸ ha₀HM.1
  have hLc : IsTwoPrimeComponent M L := hd.block.toIsTwoPrimeComponent
  have hXM : Subgroup.normalizer (S : Set G) ⊓ L ≤ M := by
    rw [hNH]
    exact inf_le_right.trans hLc.le
  have ha₀X : a₀ ∈ normalizer ((Subgroup.normalizer (S : Set G) ⊓ L : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have h1 := mem_normalizer_iff.mp (le_normalizer ha₀S) y
    have h2 := mem_normalizer_iff.mp (hd.normal ha₀HM.2) y
    exact (mem_inf.trans (and_congr h1 h2)).trans mem_inf.symm
  refine ⟨ha₀HM.2, ?_, fun h => ?_⟩
  · have haL' := TenThreeThree.mem_normalizer_barM ha₀HM.2 (hd.normal ha₀HM.2)
    have haS' := TenThreeThree.mem_normalizer_barM ha₀HM.2 ha₀S
    exact Subgroup.mem_normalizer_fintype
      (CFSG.HardMathSupport.Curtis.Coordinator.blockPL_conj_mem hT.asc81bHyp haL' haS')
  · obtain ⟨j, hj, hjy⟩ := exists_inner_jZero_of_inner_wPre hXM ha₀HM.2 ha₀X h
    rw [hNH] at hj hjy
    exact hd.not_split (hd.split_of_inner hj hjy)

theorem modThree_two_pow_of_even {k : ℕ} (hk : Even k) : ModThree true (2 ^ k) := by
  obtain ⟨j, rfl⟩ := hk
  change 2 ^ (j + j) % 3 = 1
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem agl81TenElevenOneLie_holds
    (h108 : KFactTenOneEight) (hodd : SL3E27.KFactLThreeOddAutRank) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (hNX : NoXBlockFor G) (h98 : AGL81NineEightFour G) :
    AGL81TenElevenOneLie G := by
  intro hS P M H Q K L W a₀ hd V hVM hc _ hlie
  refine absurd ?_ hc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hp, hp2, hyps, hQS, hLn, hrk, hdvd, hrkW, -⟩ :=
    hd.blockFieldIndexW_hyps hS h85 h93 hNX h98
  obtain ⟨ha₀M, haJ, hnon⟩ := hd.mk_normalizer_not_inner_wPre hS h98
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  set a : ↥M ⧸ CFSG.pCore 2 ↥M := π ⟨a₀, ha₀M⟩ with ha
  have ha3 : a ^ 3 = 1 := by
    have h1 : (⟨a₀, ha₀M⟩ : ↥M) ^ 3 = 1 :=
      Subtype.ext (by simp [← hd.order, pow_orderOf_eq_one])
    rw [ha, ← map_pow, h1, map_one]
  have hap : IsPGroup 3 (Subgroup.zpowers a) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one]; exact ha3)
  have hCP := compParab_of_blockHyps hyps
    (nineThreeTwo_of_not_inner_wPre hp hp2 hyps hrk hdvd hrkW hap haJ hnon)
  set N := barM M L with hNdef
  haveI hNn : N.Normal := hLn.map π (QuotientGroup.mk'_surjective _)
  set C := centralizer (N : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCdef
  obtain ⟨n, hn⟩ := hlie
  have hn1 : 1 ≤ n := by
    obtain ⟨-, ⟨q, -, hqe, -⟩, -⟩ := hn
    exact hqe ▸ q.exponent_pos
  obtain ⟨φ⟩ := h108 G M (pCoreOf 2 H) L hyps hQS n hn
  have hN2 := TenElevenOneLie.not_three_dvd_card_pCore_two ↥M
  have hrkY : 3 ≤ Open.pRank 3 (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥M) hN2,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup M]
    obtain ⟨H₁, R₁, hesc⟩ := hd.data.escape
    exact hesc.three_le_pRank.trans (CFSG.SectionRank.pRank_mono (by norm_num) hesc.le_M)
  have hJL : blockPL M (pCoreOf 2 H) L ≤ N :=
    fun x ⟨y, hy, hyx⟩ => ⟨y, (Subgroup.mem_inf.1 hy).2, hyx⟩
  have hpN : 3 ∣ Nat.card N :=
    hdvd.trans (Subgroup.card_dvd_of_le ((wPre_le _).trans hJL))
  have hH2 : ∀ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
      3 ≤ Open.pRank 3 (centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := by
    intro D hD hDc
    rcases Nat.even_or_odd n with hev | hodn
    · obtain ⟨e, f₀, hf, σ, hσ, g, hg⟩ :=
        SL3E27.exists_slPi_field_of_not_inner_wPre hCP hn1 φ hrkW ha3 haJ hnon
      haveI : Group.IsPerfect N := ⟨hCP.comp.2.2.1⟩
      have hK : PiField true 2 n (GaloisField 2 n) :=
        ⟨Nat.prime_two, hn1, GaloisField.card 2 n (by omega)⟩
      have hθ := SL3E27.aschbacherSolvableCore_eq_bot_of_mulEquiv hCP.comp.2.2 φ
      have hf₀ : Even f₀ := (Nat.even_mul.1 (hf ▸ hev)).resolve_left (by decide)
      obtain ⟨z, hz, hNz, hw⟩ := SL3E27.exists_commute_slThree hK (modThree_two_pow_of_even hev)
        hf (modThree_two_pow_of_even hf₀) hθ e ha3 hσ hg
      haveI : (zpowers z).Normal := by
        rw [← hNz]
        infer_instance
      exact SL3E27.three_le_pRank_centralizer_of_commute hz hw hD hDc
    · refine SL3E27.three_le_pRank_centralizer_of_inf_ne_bot (N := N) (C := C) hpN ?_ hrkY ?_
        hD hDc
      · refine eq_bot_iff.2 fun x hx => ?_
        have hxc : (⟨x, hx.1⟩ : N) ∈ Subgroup.center N := by
          rw [Subgroup.mem_center_iff]
          intro g
          apply Subtype.ext
          exact mem_centralizer_iff.1 hx.2 g g.2
        have h1 : φ ⟨x, hx.1⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3)
            (GaloisField 2 n)) := by
          rw [← Subgroup.map_center_eq φ]
          exact ⟨_, hxc, rfl⟩
        rw [SL3E27.center_eq_bot_of_odd hodn, Subgroup.mem_bot] at h1
        have h2 : (⟨x, hx.1⟩ : N) = 1 := φ.injective (by rw [h1, map_one])
        rw [Subgroup.mem_bot]
        exact congrArg Subtype.val h2
      · intro P' hP'
        have h1 := hodd _ N hNn n hodn ⟨φ⟩ P' P'.isPGroup' hP'
        have h2 := (CFSG.SectionRank.pRank_sylow P').1
        omega
  intro E hEM hE hEc
  set E' : Subgroup ↥M := E.subgroupOf M
  haveI := hE.1
  have hE' : IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · change ((a : ↥M) : G) * ((b : ↥M) : G) = ((b : ↥M) : G) * ((a : ↥M) : G)
      exact congrArg Subtype.val
        (mul_comm' (⟨_, mem_subgroupOf.mp a.2⟩ : E) ⟨_, mem_subgroupOf.mp b.2⟩)
    · simpa using hE.2 _ (mem_subgroupOf.mp hx)
  have hE'p : IsPGroup 3 E' := fun x => ⟨1, Subtype.ext (by simpa using hE'.2 _ x.2)⟩
  have hinj := CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype hN2 hE'p
  have hcard : Nat.card (E'.map π) = 3 ^ 2 := by
    have hrange : E'.map π = (π.comp E'.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hEM).toEquiv, hEc]
  have key := hH2 _ (CFSG.SectionRank.isElemAbelian_map hE' π) hcard
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hN2 hE'p] at key
  have h1 := TenElevenOneLie.pRank_map_le Nat.prime_three π (by rwa [QuotientGroup.ker_mk'])
    (centralizer (E' : Set ↥M))
  have h2 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) M.subtype
    M.subtype_injective (centralizer (E' : Set ↥M))
  have h3 : (centralizer (E' : Set ↥M)).map M.subtype ≤ centralizer (E : Set G) ⊓ M := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨mem_centralizer_iff.mpr fun e he => ?_, y.2⟩
    have := mem_centralizer_iff.mp hy ⟨e, hEM he⟩ (mem_subgroupOf.mpr he)
    exact congrArg Subtype.val this
  have h4 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) h3
  exact key.trans (h1.trans (h2.trans h4))

end CFSG.LocalAnalysis.RankThreeTheoremC
