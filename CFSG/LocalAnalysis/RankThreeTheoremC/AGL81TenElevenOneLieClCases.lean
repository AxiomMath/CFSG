module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieCl
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepSix
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneSLThreeOdd
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FourSixteenPGroup
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRankOne
import CFSG.HardMathSupport.Cooperstein.StructureLie.ParabolicCase
import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroThreePerfectProof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup

@[expose] def KFactTripleAltSixHTwo : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → Open.IsQuasisimple ↥L →
    CFSG.pCore 2 Y = ⊥ → Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6)) →
    3 ∣ Nat.card (Subgroup.center ↥L) → Open.pRank 3 (⊤ : Subgroup Y) = 3 →
    ∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E = 9 →
      3 ≤ Open.pRank 3 (Subgroup.centralizer (E : Set Y))

@[expose] def KFactTenElevenOneLieAut : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → Open.IsQuasisimple ↥L →
    CFSG.pCore 2 Y = ⊥ → IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) →
    (∃ T J : Subgroup (↥L ⧸ Subgroup.center ↥L), IsSylowTwoOf T ⊤ ∧
      Subgroup.normalizer (T : Set _) ≤ J ∧ J ≠ Subgroup.normalizer (T : Set _) ∧ J ≠ ⊤) →
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (L : Set Y)) →
    Open.pRank 3 (⊤ : Subgroup Y) = 3 →
    (∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      Open.pRank 3 (Subgroup.centralizer (E : Set Y)) ≤ 2) →
    (∃ N : Subgroup Y, N.Normal ∧ N.index = 3) →
    ∃ e : ℕ, IsLieOver (↥L ⧸ Subgroup.center ↥L) (.A 2) 2 e

namespace LieClCases

open SL3E27

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]

theorem three_le_pRank_centralizer_of_inf_ne_bot_of_ne {N C : Subgroup Y} [N.Normal] [C.Normal]
    (hpN : p ∣ Nat.card N) (hNC : ∀ z ∈ N, z ∈ C → orderOf z ≠ p)
    (hrk : 3 ≤ Open.pRank p (⊤ : Subgroup Y))
    (hPC : ∀ P : Sylow p Y, (P : Subgroup Y) ⊓ C ≠ ⊥)
    {D : Subgroup Y} (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2) :
    3 ≤ Open.pRank p (centralizer (D : Set Y)) := by
  have hp1 := hp.out.one_lt
  have hDp : IsPGroup p D := IsPGroup.of_card hDc
  obtain ⟨P, hDP⟩ := hDp.exists_le_sylow
  have hPr : Open.pRank p (P : Subgroup Y) = Open.pRank p (⊤ : Subgroup Y) :=
    (CFSG.SectionRank.pRank_sylow P).1
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => by
    simpa using congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨z₁, hz₁C, hz₁P, hz₁p⟩ := exists_mem_centralizer_sylow_of_inf_ne_bot P C (hPC P)
  obtain ⟨z₂, hz₂N, hz₂P, hz₂p⟩ :=
    exists_mem_centralizer_sylow_of_inf_ne_bot P N (sylow_inf_ne_bot_of_dvd P hpN)
  have hz₂ : z₂ ∉ zpowers z₁ := fun h => hNC z₂ hz₂N ((zpowers_le.2 hz₁C) h) hz₂p
  by_cases hzD : z₁ ∈ D ∧ z₂ ∈ D
  ·
    set H := D ⊓ centralizer ((P : Subgroup Y) : Set Y)
    have hlt : zpowers z₁ < H := by
      refine lt_of_le_of_ne (zpowers_le.2 ⟨hzD.1, hz₁P⟩) fun h => hz₂ ?_
      rw [h]
      exact ⟨hzD.2, hz₂P⟩
    have hc1 := Subgroup.card_lt_of_lt hlt
    rw [Nat.card_zpowers, hz₁p] at hc1
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 (hDp.to_le (inf_le_left : H ≤ D))
    have hdvd : Nat.card H ∣ p ^ 2 := hDc ▸ Subgroup.card_dvd_of_le inf_le_left
    rw [hj] at hdvd hc1
    have hj2 : j ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hp1).1 hdvd
    have hj1 : 1 < j := (Nat.pow_lt_pow_iff_right hp1).1 (by simpa using hc1)
    have hHD : H = D := Subgroup.eq_of_le_of_card_ge inf_le_left (by
      rw [hDc, hj, show j = 2 by omega])
    have hPD : (P : Subgroup Y) ≤ centralizer (D : Set Y) := by
      intro g hg
      rw [mem_centralizer_iff]
      intro d hd
      rw [← hHD] at hd
      exact ((mem_centralizer_iff.1 hd.2) g hg).symm
    calc 3 ≤ Open.pRank p (P : Subgroup Y) := hPr ▸ hrk
      _ ≤ Open.pRank p (centralizer (D : Set Y)) := CFSG.SectionRank.pRank_mono hp1 hPD
  obtain ⟨z, hzP, hzp, hzD'⟩ : ∃ z, z ∈ centralizer ((P : Subgroup Y) : Set Y) ∧
      orderOf z = p ∧ z ∉ D := by
    by_cases h1 : z₁ ∈ D
    · exact ⟨z₂, hz₂P, hz₂p, fun h2 => hzD ⟨h1, h2⟩⟩
    · exact ⟨z₁, hz₁P, hz₁p, h1⟩
  have hzd : ∀ d ∈ D, d * z = z * d := fun d hd => (mem_centralizer_iff.1 hzP d (hDP hd))
  set s : Set Y := (D : Set Y) ∪ {z}
  have hcomm : s.Pairwise Commute := by
    rintro a (ha | rfl) b (hb | rfl) -
    · exact hDcomm a ha b hb
    · exact hzd a ha
    · exact (hzd b hb).symm
    · exact Commute.refl _
  have hexp : ∀ a ∈ s, a ^ p = 1 := by
    rintro a (ha | rfl)
    · exact hD.2 a ha
    · rw [← hzp, pow_orderOf_eq_one]
  set D' := closure s
  have hD'e : IsElemAbelian p D' :=
    ⟨isMulCommutative_closure hcomm, fun x hx =>
      FourSixteen.pow_eq_one_of_mem_closure hcomm hexp hx⟩
  have hD'C : D' ≤ centralizer (D : Set Y) := by
    rw [closure_le]
    rintro a (ha | rfl)
    · exact mem_centralizer_iff.2 fun d hd => hDcomm d hd a ha
    · exact mem_centralizer_iff.2 fun d hd => hzd d hd
  have hDD' : D < D' := by
    refine lt_of_le_of_ne (fun d hd => subset_closure (Or.inl hd)) fun h => hzD' ?_
    rw [h]
    exact subset_closure (Or.inr rfl)
  have hD'p : IsPGroup p D' := fun x => ⟨1, Subtype.ext (by simpa using hD'e.2 _ x.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hD'p
  have hlt := Subgroup.card_lt_of_lt hDD'
  rw [hDc, hk] at hlt
  have hk3 : 3 ≤ k := by
    have := (Nat.pow_lt_pow_iff_right hp1).1 hlt
    omega
  exact hk3.trans (CFSG.SectionRank.le_pRank hp1 hD'C hD'e hk)

end LieClCases

theorem kFactTenElevenOneLieCl_of_cases (hKC : RankOneCent.KFactCentralThreeClassical)
    (hPP : KFactParabolicPerfectThree) (hA6 : KFactTripleAltSixHTwo)
    (hB : KFactTenElevenOneLieAut) : KFactTenElevenOneLieCl := by
  intro Y _ _ L hLn hq hO hcl hJ hrk hE hN
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hLn
  obtain ⟨E, hEe, hEc, hEr⟩ := id hE
  have hH2 : ¬ ∀ D : Subgroup Y, IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
      3 ≤ Open.pRank 3 (centralizer (D : Set Y)) := fun h => by
    have := h E hEe (by rw [hEc]; norm_num)
    omega
  by_cases h3Z : 3 ∣ Nat.card (Subgroup.center ↥L)
  · rcases hKC ↥L hq hcl h3Z with he | h4 | ⟨d, q, hq2, hdq, ⟨e⟩⟩
    · exact absurd (fun D hD hDc =>
        hA6 Y L hLn hq hO he h3Z hrk D hD (by rw [hDc]; norm_num)) hH2
    · exfalso
      have h1 := CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L
      have h2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (le_top : L ≤ ⊤)
      omega
    · rcases hdq with hd | hd
      · exact ⟨q.exponent, d, ⟨q, hq2, rfl, hd⟩, ⟨e⟩⟩
      · exfalso
        obtain ⟨d, hv⟩ := d
        obtain rfl : d = .twistedA 2 q := hd
        have hM := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
        rw [hq2] at hM
        have hmax := CFSG.AGLEmbedding.LieOut.borelMaximal_of_model_psu_three hM
        obtain ⟨T, J, ⟨-, hT2, hTi⟩, hTJ, hJT, hJt⟩ := hJ
        change ¬ 2 ∣ T.relIndex ⊤ at hTi
        rw [Subgroup.relIndex_top_right] at hTi
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have h := hmax (hT2.toSylow hTi) J (by rw [IsPGroup.toSylow_coe]; exact hTJ) hJt
        rw [IsPGroup.toSylow_coe] at h
        exact hJT h
  · by_cases hall : ∀ P : Sylow 3 Y, (P : Subgroup Y) ⊓ centralizer (L : Set Y) ≠ ⊥
    · exfalso
      apply hH2
      have hO2L : pCoreOf 2 L = ⊥ := le_bot_iff.1
        ((CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (le_top : L ≤ ⊤)
          fun g _ => normalizer_eq_top (H := L) ▸ mem_top g).trans
          (by rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore, hO]))
      have hLbot : L ≠ ⊥ := by
        intro h
        haveI := hq.2.toNontrivial
        obtain ⟨x, y, hxy⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
        have h1 : ∀ w : ↥L, w = 1 := fun w =>
          Subtype.ext (Subgroup.mem_bot.1 (h ▸ w.2))
        exact hxy (by rw [h1 x, h1 y])
      have hLL : ⁅L, L⁆ = L := by
        rw [← Subgroup.map_subtype_commutator, hq.1, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      obtain ⟨T, hT⟩ := CFSG.HardMathSupport.Cooperstein.StructureLie.exists_isSylowTwoOf L
      have hpL : 3 ∣ Nat.card L :=
        hPP Y L L hq hO2L hcl ⟨le_rfl, T, hT, inf_le_left⟩ L le_rfl hLbot hLL
          (by rw [Subgroup.subgroupOf_self]; exact Subgroup.IsSubnormal.top)
      intro D hD hDc
      refine LieClCases.three_le_pRank_centralizer_of_inf_ne_bot_of_ne hpL ?_ (by omega) hall hD
        hDc
      intro z hzL hzC hz3
      apply h3Z
      have hzZ : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact mem_centralizer_iff.1 hzC g g.2
      have h := orderOf_dvd_natCard (⟨⟨z, hzL⟩, hzZ⟩ : Subgroup.center ↥L)
      simpa only [Subgroup.orderOf_mk, hz3] using h
    · push Not at hall
      obtain ⟨P, hP⟩ := hall
      have hC3 : ¬ 3 ∣ Nat.card (centralizer (L : Set Y)) := fun h =>
        SL3E27.sylow_inf_ne_bot_of_dvd P h hP
      exact hB Y L hLn hq hO hcl hJ hC3 hrk hE hN

end CFSG.LocalAnalysis.RankThreeTheoremC
