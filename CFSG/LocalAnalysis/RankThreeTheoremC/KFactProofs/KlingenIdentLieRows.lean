module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Chev
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Defs
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Defs
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieAux

open CFSG.Open CFSG.AGLEmbedding CFSG.PreuniquenessRankFour.Helpers
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.RankThreeTheoremC

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
  {Y₀ : Subgroup Y} {K : Subgroup Y}

theorem exists_sylow_map_eq_inf (hK : IsComponentOf K ⊤) :
    ∃ T : Sylow p K, (T : Subgroup K).map K.subtype = (Rb : Subgroup Y) ⊓ K :=
  CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)

theorem ree_false (hschur : KFactReeSchur) (hsyl : KFactReeSylowElemAbelian)
    (hred : ReducedNongeneration p Y Rb Y₀) (hrank : Open.pRank p (Rb : Subgroup Y) = 3)
    (hK : IsComponentOf K ⊤) {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex p d)
    (e₁ : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  obtain ⟨hp3, -⟩ := hd.exists_eq
  subst hp3
  have hZ : Subgroup.center K = ⊥ := hschur K d hd hK.2.2 (isPGroup_center hred hK) ⟨e₁⟩
  have eK : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  obtain ⟨T₀, hT₀⟩ := exists_sylow_map_eq_inf (Rb := Rb) hK
  obtain ⟨E, hET, hE, hEcard⟩ := hsyl K d hd ⟨eK.trans e₁⟩ T₀
  have hER : E.map K.subtype ≤ (Rb : Subgroup Y) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hT₀.le ⟨x, hET hx, rfl⟩).1
  have hge : 2 * d.1.fieldExponent ≤ Open.pRank 3 (Rb : Subgroup Y) :=
    le_csSup (pRank_bddAbove 3 Nat.prime_three _) ⟨_, hER, elementary_abelian_map 3 hE _, by
      rw [Subgroup.card_map_of_injective K.subtype_injective, hEcard]⟩
  have := hd.three_le_fieldExponent
  omega

theorem unitary_false (hKU1 : KFactUnitarySchur) (hKU2 : KFactUnitarySylowStructure)
    (hKU9 : KFactUnitaryAutElemRank) (hred : ReducedNongeneration p Y Rb Y₀)
    (hrank : Open.pRank p (Rb : Subgroup Y) = 3) (hK : IsComponentOf K ⊤) (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d)
    (e₁ : K ⧸ Subgroup.center K ≃* CatGroup d) : False := by
  have hp : p.Prime := Fact.out
  have hZ : Subgroup.center K = ⊥ := hKU1 K p d hd hK.2.2 (isPGroup_center hred hK) ⟨e₁⟩
  have eK : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hL : Nonempty (K ≃* CatGroup d) := ⟨eK.trans e₁⟩
  have hinj : Function.Injective (MulAut.conjNormal (H := K) : Y →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal_eq_centralizer,
      centralizer_eq_bot hred hKn hcent hZ]
  have hle : Open.pRank p (Rb : Subgroup Y) ≤ 2 * d.1.fieldExponent := by
    apply csSup_le'
    rintro k ⟨E, -, hE, hcard⟩
    have h := hKU9 K p d hd hL (E.map MulAut.conjNormal) (elementary_abelian_map p hE _)
    rw [Subgroup.card_map_of_injective hinj, hcard] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  obtain ⟨T₀, hT₀⟩ := exists_sylow_map_eq_inf (Rb := Rb) hK
  obtain ⟨-, -, -, E, hET, hE, hEcard⟩ := hKU2 K p d hred.ne_two hd hL T₀
  have hER : E.map K.subtype ≤ (Rb : Subgroup Y) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hT₀.le ⟨x, hET hx, rfl⟩).1
  have hge : 2 * d.1.fieldExponent ≤ Open.pRank p (Rb : Subgroup Y) :=
    le_csSup (pRank_bddAbove p hp _) ⟨_, hER, elementary_abelian_map p hE _, by
      rw [Subgroup.card_map_of_injective K.subtype_injective, hEcard]⟩
  omega

theorem linTwo_false (hred : ReducedNongeneration p Y Rb Y₀)
    (hrank : Open.pRank p (Rb : Subgroup Y) = 3) (hK : IsComponentOf K ⊤) (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    (hkl : HasKlingenData p Rb Y₀) {n : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : IsLinTwoIndex p n d) (e₁ : K ⧸ Subgroup.center K ≃* CatGroup d) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hred.ne_two
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hn1 : 1 ≤ n := by
    obtain ⟨q, -, -, hqn⟩ := hd
    rw [← hqn]
    exact q.exponent_pos
  obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have hZ : Subgroup.center K = ⊥ :=
    center_eq_bot_of_center_quotient_psl2 hp2 (by omega) (card_ne_nine_of_isLinTwoIndex hd) hK.2.2
      (isPGroup_center hred hK) (e₁.trans eP)
  have eK : K ≃* PSL2GF p n :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans (e₁.trans eP)
  have hC := centralizer_eq_bot hred hKn hcent hZ
  obtain ⟨hUab, hUcard⟩ := isElemAbelian_sylow_inf_of_psl2GF hn1 eK Rb
  have hge : n ≤ Open.pRank p ((Rb : Subgroup Y) ⊓ K : Subgroup Y) :=
    le_csSup (pRank_bddAbove p hp _) ⟨_, le_rfl, hUab, hUcard⟩
  have hmono := pRank_mono p hp (inf_le_left : (Rb : Subgroup Y) ⊓ K ≤ Rb)
  have hn3 : n ≤ 3 := by omega
  have hRb : Nat.card (Rb : Subgroup Y) ∣ p ^ n * n :=
    card_dvd_of_isPGroup_of_psl2GF kFactL2AutPCard hp2 hn1 hKn ⟨eK⟩ hC _ Rb.isPGroup'
  have hlt : Nat.card (Rb : Subgroup Y) <
      p ^ 2 * Nat.card ((Rb : Subgroup Y) ⊓ K : Subgroup Y) := by
    rw [hUcard]
    have h1 : Nat.card (Rb : Subgroup Y) ≤ p ^ n * n :=
      Nat.le_of_dvd (Nat.mul_pos (pow_pos hp.pos n) hn1) hRb
    have h2 : 9 ≤ p ^ 2 := by nlinarith
    have h3 : p ^ n * n < p ^ n * 9 :=
      Nat.mul_lt_mul_of_pos_left (by omega) (pow_pos hp.pos n)
    calc Nat.card (Rb : Subgroup Y) ≤ p ^ n * n := h1
      _ < p ^ n * 9 := h3
      _ ≤ p ^ n * p ^ 2 := Nat.mul_le_mul_left _ h2
      _ = p ^ 2 * p ^ n := mul_comm _ _
  have hidx : ¬ p ^ 2 ∣ K.index :=
    haveI := hKn
    not_sq_dvd_index_of_card_lt K hlt
  refine false_of_comm_of_klingen hKn (by rw [hC]; infer_instance)
    (by rw [hC, sup_bot_eq]; exact hidx) (fun a ha b hb => ?_) hkl
  exact congrArg Subtype.val ((isMulCommutative_iff.mp hUab.1) ⟨a, ha⟩ ⟨b, hb⟩)

theorem chevTwo_cases (hin : KFactChevTwoInnerRank) (hout : KFactChevTwoOuterGen)
    (hred : ReducedNongeneration p Y Rb Y₀) (hrank : Open.pRank p (Rb : Subgroup Y) = 3)
    (hK : IsComponentOf K ⊤) (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsP1ChevTwoIndex p d)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    (p = 3 ∧ IsSpSixTwoIndex d) ∨ (p = 3 ∧ IsSpFourEightIndex d) ∨ (p = 3 ∧ IsGTwoEightIndex d) ∨
      (p = 5 ∧ IsReeFFourFiveIndex d) := by
  have hinner : p = 3 → IsChevTwoInnerIndex d → False := by
    rintro rfl hdi
    obtain ⟨T⟩ : Nonempty (Sylow 3 K) := inferInstance
    have h4 := hin d hdi K hK.2.2 e (isPGroup_center hred hK) (hred.isCyclic_center hK hKn) T
    have h3 := pRank_sylow_le_three hrank T
    omega
  have houter : p = 3 → IsChevTwoOuterIndex d → False := by
    rintro rfl hdo
    obtain ⟨e'⟩ := e
    exact false_of_le_weakCore hred hK hKn hcent e' (hout.1 d hdo)
      (hout.2 d hdo _ K hKn hK.2.2 ⟨e'⟩ (isPGroup_centralizer hred hKn hcent)
        (mem_center_of_mem_centralizer hKn hcent) Rb hred.three_le_pRank)
  rcases hd with ⟨hp, q, hq, hq1, h' | h' | h' | h' | h' | h' | h' | h'⟩ |
    ⟨hp, q, hq, hq3, h' | h' | h' | h'⟩ | ⟨hp, h'⟩
  · exact Or.inl ⟨hp, q, hq, hq1, h'⟩
  · exact (hinner hp ⟨q, hq, hq1, Or.inl h'⟩).elim
  · exact (hinner hp ⟨q, hq, hq1, Or.inr (Or.inl h')⟩).elim
  · exact (hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inl h'))⟩).elim
  · exact (hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inl h')))⟩).elim
  · exact (hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))⟩).elim
  · exact (hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))⟩).elim
  · exact (houter hp (Or.inl ⟨q, hq, hq1, h'⟩)).elim
  · exact Or.inr (Or.inl ⟨hp, q, hq, hq3, h'⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hp, q, hq, hq3, h'⟩))
  · exact (houter hp (Or.inr ⟨q, hq, hq3, Or.inl h'⟩)).elim
  · exact (houter hp (Or.inr ⟨q, hq, hq3, Or.inr h'⟩)).elim
  · exact Or.inr (Or.inr (Or.inr ⟨hp, h'⟩))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieAux
