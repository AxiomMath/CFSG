module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Main
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.G2EvenOuterTypeDet
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.S11d.OddOutPSL2
public import CFSG.RankThree.PartOne.S11d.OutEsix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HG2Inn

open CFSG.Assembly CFSG.StandardType CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA

section Certs


theorem markedModel_g2_of_catalog {S : Type} [Group S] {n : ℕ}
    (h : catalogIs S (S10.isG2n n)) : 2 ≤ n ∧ MarkedModel ⟨.G2, 0, n⟩ S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | G2 q =>
      obtain ⟨hp, hf⟩ : q.p = 2 ∧ q.exponent = n := hi
      have h3 : 3 ≤ q.card :=
        (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      have h3' : 3 ≤ 2 ^ n := by
        have h := h3
        rw [TauCeti.PrimePower.card_def, hp, hf] at h
        exact h
      have hn2 : 2 ≤ n := by
        rcases Nat.lt_or_ge n 2 with hlt | hge
        · interval_cases n <;> norm_num at h3'
        · exact hge
      refine ⟨hn2, ?_⟩
      have h3q : 3 ≤ q.p ^ q.exponent := by
        rw [← TauCeti.PrimePower.card_def]
        exact h3
      have hstd : CFSG.Open.StatedLieAdmissible .G2 0 q.p q.exponent :=
        ⟨q.prime_p, q.exponent_pos, rfl, h3q⟩
      have hM : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2 0 q.p q.exponent :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_lie hstd ⟨.G2 q, hv⟩ ⟨rfl, rfl⟩
      have hM' := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.models_lieModel_of_mulEquiv e.symm hM
      have hB := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hM'
      rw [hp, hf] at hB
      exact hB
    | _ => exact hi.elim
  | _ => exact hi.elim

theorem tag_eq_G2_of_markTag {lab : LargeEvenLabel} (h : markTag lab = .G2) : lab.tag = .G2 := by
  obtain ⟨tg, r, m⟩ := lab
  cases tg <;> first | rfl | (dsimp only [markTag] at h; (try split_ifs at h) <;> cases h)

theorem label_eq_g2_of_char_two {R : Type} [Group R] {lab : LargeEvenLabel} {n : ℕ}
    (hl : CFSG.Assembly.LargeEvenInLambda2 lab) (hc : markChar lab = 2)
    (hM : MarkedModel lab R) (hG : MarkedModel ⟨.G2, 0, n⟩ R) : lab = ⟨.G2, 0, n⟩ := by
  have hm2 : CFSG.Blueprint.LieModel R (markTag lab) (markRank lab) 2 (markDeg lab) := by
    unfold MarkedModel at hM
    rwa [hc] at hM
  have hG2 : CFSG.Blueprint.LieModel R .G2 0 2 n := hG
  obtain ⟨ht, hg⟩ := CFSG.EvenSporadicStandard.Induction.lieModel_G2_two_unique hG2 hm2
  obtain ⟨tg, r, m⟩ := lab
  have htag : tg = .G2 := tag_eq_G2_of_markTag (lab := ⟨tg, r, m⟩) ht
  subst htag
  have hm : m = n := hg
  have hr : r = 0 := hl.2.1
  subst hm hr
  rfl

theorem false_of_char_three {R : Type} [Group R] {lab : LargeEvenLabel} {n : ℕ}
    (hl : CFSG.Assembly.LargeEvenInLambda2 lab) (hc : markChar lab ≠ 2)
    (hM : MarkedModel lab R) (hG : MarkedModel ⟨.G2, 0, n⟩ R) : False := by
  have hG2 : CFSG.Blueprint.LieModel R .G2 0 2 n := hG
  have hdvd := CFSG.EvenSporadicStandard.Induction.two_pow_twelve_dvd_card_of_lieModel_G2 hG2
  obtain ⟨tg, r, m⟩ := lab
  have hc3 : tg = .B2der ∨ tg = .G2der := by
    cases tg <;> simp_all [markChar]
  rcases hc3 with rfl | rfl
  · obtain ⟨-, hr, hm1⟩ : 1 ≤ m ∧ r = 0 ∧ m = 1 := hl
    subst hr hm1
    have h360 := card_of_B2der hM
    rw [h360] at hdvd
    omega
  · obtain ⟨-, hr, hm1⟩ : 1 ≤ m ∧ r = 0 ∧ m = 1 := hl
    subst hr hm1
    have h6048 := card_of_G2der hM
    rw [h6048] at hdvd
    omega

theorem label_eq_g2 {R : Type} [Group R] {lab : LargeEvenLabel} {n : ℕ}
    (hl : CFSG.Assembly.LargeEvenInLambda2 lab) (hM : MarkedModel lab R) (hG : MarkedModel ⟨.G2, 0, n⟩ R) :
    lab = ⟨.G2, 0, n⟩ := by
  by_cases hc : markChar lab = 2
  · exact label_eq_g2_of_char_two hl hc hM hG
  · exact (false_of_char_three hl hc hM hG).elim

theorem g2Datum_of_marking {L : Type} [Group L] {n : ℕ}
    (hG : catalogIs (L ⧸ Subgroup.center L) (S10.isG2n n)) {P : CFSG.Assembly.LargeEvenMarkProp L}
    (hM : CFSG.Assembly.LargeEvenMarking L P) :
    2 ≤ n ∧ CFSG.Assembly.LargeEvenRawDatum ⟨.G2, 0, n⟩ (fun R _ I F => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ ∃ θ : L ⧸ Subgroup.center L ≃* R, P ⟨.G2, 0, n⟩ R I F θ) := by
  obtain ⟨hn2, hG2⟩ := markedModel_g2_of_catalog hG
  obtain ⟨-, lab, hlab, hraw⟩ := CFSG.StandardType.Canonical.largeEvenMarking_markedModel hM
  obtain ⟨R, _, I, F, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, -, hm⟩ := hQ
  have hL : MarkedModel lab (L ⧸ Subgroup.center L) := MarkedModel.of_mulEquiv θ.symm hm
  have key : lab = ⟨.G2, 0, n⟩ := label_eq_g2 hlab hL hG2
  subst key
  refine ⟨hn2, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun R _ I F hq => ⟨hq.1, hq.2.1, ?_⟩) hraw⟩
  obtain ⟨θ', hP, -⟩ := hq.2.2
  exact ⟨θ', hP⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.HG2Inn

end
