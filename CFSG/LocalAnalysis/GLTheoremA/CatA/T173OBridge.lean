module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ODefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQChar2Index
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Tuple
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InnRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.KRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Arith2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Inn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Rigid
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporMathieu
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173InnDiagImage
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3ChevSimple
public import CFSG.Goldschmidt.Steps.G310Comp
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Defs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Arith
public import CFSG.Holt.Fixed
public import CFSG.LargeExtraspecial.S14Defs
public import CFSG.LargeExtraspecial.S14Inputs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Base
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescCTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIPComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieReduce
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Inputs
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.RankThree.PartOne.K159.AutCore
public import CFSG.RankThree.PartOne.K159.AutSzIso
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38K0
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.RankThree.ThinCatalog.EvenLinearTwoLocal
public import Certificates.Certificate14953
public import Certificates.Certificate8166

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.LocalAnalysis.GLTheoremA.T173X CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.HDesc
open scoped commutatorElement


private theorem rank_bound_of_raw
    {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S B : Subgroup Y} {x : Y} (hB : IsElemAbelian p B) (hB4 : p ^ 4 ≤ Nat.card B)
    (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hcent : ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Y) ↔ b ∈ Subgroup.zpowers x)
    (hS : commutator ↥S = ⊤) {lab : GLALabel} (hlab : GLAInLambda2 lab)
    {Q : CFSG.Assembly.LargeEvenRawCont} (hraw : GLARawDatum lab Q)
    (hdata : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F →
      ∃ θ : ↥S ⧸ Subgroup.center ↥S ≃* R,
        IsSimpleGroup R ∧ B ≤ Subgroup.normalizer (S : Set Y) ∧
        ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Y) = b⁻¹ * l * b) φ) :
    3 ≤ rk2Mult lab (rk2Ord p lab.n) := by
  have hRank : Rk2InnRank :=
    CFSG.LocalAnalysis.GLTheoremA.rk2InnRank_of_kRank CFSG.LocalAnalysis.GLTheoremA.rk2KRank
  have htab := hRank lab hlab trivial p hp hp2
  obtain ⟨R, hR, I, F, hQ, hbound⟩ := rk2_rawDatum_exists (htab _ hraw)
  obtain ⟨θ, hs, hN, hind⟩ := hdata R I F hQ
  obtain ⟨E, hEle, hEel, hEcard⟩ :=
    exists_elemAbelian_image_of_innerDiag hp hB hB4 hxB hx1 hcent hS θ hN hind
  have hb := hbound hs E hEle hEel
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 (hEcard.trans hb)


private theorem exists_marking_data
    {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) :
    ∃ (lab : GLALabel) (R : Type) (_ : Group R) (I F : Set (MulAut R))
      (θ : ↥S ⧸ Subgroup.center ↥S ≃* R),
      GLAInLambda2 lab ∧ GLASplit16 p lab ∧ MarkedModel lab R ∧ commutator ↥S = ⊤ ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      (∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ) ∧
      GLAMarking S (fun lab' _ _ I' _ θ' => lab' = lab ∧ GLASplit16 p lab' ∧
        B ≤ Subgroup.normalizer (S : Set Ω) ∧
        ∀ b ∈ B, ∃ φ ∈ I', GLAInduces θ' (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ) ∧
      3 ≤ rk2Mult lab (rk2Ord p lab.n) := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hcfg.split
  have hrawM := CFSG.StandardType.Canonical.largeEvenRawDatum_markedModel hlab
    (fun R _ I F hq => hq.2.1) hraw
  obtain ⟨R, hR, I, F, hQ, hM⟩ := rk2_rawDatum_exists hrawM
  obtain ⟨hs, hna, θ, hspl, hN, hind⟩ := hQ
  have h3 := rank_bound_of_raw hcfg.prime hcfg.odd hcfg.elem hcfg.four hcfg.mem hcfg.ne_one
    hcfg.cent hperf hlab hraw
    (by
      rintro R' _ I' F' ⟨hs', hna', θ', hspl', hN', hind'⟩
      exact ⟨θ', hs', hN', hind'⟩)
  refine ⟨lab, R, hR, I, F, θ, hlab, hspl, hM, hperf, hN, hind, ?_, h3⟩
  refine ⟨hperf, lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R' _ I' F' ⟨hs', hna', θ', hspl', hN', hind'⟩
  exact ⟨hs', hna', θ', rfl, hspl', hN', hind'⟩

private theorem rk2Mult_le_two_of_BC_rank_two {lab : GLALabel} (htag : lab.tag = .B ∨ lab.tag = .C)
    (hrank : lab.rank = 2) {m : ℕ} (hm : 0 < m) :
    rk2Mult lab m ≤ 2 := by
  obtain ⟨t, l, n⟩ := lab
  rcases htag with rfl | rfl <;> subst hrank <;> simp only [rk2Mult] <;> split_ifs with hm2
  · have hm2' : 2 ≤ m := by omega
    calc 2 * 2 / m ≤ 2 * 2 / 2 := Nat.div_le_div_left hm2' (by norm_num)
      _ = 2 := by norm_num
  · calc 2 / m ≤ 2 / 1 := Nat.div_le_div_left hm (by norm_num)
      _ = 2 := by norm_num
  · have hm2' : 2 ≤ m := by omega
    calc 2 * 2 / m ≤ 2 * 2 / 2 := Nat.div_le_div_left hm2' (by norm_num)
      _ = 2 := by norm_num
  · calc 2 / m ≤ 2 / 1 := Nat.div_le_div_left hm (by norm_num)
      _ = 2 := by norm_num

private theorem rk2Mult_le_two_of_small_tag {lab : GLALabel} {m : ℕ} (hm : 0 < m)
    (ht : lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
      lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) :
    rk2Mult lab m ≤ 2 :=
  CFSG.LocalAnalysis.GLTheoremA.rk2Mult_le_two_of_small ht hm

private theorem rk2Mult_A1_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hspl : GLASplit16 p (⟨.A, 1, 2⟩ : GLALabel)) :
    rk2Mult (⟨.A, 1, 2⟩ : GLALabel) (rk2Ord p 2) ≤ 2 := by
  have hdiv : p ∣ 2 ^ 2 - 1 := by
    simp only [GLASplit16, CFSG.Assembly.LargeEvenSplit16,
      CFSG.Assembly.LargeEvenUntwisted] at hspl
    rcases hspl with h | h | h | h
    · exact h.2
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · omega
  have hm0 : rk2Ord p 2 = 1 := rk2Ord_eq_one_iff.2 hdiv
  simp [rk2Mult, hm0]

private theorem rk2Mult_A2_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hspl : GLASplit16 p (⟨.A, 2, 1⟩ : GLALabel)) :
    rk2Mult (⟨.A, 2, 1⟩ : GLALabel) (rk2Ord p 1) ≤ 2 := by
  have hp3 : p = 3 := by
    simp only [GLASplit16, CFSG.Assembly.LargeEvenSplit16,
      CFSG.Assembly.LargeEvenUntwisted] at hspl
    rcases hspl with h | h | h | h
    · exact absurd (Nat.dvd_one.mp h.2) hp.ne_one
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · exact h.2
  subst hp3
  have hm0 : rk2Ord 3 1 = 2 := (rk2Ord_one_eq_two_iff Nat.prime_three (by norm_num)).2 rfl
  simp [rk2Mult, hm0]

private theorem rk2Mult_A3_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hspl : GLASplit16 p (⟨.A, 3, 1⟩ : GLALabel)) :
    rk2Mult (⟨.A, 3, 1⟩ : GLALabel) (rk2Ord p 1) ≤ 2 := by
  have hp3 : p = 3 := by
    simp only [GLASplit16, CFSG.Assembly.LargeEvenSplit16,
      CFSG.Assembly.LargeEvenUntwisted] at hspl
    rcases hspl with h | h | h | h
    · exact absurd (Nat.dvd_one.mp h.2) hp.ne_one
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · exact h.2
  subst hp3
  have hm0 : rk2Ord 3 1 = 2 := (rk2Ord_one_eq_two_iff Nat.prime_three (by norm_num)).2 rfl
  simp [rk2Mult, hm0]

private theorem rk2Mult_D3_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hspl : GLASplit16 p (⟨.D, 3, 1⟩ : GLALabel)) :
    rk2Mult (⟨.D, 3, 1⟩ : GLALabel) (rk2Ord p 1) ≤ 2 := by
  have hp3 : p = 3 := by
    simp only [GLASplit16, CFSG.Assembly.LargeEvenSplit16,
      CFSG.Assembly.LargeEvenUntwisted] at hspl
    rcases hspl with h | h | h | h
    · exact absurd (Nat.dvd_one.mp h.2) hp.ne_one
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · exact h.2
  subst hp3
  have hm0 : rk2Ord 3 1 = 2 := (rk2Ord_one_eq_two_iff Nat.prime_three (by norm_num)).2 rfl
  norm_num [rk2Mult, hm0]

private theorem rk2Mult_twD2_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hspl : GLASplit16 p (⟨.twD, 2, 1⟩ : GLALabel)) :
    rk2Mult (⟨.twD, 2, 1⟩ : GLALabel) (rk2Ord p 1) ≤ 2 := by
  have hp3 : p = 3 := by
    simp only [GLASplit16, CFSG.Assembly.LargeEvenSplit16,
      CFSG.Assembly.LargeEvenUntwisted] at hspl
    rcases hspl with h | h | h | h
    · exact absurd h.1 (by simp)
    · have := h.2.2.2
      norm_num at this
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this
    · exact absurd (Nat.dvd_one.mp h.2) hp.ne_one
    · exact h.2
  subst hp3
  have hm0 : rk2Ord 3 1 = 2 := (rk2Ord_one_eq_two_iff Nat.prime_three (by norm_num)).2 rfl
  norm_num [rk2Mult, hm0]

private theorem rk2Mult_le_two_of_linear_small {lab : GLALabel} {N f p : ℕ}
    (htag : lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .D ∨ lab.tag = .twD)
    (hm : markTag lab = .PSL) (hr : markRank lab = N) (hd : markDeg lab = f)
    (hNf : (N = 2 ∧ f = 2) ∨ (N = 3 ∧ f = 1) ∨ (N = 4 ∧ f = 1))
    (hp : p.Prime) (hp2 : p ≠ 2) (hspl : GLASplit16 p lab) :
    rk2Mult lab (rk2Ord p lab.n) ≤ 2 := by
  obtain ⟨t, r, n⟩ := lab
  rcases htag with rfl | rfl | rfl | rfl
  · rcases hNf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [markTag, markRank, markDeg] at hr hd
      have hr1 : r = 1 := by omega
      subst hr1
      subst hd
      exact rk2Mult_A1_two hp hp2 (by simpa using hspl)
    · simp only [markTag, markRank, markDeg] at hr hd
      have hr2 : r = 2 := by omega
      subst hr2
      subst hd
      exact rk2Mult_A2_one hp hp2 (by simpa using hspl)
    · simp only [markTag, markRank, markDeg] at hr hd
      have hr3 : r = 3 := by omega
      subst hr3
      subst hd
      exact rk2Mult_A3_one hp hp2 (by simpa using hspl)
  · simp only [markTag] at hm
    exact absurd hm (by decide)
  · by_cases h3 : r = 3
    · subst h3
      simp only [markRank, markDeg, if_true] at hr hd
      rcases hNf with hNf | hNf | hNf
      · omega
      · omega
      · obtain ⟨-, hf⟩ := hNf
        have hn : n = 1 := by omega
        subst hn
        subst hf
        exact rk2Mult_D3_one hp hp2 (by simpa using hspl)
    · simp only [markTag, h3, if_false] at hm
      exact absurd hm (by decide)
  · by_cases h2 : r = 2
    · subst h2
      simp only [markRank, markDeg, if_true] at hr hd
      rcases hNf with hNf | hNf | hNf
      · obtain ⟨-, hf⟩ := hNf
        have hn : n = 1 := by omega
        subst hn
        subst hf
        exact rk2Mult_twD2_one hp hp2 (by simpa using hspl)
      · omega
      · omega
    · simp only [markTag, h2, if_false] at hm
      split_ifs at hm
      all_goals exact absurd hm (by decide)


private theorem onLie_A_of_tagOf_eq_PSL {d : TauCeti.LieTypeIndex} (h : tagOf d = .PSL) :
    T173ClassA d := by
  cases d <;> simp [tagOf, T173ClassA] at h ⊢

private theorem onLie_A_of_tagOf_eq_PSU {d : TauCeti.LieTypeIndex} (h : tagOf d = .PSU) :
    T173ClassA d := by
  cases d <;> simp [tagOf, T173ClassA] at h ⊢

private theorem onLie_D_of_tagOf_eq_POmegaPlus {d : TauCeti.LieTypeIndex}
    (h : tagOf d = .POmegaPlus) : T173ClassD d := by
  cases d <;> simp [tagOf, T173ClassA, T173ClassD, T173ClassTD] at h ⊢

private theorem onLie_TD_of_tagOf_eq_POmegaMinus {d : TauCeti.LieTypeIndex}
    (h : tagOf d = .POmegaMinus) : T173ClassTD d := by
  cases d <;> simp [tagOf, T173ClassA, T173ClassD, T173ClassTD] at h ⊢

private theorem catalogIs_of_classical_markedModel {R : Type} [Group R] {lab : GLALabel} {p : ℕ}
    (hlab : GLAInLambda2 lab)
    (htag : lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .D ∨ lab.tag = .twD)
    (hM : MarkedModel lab R) (h3 : 3 ≤ rk2Mult lab (rk2Ord p lab.n))
    (hp : p.Prime) (hp2 : p ≠ 2) (hspl : GLASplit16 p lab) :
    (markTag lab = .PSL ∧ catalogIs R (onLie T173ClassA)) ∨
    (markTag lab = .PSU ∧ catalogIs R (onLie T173ClassA)) ∨
    (markTag lab = .POmegaPlus ∧ catalogIs R (onLie T173ClassD)) ∨
    (markTag lab = .POmegaMinus ∧ catalogIs R (onLie T173ClassTD)) := by
  obtain ⟨t, r, n⟩ := lab
  have hctag : markTag ⟨t, r, n⟩ ∈ CFSG.Blueprint.classicalTags := by
    rcases htag with rfl | rfl | rfl | rfl
    · simp [markTag, CFSG.Blueprint.classicalTags]
    · simp [markTag, CFSG.Blueprint.classicalTags]
    · simp only [markTag]
      split_ifs <;> simp [CFSG.Blueprint.classicalTags]
    · simp only [markTag]
      split_ifs <;> simp [CFSG.Blueprint.classicalTags]
  have hchar : markChar ⟨t, r, n⟩ = 2 := by
    rcases htag with rfl | rfl | rfl | rfl <;> simp [markChar]
  have hLM : CFSG.Blueprint.LieModel R (markTag ⟨t, r, n⟩) (markRank ⟨t, r, n⟩) 2
      (markDeg ⟨t, r, n⟩) := by
    simpa [CFSG.StandardType.MarkedModel, hchar] using hM
  have hSC : StatedClassicalModel R (markTag ⟨t, r, n⟩) (markRank ⟨t, r, n⟩) 2
      (markDeg ⟨t, r, n⟩) :=
    hLM.statedClassicalModel hctag
  rcases CFSG.LocalAnalysis.GLTheoremA.classical_two_cases hSC with
    ⟨d, hd2, ⟨eiso⟩⟩ | ⟨hm, hr, hd⟩ | ⟨hm, hr, hd⟩ | ⟨hm, hr, hd⟩
  · have hM' : MarkedModel ⟨t, r, n⟩ d.Group := MarkedModel.of_mulEquiv eiso hM
    have hLMd : CFSG.Blueprint.LieModel d.Group (tagOf d.1) (dimOf d.1) 2 d.1.fieldExponent :=
      CFSG.LocalAnalysis.GLTheoremA.HDesc.tupleLemma_holds d.Group d hd2 (MulEquiv.refl _)
    have hc6 : (⟨t, r, n⟩ : GLALabel).tag = .A ∨ (⟨t, r, n⟩ : GLALabel).tag = .twA ∨
        (⟨t, r, n⟩ : GLALabel).tag = .B ∨ (⟨t, r, n⟩ : GLALabel).tag = .C ∨
        (⟨t, r, n⟩ : GLALabel).tag = .D ∨ (⟨t, r, n⟩ : GLALabel).tag = .twD := by
      rcases htag with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    have htagEq : tagOf d.1 = markTag ⟨t, r, n⟩ :=
      (CFSG.LocalAnalysis.GLTheoremA.rk2_cls_det hlab hc6 hM' hLMd).1
    rcases htag with rfl | rfl | rfl | rfl
    · have hPSL : tagOf d.1 = .PSL := by simpa [markTag] using htagEq
      exact Or.inl ⟨by simp [markTag],
        ⟨.lie d, onLie_A_of_tagOf_eq_PSL hPSL, ⟨eiso⟩⟩⟩
    · have hPSU : tagOf d.1 = .PSU := by simpa [markTag] using htagEq
      exact Or.inr (Or.inl ⟨by simp [markTag],
        ⟨.lie d, onLie_A_of_tagOf_eq_PSU hPSU, ⟨eiso⟩⟩⟩)
    · by_cases h3r : r = 3
      · have hPSL : tagOf d.1 = .PSL := by simpa [markTag, h3r] using htagEq
        exact Or.inl ⟨by simp [markTag, h3r],
          ⟨.lie d, onLie_A_of_tagOf_eq_PSL hPSL, ⟨eiso⟩⟩⟩
      · have hP : tagOf d.1 = .POmegaPlus := by simpa [markTag, h3r] using htagEq
        exact Or.inr (Or.inr (Or.inl ⟨by simp [markTag, h3r],
          ⟨.lie d, onLie_D_of_tagOf_eq_POmegaPlus hP, ⟨eiso⟩⟩⟩))
    · by_cases h2r : r = 2
      · have hPSL : tagOf d.1 = .PSL := by simpa [markTag, h2r] using htagEq
        exact Or.inl ⟨by simp [markTag, h2r],
          ⟨.lie d, onLie_A_of_tagOf_eq_PSL hPSL, ⟨eiso⟩⟩⟩
      · by_cases h3r : r = 3
        · have hPSU : tagOf d.1 = .PSU := by simpa [markTag, h2r, h3r] using htagEq
          exact Or.inr (Or.inl ⟨by simp [markTag, h2r, h3r],
            ⟨.lie d, onLie_A_of_tagOf_eq_PSU hPSU, ⟨eiso⟩⟩⟩)
        · have hM'' : tagOf d.1 = .POmegaMinus := by
            simpa [markTag, h2r, h3r] using htagEq
          exact Or.inr (Or.inr (Or.inr ⟨by simp [markTag, h2r, h3r],
            ⟨.lie d, onLie_TD_of_tagOf_eq_POmegaMinus hM'', ⟨eiso⟩⟩⟩))
  · exfalso
    have hle := rk2Mult_le_two_of_linear_small htag hm hr hd (Or.inl ⟨rfl, rfl⟩) hp hp2 hspl
    omega
  · exfalso
    have hle := rk2Mult_le_two_of_linear_small htag hm hr hd (Or.inr (Or.inl ⟨rfl, rfl⟩))
      hp hp2 hspl
    omega
  · exfalso
    have hle := rk2Mult_le_two_of_linear_small htag hm hr hd (Or.inr (Or.inr ⟨rfl, rfl⟩))
      hp hp2 hspl
    omega


private theorem split_untwisted {p : ℕ} {lab : GLALabel} (hu : CFSG.Assembly.LargeEvenUntwisted lab.tag)
    (hspl : GLASplit16 p lab) : p ∣ 2 ^ lab.n - 1 ∨ (lab.n = 1 ∧ p = 3) := by
  obtain ⟨tg, r, n⟩ := lab
  rw [GLASplit16, CFSG.Assembly.LargeEvenSplit16] at hspl
  rcases hspl with h | h | h | h
  · exact Or.inl h.2
  · exact absurd hu h.1
  · rcases h.1 with h' | h' | h' | h'
    all_goals
      rw [h'] at hu
      simp [CFSG.Assembly.LargeEvenUntwisted] at hu
  · exact Or.inr h

private theorem split_twE6 {p : ℕ} {lab : GLALabel} (ht : lab.tag = .twE6)
    (hspl : GLASplit16 p lab) : p ∣ 2 ^ lab.n + 1 ∨ (lab.n = 1 ∧ p = 3) := by
  obtain ⟨tg, r, n⟩ := lab
  subst ht
  rw [GLASplit16, CFSG.Assembly.LargeEvenSplit16] at hspl
  rcases hspl with h | h | h | h
  · exact absurd h.1 (by simp [CFSG.Assembly.LargeEvenUntwisted])
  · exact Or.inl h.2.2.2
  · exact absurd h.1 (by simp)
  · exact Or.inr h

private theorem false_of_classical_markedModel {R : Type} [Group R] {lab : GLALabel} {p : ℕ}
    (hlab : GLAInLambda2 lab)
    (htag : lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .D ∨ lab.tag = .twD)
    (hM : MarkedModel lab R) (h3 : 3 ≤ rk2Mult lab (rk2Ord p lab.n))
    (hp : p.Prime) (hp2 : p ≠ 2) (hspl : GLASplit16 p lab)
    (hA : ¬ catalogIs R (onLie T173ClassA))
    (hD : ¬ catalogIs R (onLie T173ClassD)) (hTD : ¬ catalogIs R (onLie T173ClassTD)) : False := by
  rcases catalogIs_of_classical_markedModel hlab htag hM h3 hp hp2 hspl with
    ⟨-, hcat⟩ | ⟨-, hcat⟩ | ⟨-, hcat⟩ | ⟨-, hcat⟩
  · exact hA hcat
  · exact hA hcat
  · exact hD hcat
  · exact hTD hcat

theorem i173FactO_of_families (hExc : I173OOn famExcSplit) (hSp : I173OOn famSpSplit)
    (hThree : I173OOn famThree) (hTwE6 : I173OOn famTwE6) (hFive : I173OOn famFive) :
    T173.I173FactO := by
  intro p Ω _ _ S B N D K x hcfg hA hD hTD
  obtain ⟨lab, R, hR, I, F, θ, hlab, hspl, hM, hperf, hN, hind, hpinned, h3⟩ :=
    exists_marking_data hcfg
  have hnt : Nontrivial (PSimple p S) :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.isSimpleGroup_of_isChevSimple_two hcfg.chev).toNontrivial
  obtain ⟨ePZ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.HSubT.psimple_nonempty_equiv_quotCenter p S hcfg.qs hnt
  let ePR : PSimple p S ≃* R := ePZ.trans θ
  have hA' : ¬ catalogIs R (onLie T173ClassA) := fun hc => hA ((catalogIs_congr ePR).mpr hc)
  have hD' : ¬ catalogIs R (onLie T173ClassD) := fun hc => hD ((catalogIs_congr ePR).mpr hc)
  have hTD' : ¬ catalogIs R (onLie T173ClassTD) := fun hc => hTD ((catalogIs_congr ePR).mpr hc)
  obtain ⟨t, r, n⟩ := lab
  cases t
  ·
    exact (false_of_classical_markedModel hlab (Or.inl rfl) hM h3 hcfg.prime hcfg.odd hspl
      hA' hD' hTD').elim
  ·
    exact (false_of_classical_markedModel hlab (Or.inr (Or.inl rfl)) hM h3 hcfg.prime hcfg.odd
      hspl hA' hD' hTD').elim
  ·
    by_cases hr : r = 2
    · have hle := rk2Mult_le_two_of_BC_rank_two (lab := ⟨.B, r, n⟩) (Or.inl rfl)
        (by simpa using hr) (CFSG.LocalAnalysis.GLTheoremA.rk2Ord_pos hcfg.prime hcfg.odd n)
      have hle' : rk2Mult (⟨.B, r, n⟩ : GLALabel)
          (rk2Ord p (⟨.B, r, n⟩ : GLALabel).n) ≤ 2 := by simpa using hle
      omega
    · have hr3 : 3 ≤ r := by
        have h2r : 2 ≤ r := by simpa using hlab.2.1
        omega
      rcases split_untwisted (by simp [CFSG.Assembly.LargeEvenUntwisted]) hspl with hd | ⟨hn, hp3⟩
      · have hP : famSpSplit (⟨.B, r, n⟩ : GLALabel) p :=
          ⟨Or.inl rfl, hr3, by simpa using hd⟩
        exact hSp p Ω S B N D K x ⟨.B, r, n⟩ hcfg (by simpa using hlab) hP
          (by simpa using hpinned)
      · have hP : famThree (⟨.B, r, n⟩ : GLALabel) p :=
          ⟨Or.inl ⟨Or.inl rfl, hr3⟩, hn, hp3⟩
        exact hThree p Ω S B N D K x ⟨.B, r, n⟩ hcfg (by simpa using hlab) hP
          (by simpa using hpinned)
  ·
    by_cases hr : r = 2
    · have hle := rk2Mult_le_two_of_BC_rank_two (lab := ⟨.C, r, n⟩) (Or.inr rfl)
        (by simpa using hr) (CFSG.LocalAnalysis.GLTheoremA.rk2Ord_pos hcfg.prime hcfg.odd n)
      have hle' : rk2Mult (⟨.C, r, n⟩ : GLALabel)
          (rk2Ord p (⟨.C, r, n⟩ : GLALabel).n) ≤ 2 := by simpa using hle
      omega
    · have hr3 : 3 ≤ r := by
        have h2r : 2 ≤ r := by simpa using hlab.2.1
        omega
      rcases split_untwisted (by simp [CFSG.Assembly.LargeEvenUntwisted]) hspl with hd | ⟨hn, hp3⟩
      · have hP : famSpSplit (⟨.C, r, n⟩ : GLALabel) p :=
          ⟨Or.inr rfl, hr3, by simpa using hd⟩
        exact hSp p Ω S B N D K x ⟨.C, r, n⟩ hcfg (by simpa using hlab) hP
          (by simpa using hpinned)
      · have hP : famThree (⟨.C, r, n⟩ : GLALabel) p :=
          ⟨Or.inl ⟨Or.inr rfl, hr3⟩, hn, hp3⟩
        exact hThree p Ω S B N D K x ⟨.C, r, n⟩ hcfg (by simpa using hlab) hP
          (by simpa using hpinned)
  ·
    exact (false_of_classical_markedModel hlab (Or.inr (Or.inr (Or.inl rfl))) hM h3 hcfg.prime
      hcfg.odd hspl hA' hD' hTD').elim
  ·
    exact (false_of_classical_markedModel hlab (Or.inr (Or.inr (Or.inr rfl))) hM h3 hcfg.prime
      hcfg.odd hspl hA' hD' hTD').elim
  ·
    rcases split_untwisted (by simp [CFSG.Assembly.LargeEvenUntwisted]) hspl with hd | ⟨hn, hp3⟩
    · by_cases hp3' : p = 3
      · have hP : famFive (⟨.E6, r, n⟩ : GLALabel) p :=
          ⟨hp3', Or.inl ⟨rfl, by simpa [hp3'] using hd⟩⟩
        exact hFive p Ω S B N D K x ⟨.E6, r, n⟩ hcfg (by simpa using hlab) hP
          (by simpa using hpinned)
      · have hP : famExcSplit (⟨.E6, r, n⟩ : GLALabel) p :=
          ⟨Or.inr (Or.inl rfl), by simpa using hd, by simpa using hp3'⟩
        exact hExc p Ω S B N D K x ⟨.E6, r, n⟩ hcfg (by simpa using hlab) hP
          (by simpa using hpinned)
    · have hP : famThree (⟨.E6, r, n⟩ : GLALabel) p :=
        ⟨Or.inr (Or.inr (Or.inl rfl)), hn, hp3⟩
      exact hThree p Ω S B N D K x ⟨.E6, r, n⟩ hcfg (by simpa using hlab) hP
        (by simpa using hpinned)
  ·
    rcases split_untwisted (by simp [CFSG.Assembly.LargeEvenUntwisted]) hspl with hd | ⟨hn, hp3⟩
    · have hP : famExcSplit (⟨.E7, r, n⟩ : GLALabel) p :=
        ⟨Or.inr (Or.inr (Or.inl rfl)), by simpa using hd, by simp⟩
      exact hExc p Ω S B N D K x ⟨.E7, r, n⟩ hcfg (by simpa using hlab) hP
        (by simpa using hpinned)
    · have hP : famThree (⟨.E7, r, n⟩ : GLALabel) p :=
        ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), hn, hp3⟩
      exact hThree p Ω S B N D K x ⟨.E7, r, n⟩ hcfg (by simpa using hlab) hP
        (by simpa using hpinned)
  ·
    rcases split_untwisted (by simp [CFSG.Assembly.LargeEvenUntwisted]) hspl with hd | ⟨hn, hp3⟩
    · have hP : famExcSplit (⟨.E8, r, n⟩ : GLALabel) p :=
        ⟨Or.inr (Or.inr (Or.inr rfl)), by simpa using hd, by simp⟩
      exact hExc p Ω S B N D K x ⟨.E8, r, n⟩ hcfg (by simpa using hlab) hP
        (by simpa using hpinned)
    · have hP : famThree (⟨.E8, r, n⟩ : GLALabel) p :=
        ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))), hn, hp3⟩
      exact hThree p Ω S B N D K x ⟨.E8, r, n⟩ hcfg (by simpa using hlab) hP
        (by simpa using hpinned)
  ·
    rcases split_untwisted (by simp [CFSG.Assembly.LargeEvenUntwisted]) hspl with hd | ⟨hn, hp3⟩
    · have hP : famExcSplit (⟨.F4, r, n⟩ : GLALabel) p :=
        ⟨Or.inl rfl, by simpa using hd, by simp⟩
      exact hExc p Ω S B N D K x ⟨.F4, r, n⟩ hcfg (by simpa using hlab) hP
        (by simpa using hpinned)
    · have hP : famThree (⟨.F4, r, n⟩ : GLALabel) p :=
        ⟨Or.inr (Or.inl rfl), hn, hp3⟩
      exact hThree p Ω S B N D K x ⟨.F4, r, n⟩ hcfg (by simpa using hlab) hP
        (by simpa using hpinned)
  ·
    rcases split_twE6 rfl hspl with hd | ⟨hn, hp3⟩
    · by_cases hp3' : p = 3
      · have hP : famFive (⟨.twE6, r, n⟩ : GLALabel) p := ⟨hp3', Or.inr rfl⟩
        exact hFive p Ω S B N D K x ⟨.twE6, r, n⟩ hcfg (by simpa using hlab) hP
          (by simpa using hpinned)
      · have hP : famTwE6 (⟨.twE6, r, n⟩ : GLALabel) p := ⟨rfl, hp3'⟩
        exact hTwE6 p Ω S B N D K x ⟨.twE6, r, n⟩ hcfg (by simpa using hlab) hP
          (by simpa using hpinned)
    · have hP : famFive (⟨.twE6, r, n⟩ : GLALabel) p := ⟨hp3, Or.inr rfl⟩
      exact hFive p Ω S B N D K x ⟨.twE6, r, n⟩ hcfg (by simpa using hlab) hP
        (by simpa using hpinned)
  ·
    have hle := rk2Mult_le_two_of_small_tag (lab := ⟨.triD4, r, n⟩)
      (CFSG.LocalAnalysis.GLTheoremA.rk2Ord_pos hcfg.prime hcfg.odd n) (Or.inr (Or.inl rfl))
    have hle' : rk2Mult (⟨.triD4, r, n⟩ : GLALabel)
        (rk2Ord p (⟨.triD4, r, n⟩ : GLALabel).n) ≤ 2 := by simpa using hle
    omega
  ·
    have hle := rk2Mult_le_two_of_small_tag (lab := ⟨.G2, r, n⟩)
      (CFSG.LocalAnalysis.GLTheoremA.rk2Ord_pos hcfg.prime hcfg.odd n) (Or.inl rfl)
    have hle' : rk2Mult (⟨.G2, r, n⟩ : GLALabel)
        (rk2Ord p (⟨.G2, r, n⟩ : GLALabel).n) ≤ 2 := by simpa using hle
    omega
  ·
    have hle := rk2Mult_le_two_of_small_tag (lab := ⟨.twB2, r, n⟩)
      (CFSG.LocalAnalysis.GLTheoremA.rk2Ord_pos hcfg.prime hcfg.odd n)
      (Or.inr (Or.inr (Or.inl rfl)))
    have hle' : rk2Mult (⟨.twB2, r, n⟩ : GLALabel)
        (rk2Ord p (⟨.twB2, r, n⟩ : GLALabel).n) ≤ 2 := by simpa using hle
    omega
  ·
    have hle := rk2Mult_le_two_of_small_tag (lab := ⟨.twF4, r, n⟩)
      (CFSG.LocalAnalysis.GLTheoremA.rk2Ord_pos hcfg.prime hcfg.odd n)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have hle' : rk2Mult (⟨.twF4, r, n⟩ : GLALabel)
        (rk2Ord p (⟨.twF4, r, n⟩ : GLALabel).n) ≤ 2 := by simpa using hle
    omega
  ·
    have hle := rk2Mult_le_two_of_small_tag (lab := ⟨.B2der, r, n⟩)
      (CFSG.LocalAnalysis.GLTheoremA.rk2Ord_pos hcfg.prime hcfg.odd n)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    have hle' : rk2Mult (⟨.B2der, r, n⟩ : GLALabel)
        (rk2Ord p (⟨.B2der, r, n⟩ : GLALabel).n) ≤ 2 := by simpa using hle
    omega
  ·
    have hle := rk2Mult_le_two_of_small_tag (lab := ⟨.G2der, r, n⟩)
      (CFSG.LocalAnalysis.GLTheoremA.rk2Ord_pos hcfg.prime hcfg.odd n)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    have hle' : rk2Mult (⟨.G2der, r, n⟩ : GLALabel)
        (rk2Ord p (⟨.G2der, r, n⟩ : GLALabel).n) ≤ 2 := by simpa using hle
    omega
  ·
    have hle := rk2Mult_le_two_of_small_tag (lab := ⟨.twF4der, r, n⟩)
      (CFSG.LocalAnalysis.GLTheoremA.rk2Ord_pos hcfg.prime hcfg.odd n)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
    have hle' : rk2Mult (⟨.twF4der, r, n⟩ : GLALabel)
        (rk2Ord p (⟨.twF4der, r, n⟩ : GLALabel).n) ≤ 2 := by simpa using hle
    omega

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
