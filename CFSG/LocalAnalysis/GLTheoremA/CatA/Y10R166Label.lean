module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import Certificates.Certificate8026Base

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.StandardType

theorem hasLabel_of_rawDatum {J : Type} [Group J] {lab : GLALabel}
    (hJ : commutator J = ⊤) (hlab : GLAInLambda2 lab)
    (h : GLARawDatum lab fun R _ _ _ => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ Nonempty (J ⧸ Subgroup.center J ≃* R)) :
    HasLabel J (· = lab) := by
  refine ⟨hJ, lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ h
  rintro R _ I F ⟨hs, hna, ⟨θ⟩⟩
  exact ⟨hs, hna, θ, rfl⟩

theorem hasLabel_of_quasisimple_rawDatum {J : Type} [Group J] {lab : GLALabel}
    (hJ : CFSG.IsQuasisimple J) (hlab : GLAInLambda2 lab)
    (h : GLARawDatum lab fun R _ _ _ => Nonempty (J ⧸ Subgroup.center J ≃* R)) :
    HasLabel J (· = lab) := by
  refine hasLabel_of_rawDatum hJ.1.commutator_eq_top hlab ?_
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ h
  rintro R _ I F ⟨e⟩
  refine ⟨(MulEquiv.isSimpleGroup_congr e).1 hJ.2.1, ?_, ⟨e⟩⟩
  obtain ⟨a, b, hab⟩ := hJ.2.2
  exact ⟨e a, e b, fun heq => hab (e.injective (by rw [map_mul, map_mul, heq]))⟩

theorem hasLabel_of_statedClassicalModel_PSp {J : Type} [Group J] {m n : ℕ}
    (hJ : CFSG.IsQuasisimple J)
    (h : StatedClassicalModel (J ⧸ Subgroup.center J) .PSp m 2 n) :
    HasLabel J (· = ⟨.B, m, n⟩) := by
  obtain ⟨hp, hf, hm, hne⟩ := h.1
  have hlab : GLAInLambda2 ⟨.B, m, n⟩ := by
    simp only [CFSG.Assembly.LargeEvenInLambda2]
    refine ⟨hf, hm, ?_⟩
    intro hm2
    have hn1 : n ≠ 1 := by
      intro hn
      exact hne (by simp [hm2, hn])
    omega
  exact hasLabel_of_quasisimple_rawDatum hJ hlab
    (recipeSymplectic_of_statedClassicalModel h)

theorem hasLabel_of_statedClassicalModel_PSL {J : Type} [Group J] {r n : ℕ}
    (hJ : CFSG.IsQuasisimple J)
    (h : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL (r + 1) 2 n) :
    HasLabel J (· = ⟨.A, r, n⟩) := by
  obtain ⟨hp, hf, hr, hne2, hne3⟩ := h.1
  have hlab : GLAInLambda2 ⟨.A, r, n⟩ := by
    simp only [CFSG.Assembly.LargeEvenInLambda2]
    refine ⟨hf, by omega, ?_⟩
    intro hr1
    have hn1 : n ≠ 1 := by
      intro hn
      exact hne2 (by simp [hr1, hn])
    omega
  exact hasLabel_of_quasisimple_rawDatum hJ hlab
    (recipeLinear_of_statedClassicalModel h)

theorem hasLabel_of_statedClassicalModel_PSL4_D {J : Type} [Group J] {n : ℕ}
    (hJ : CFSG.IsQuasisimple J)
    (h : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 4 2 n) :
    HasLabel J (· = ⟨.D, 3, n⟩) := by
  obtain ⟨hp, hf, -⟩ := h.1
  have hlab : GLAInLambda2 ⟨.D, 3, n⟩ := by
    simp only [CFSG.Assembly.LargeEvenInLambda2]
    exact ⟨hf, by norm_num⟩
  refine hasLabel_of_quasisimple_rawDatum hJ hlab ?_
  simpa [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] using
    recipeLinear_of_statedClassicalModel h

theorem hasLabel_of_statedClassicalModel_PSU {J : Type} [Group J] {r n : ℕ}
    (hJ : CFSG.IsQuasisimple J)
    (h : StatedClassicalModel (J ⧸ Subgroup.center J) .PSU (r + 1) 2 n) :
    HasLabel J (· = ⟨.twA, r, n⟩) := by
  obtain ⟨hp, hf, hr, hne⟩ := h.1
  have hlab : GLAInLambda2 ⟨.twA, r, n⟩ := by
    simp only [CFSG.Assembly.LargeEvenInLambda2]
    refine ⟨hf, by omega, ?_⟩
    intro hr2
    have hn1 : n ≠ 1 := by
      intro hn
      exact hne (by simp [hr2, hn])
    omega
  exact hasLabel_of_quasisimple_rawDatum hJ hlab
    (recipeUnitary_of_statedClassicalModel h)

theorem hasLabel_of_statedClassicalModel_POmegaPlus {J : Type} [Group J] {m n : ℕ}
    (hJ : CFSG.IsQuasisimple J)
    (h : StatedClassicalModel (J ⧸ Subgroup.center J) .POmegaPlus m 2 n) :
    HasLabel J (· = ⟨.D, m, n⟩) := by
  obtain ⟨hp, hf, hm⟩ := h.1
  have hm3 : m ≠ 3 := by omega
  have hlab : GLAInLambda2 ⟨.D, m, n⟩ := by
    simp only [CFSG.Assembly.LargeEvenInLambda2]
    exact ⟨hf, by omega⟩
  refine hasLabel_of_quasisimple_rawDatum hJ hlab ?_
  simpa [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, if_neg hm3] using
    recipeOmegaPlus_of_statedClassicalModel h

theorem hasLabel_of_statedClassicalModel_POmegaMinus {J : Type} [Group J] {m n : ℕ}
    (hJ : CFSG.IsQuasisimple J)
    (h : StatedClassicalModel (J ⧸ Subgroup.center J) .POmegaMinus m 2 n) :
    HasLabel J (· = ⟨.twD, m, n⟩) := by
  obtain ⟨hp, hf, hm⟩ := h.1
  have hm2 : m ≠ 2 := by omega
  have hm3 : m ≠ 3 := by omega
  have hlab : GLAInLambda2 ⟨.twD, m, n⟩ := by
    simp only [CFSG.Assembly.LargeEvenInLambda2]
    exact ⟨hf, by omega⟩
  refine hasLabel_of_quasisimple_rawDatum hJ hlab ?_
  simpa [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, if_neg hm2, if_neg hm3] using
    recipeOmegaMinus_of_statedClassicalModel h

section LabelUniqueness

theorem label_eq_or_BC {K : Type} [Group K] [Finite K] (he : 4 ≤ evenRank K)
    {lab₁ lab₂ : GLALabel} (h₁ : HasLabel K (fun l => l = lab₁))
    (h₂ : HasLabel K (fun l => l = lab₂)) :
    lab₁ = lab₂ ∨ ((lab₁.tag = .B ∨ lab₁.tag = .C) ∧
      (lab₂.tag = .B ∨ lab₂.tag = .C) ∧ lab₁.rank = lab₂.rank ∧ lab₁.n = lab₂.n) := by
  have htop : 4 ≤ evenRank ↥(⊤ : Subgroup K) :=
    he.trans (CFSG.RankThree.PartOne.Census3.evenRank_le_of_mulEquiv
      (Subgroup.topEquiv : ↥(⊤ : Subgroup K) ≃* K).symm)
  have h₁' : LabelOf (⊤ : Subgroup K) lab₁ :=
    (hasLabel_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup K) ≃* K)
      (fun l => l = lab₁)).2 h₁
  have h₂' : LabelOf (⊤ : Subgroup K) lab₂ :=
    (hasLabel_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup K) ≃* K)
      (fun l => l = lab₂)).2 h₂
  exact labelUniqAt_holds K ⊤ lab₁ lab₂ htop h₁' h₂'

end LabelUniqueness

end CFSG.LocalAnalysis.GLTheoremA.Y10F
