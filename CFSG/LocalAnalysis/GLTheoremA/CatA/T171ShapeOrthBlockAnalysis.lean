module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthBlockModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCD
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutUnitary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.Classical2 CFSG.SeitzReduction.OmegaPilot
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def OrthCompMatrixAnalysisPlus : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (m n : ℕ)
    (K : Type) [Field K] [Finite K] (x y : ProjOrthDerived (quadPlus m K))
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* ProjOrthDerived (quadPlus m K))
    (hS : Setup p L J A d b),
    Nat.card K = 2 ^ n → 4 ≤ m →
    LargeEvenInduces θ (conjRel d) (MulAut.conj x) →
    LargeEvenInduces θ (conjRel b) (MulAut.conj y) →
    x ^ p = 1 → y ^ p = 1 → x * y = y * x →
    b ∉ Subgroup.zpowers d → b ∉ Subgroup.centralizer (J : Set G) →
    (catalogIs (PSimple p J) (onLie isLinearCharTwoIdx) ∧
        MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J)) ∨
      (catalogIs (PSimple p J) (onLie isUnitaryCharTwoIdx) ∧
        MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J)) ∨
      InducesInnerMod p J b

@[expose] def OrthCompMatrixAnalysisMinus : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (m n : ℕ)
    (K : Type) [Field K] [Finite K] (b₀ c₀ : K) (x y : ProjOrthDerived (quadMinus m K b₀ c₀))
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* ProjOrthDerived (quadMinus m K b₀ c₀))
    (hS : Setup p L J A d b),
    Nat.card K = 2 ^ n → 4 ≤ m → (∀ s : K, s ^ 2 + b₀ * s + c₀ ≠ 0) →
    LargeEvenInduces θ (conjRel d) (MulAut.conj x) →
    LargeEvenInduces θ (conjRel b) (MulAut.conj y) →
    x ^ p = 1 → y ^ p = 1 → x * y = y * x →
    b ∉ Subgroup.zpowers d → b ∉ Subgroup.centralizer (J : Set G) →
    (catalogIs (PSimple p J) (onLie isLinearCharTwoIdx) ∧
        MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J)) ∨
      (catalogIs (PSimple p J) (onLie isUnitaryCharTwoIdx) ∧
        MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J)) ∨
      InducesInnerMod p J b

theorem innerCompData_orth_charTwo_of_matrixAnalysis
    (hP : OrthCompMatrixAnalysisPlus) (hM : OrthCompMatrixAnalysisMinus) :
    InnerCompData fun i => isOrthDIdx i ∧ i.characteristic = 2 := by
  intro G _ _ p L J A d b hS hcat _hshape _hin hbz hbJ
  unfold OrthCompMatrixAnalysisPlus at hP
  unfold OrthCompMatrixAnalysisMinus at hM
  rcases exists_orthDModel_or_twistedDModel hcat with ⟨m, n, hcatD⟩ | ⟨m, n, hcatTD⟩
  · have hLM : CFSG.Blueprint.LieModel (PSimple p L) .POmegaPlus m 2 n :=
      lieModel_of_catalogIs_D hcatD
    have hm4 : 4 ≤ m := four_le_of_lieModel_POmega (Or.inl rfl) hLM
    obtain ⟨K, hKfield, hKfinite, hKcard, θ, x, y, hx, hy, hxp, hyp, hxy, -⟩ :=
      orthModelData_plus hS hcatD hm4
    letI := hKfield
    letI := hKfinite
    exact hP p L J A d b m n K x y θ hS hKcard hm4 hx hy hxp hyp hxy hbz hbJ
  · have hLM : CFSG.Blueprint.LieModel (PSimple p L) .POmegaMinus m 2 n :=
      lieModel_of_catalogIs_twistedD hcatTD
    have hm4 : 4 ≤ m := four_le_of_lieModel_POmega (Or.inr rfl) hLM
    obtain ⟨K, hKfield, hKfinite, hKcard, b₀, c₀, hbc, θ, x, y, hx, hy, hxp, hyp, hxy, -⟩ :=
      orthModelData_minus hS hcatTD hm4
    letI := hKfield
    letI := hKfinite
    exact hM p L J A d b m n K b₀ c₀ x y θ hS hKcard hm4 hbc hx hy hxp hyp hxy hbz hbJ

theorem innerCompNonShape_orth_charTwo_of_compData
    (hLin : InnAutDerivedInnDiag fun i =>
      ∃ (n : ℕ) (q : TauCeti.PrimePower), i = .A n q ∧ q.p = 2)
    (hUni : InnAutDerivedInnDiag fun i =>
      ∃ (n : ℕ) (q : TauCeti.PrimePower), i = .twistedA n q ∧ q.p = 2)
    (hAux : InnerCompData fun i => isOrthDIdx i ∧ i.characteristic = 2) :
    InnerCompNonShape fun i => isOrthDIdx i ∧ i.characteristic = 2 := by
  intro G _ _ p L J A d b hS hcat hshape hin
  have hqJ : CFSG.IsQuasisimple (PQuot p J) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr
        (isQuasisimple_pQuot_of_glaPComponent hS.prime hS.pcomp))
  by_cases hbz : b ∈ Subgroup.zpowers d
  · exact innDiagOn_zpowers_of_mem_zpowers hS.prime hS.pcomp hS.chevJ hS.b_norm
      (hS.comp.1.1.trans inf_le_right) hbz
  by_cases hbJ : b ∈ Subgroup.centralizer (J : Set G)
  · exact innDiagOn_of_mem_centralizer hS.prime hS.pcomp hS.chevJ hS.b_norm hbJ
  · rcases hAux p L J A d b hS hcat hshape hin hbz hbJ with
      ⟨htype, hmem⟩ | ⟨htype, hmem⟩ | hi
    · exact hLin p J b hS.b_norm hS.prime hqJ htype hmem
    · exact hUni p J b hS.b_norm hS.prime hqJ htype hmem
    · exact CFSG.LocalAnalysis.GLTheoremA.MI.inner_innDiag_holds hS.prime hS.pcomp hS.chevJ
        hS.b_norm hi

theorem innerCompNonShape_orth_charTwo_of_matrixAnalysis
    (hP : OrthCompMatrixAnalysisPlus) (hM : OrthCompMatrixAnalysisMinus) :
    InnerCompNonShape fun i => isOrthDIdx i ∧ i.characteristic = 2 :=
  innerCompNonShape_orth_charTwo_of_compData innAutDerivedInnDiag_linear
    innAutDerivedInnDiag_unitary (innerCompData_orth_charTwo_of_matrixAnalysis hP hM)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
