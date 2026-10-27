module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtBd
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutNF
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.IVK.L2.BN
public import CFSG.GH74.GLS.IVK.L2.BorelFive
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma114
public import CFSG.GH74.GLS.IVK.L2.Lemma12ib
public import CFSG.GH74.GLS.IVK.L2.Lemma12j
public import CFSG.GH74.GLS.IVK.L2.Lemma13fc
public import CFSG.GH74.GLS.IVK.L2.Lemma14f
public import CFSG.GH74.GLS.IVK.L2.Lemma19b
public import CFSG.GH74.GLS.IVK.Prod.Lemma31
public import CFSG.GH74.GLS.IVK.Proofs
public import CFSG.GH74.GLS.IVK.Statements
public import CFSG.GH74.GLS.LU.Ident
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.Generic.BProg.B1.Assembly2
public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicIso4
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicQuot
public import CFSG.GH74.Generic.BProg.B2.GenLocU3
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtFrame
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.BProg.Theta32
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.GH74.KGroups.L3EpsInvLin
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2CyclicFour
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix GenLocU4ExtBd

namespace GenLocU4Q2sPsi

variable {K : Type} [Field K]

@[expose] def wM (i : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 1, 0; i, 0, -i, 0; 0, 1, 0, 1; 0, i, 0, -i]

@[expose] def wI (i : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1 / 2, -i / 2, 0, 0; 0, 0, 1 / 2, -i / 2; 1 / 2, i / 2, 0, 0; 0, 0, 1 / 2, i / 2]

@[expose] def bo (P Q : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, P 0 0, P 0 1; 0, 0, P 1 0, P 1 1; Q 0 0, Q 0 1, 0, 0; Q 1 0, Q 1 1, 0, 0]

@[expose] def jm : Matrix (Fin 4) (Fin 4) K := !![0, 0, 2, 0; 0, 0, 0, 2; 2, 0, 0, 0; 0, 2, 0, 0]

@[expose] def X2 : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

@[expose] def psi (i : K) (A B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  wM i * bd A B * wI i

section Basic

variable {i : K}

theorem wM_mul_wI (hi : i * i = -1) (h2 : (2 : K) ≠ 0) : wM i * wI i = 1 := by
  have hi2 : i ^ 2 = -1 := by rw [sq]; exact hi
  ext a b
  fin_cases a <;> fin_cases b <;> simp [wM, wI, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;>
    first | ring1 | (ring_nf; try simp only [hi2]; try ring1)

theorem wI_mul_wM (hi : i * i = -1) (h2 : (2 : K) ≠ 0) : wI i * wM i = 1 := by
  have hi2 : i ^ 2 = -1 := by rw [sq]; exact hi
  ext a b
  fin_cases a <;> fin_cases b <;> simp [wM, wI, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;>
    first | ring1 | (ring_nf; try simp only [hi2]; try ring1)

theorem wM_transpose_mul (hi : i * i = -1) : (wM i)ᵀ * wM i = jm := by
  have hi2 : i ^ 2 = -1 := by rw [sq]; exact hi
  ext a b
  fin_cases a <;> fin_cases b <;> simp [wM, jm, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | ring1 | (ring_nf; try simp only [hi2]; try ring1)

theorem psi_mul (hi : i * i = -1) (h2 : (2 : K) ≠ 0) (A B A' B' : Matrix (Fin 2) (Fin 2) K) :
    psi i A B * psi i A' B' = psi i (A * A') (B * B') := by
  unfold psi
  calc wM i * bd A B * wI i * (wM i * bd A' B' * wI i)
      = wM i * bd A B * (wI i * wM i) * bd A' B' * wI i := by simp only [Matrix.mul_assoc]
    _ = wM i * (bd A B * bd A' B') * wI i := by
        rw [wI_mul_wM hi h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = wM i * bd (A * A') (B * B') * wI i := by rw [bd_mul]

theorem psi_one (hi : i * i = -1) (h2 : (2 : K) ≠ 0) : psi i 1 1 = 1 := by
  unfold psi
  rw [bd_one, Matrix.mul_one, wM_mul_wI hi h2]

theorem psi_smul_one (hi : i * i = -1) (h2 : (2 : K) ≠ 0) (c : K) : psi i (c • 1) (c • 1) = c • 1 := by
  unfold psi
  rw [← bd_smul, bd_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, wM_mul_wI hi h2]

theorem psi_inj (hi : i * i = -1) (h2 : (2 : K) ≠ 0) {A B A' B' : Matrix (Fin 2) (Fin 2) K}
    (h : psi i A B = psi i A' B') : A = A' ∧ B = B' := by
  have key : ∀ C D : Matrix (Fin 2) (Fin 2) K, wI i * psi i C D * wM i = bd C D := by
    intro C D
    unfold psi
    calc wI i * (wM i * bd C D * wI i) * wM i = (wI i * wM i) * bd C D * (wI i * wM i) := by
          simp only [Matrix.mul_assoc]
      _ = bd C D := by rw [wI_mul_wM hi h2]; simp
  exact bd_inj (by rw [← key, ← key, h])

theorem xi_wM (hi : i * i = -1) :
    (GenLocU4Out.xi : Matrix (Fin 4) (Fin 4) K) * wM i = wM i * bd ((i : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ((-i) • 1) := by
  have hi2 : i ^ 2 = -1 := by rw [sq]; exact hi
  ext a b
  fin_cases a <;> fin_cases b <;> simp [GenLocU4Out.xi, wM, bd, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | ring1 | (ring_nf; try simp only [hi2]; try ring1)

theorem wI_xi (hi : i * i = -1) (h2 : (2 : K) ≠ 0) :
    wI i * (GenLocU4Out.xi : Matrix (Fin 4) (Fin 4) K) = bd ((i : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ((-i) • 1) * wI i := by
  have hi2 : i ^ 2 = -1 := by rw [sq]; exact hi
  ext a b
  fin_cases a <;> fin_cases b <;> simp [GenLocU4Out.xi, wI, bd, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp <;> first | ring1 | (ring_nf; try simp only [hi2]; try ring1)

theorem psi_xi (hi : i * i = -1) (h2 : (2 : K) ≠ 0) (A B : Matrix (Fin 2) (Fin 2) K) :
    (GenLocU4Out.xi : Matrix (Fin 4) (Fin 4) K) * psi i A B = psi i A B * GenLocU4Out.xi := by
  unfold psi
  have hD : bd ((i : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ((-i) • 1) * bd A B =
      bd A B * bd ((i : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ((-i) • 1) := by
    rw [bd_mul, bd_mul]; simp
  calc (GenLocU4Out.xi : Matrix (Fin 4) (Fin 4) K) * (wM i * bd A B * wI i)
      = ((GenLocU4Out.xi : Matrix (Fin 4) (Fin 4) K) * wM i) * bd A B * wI i := by simp only [Matrix.mul_assoc]
    _ = wM i * (bd ((i : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ((-i) • 1) * bd A B) * wI i := by
        rw [xi_wM hi]; simp only [Matrix.mul_assoc]
    _ = wM i * (bd A B * bd ((i : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ((-i) • 1)) * wI i := by rw [hD]
    _ = wM i * bd A B * (bd ((i : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ((-i) • 1) * wI i) := by
        simp only [Matrix.mul_assoc]
    _ = wM i * bd A B * (wI i * GenLocU4Out.xi) := by rw [wI_xi hi h2]
    _ = wM i * bd A B * wI i * GenLocU4Out.xi := by simp only [Matrix.mul_assoc]

end Basic

section Off

variable {i : K}

theorem bd_mul_bo (A B P Q : Matrix (Fin 2) (Fin 2) K) : bd A B * bo P Q = bo (A * P) (B * Q) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [bd, bo, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem bo_mul_bd (A B P Q : Matrix (Fin 2) (Fin 2) K) : bo P Q * bd A B = bo (P * B) (Q * A) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [bd, bo, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem bo_inj {P Q P' Q' : Matrix (Fin 2) (Fin 2) K} (h : bo P Q = bo P' Q') : P = P' ∧ Q = Q' := by
  constructor
  · ext a b
    have := congrFun (congrFun h a.castSucc.castSucc) b.succ.succ
    fin_cases a <;> fin_cases b <;> simpa [bo] using this
  · ext a b
    have := congrFun (congrFun h a.succ.succ) b.castSucc.castSucc
    fin_cases a <;> fin_cases b <;> simpa [bo] using this

@[expose] def psiO (i : K) (P Q : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  wM i * bo P Q * wI i

theorem psi_mul_psiO (hi : i * i = -1) (h2 : (2 : K) ≠ 0) (A B P Q : Matrix (Fin 2) (Fin 2) K) :
    psi i A B * psiO i P Q = psiO i (A * P) (B * Q) := by
  unfold psi psiO
  calc wM i * bd A B * wI i * (wM i * bo P Q * wI i)
      = wM i * bd A B * (wI i * wM i) * bo P Q * wI i := by simp only [Matrix.mul_assoc]
    _ = wM i * (bd A B * bo P Q) * wI i := by
        rw [wI_mul_wM hi h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = wM i * bo (A * P) (B * Q) * wI i := by rw [bd_mul_bo]

theorem psiO_mul_psi (hi : i * i = -1) (h2 : (2 : K) ≠ 0) (A B P Q : Matrix (Fin 2) (Fin 2) K) :
    psiO i P Q * psi i A B = psiO i (P * B) (Q * A) := by
  unfold psi psiO
  calc wM i * bo P Q * wI i * (wM i * bd A B * wI i)
      = wM i * bo P Q * (wI i * wM i) * bd A B * wI i := by simp only [Matrix.mul_assoc]
    _ = wM i * (bo P Q * bd A B) * wI i := by
        rw [wI_mul_wM hi h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = wM i * bo (P * B) (Q * A) * wI i := by rw [bo_mul_bd]

theorem psiO_inj (hi : i * i = -1) (h2 : (2 : K) ≠ 0) {P Q P' Q' : Matrix (Fin 2) (Fin 2) K}
    (h : psiO i P Q = psiO i P' Q') : P = P' ∧ Q = Q' := by
  have key : ∀ C D : Matrix (Fin 2) (Fin 2) K, wI i * psiO i C D * wM i = bo C D := by
    intro C D
    unfold psiO
    calc wI i * (wM i * bo C D * wI i) * wM i = (wI i * wM i) * bo C D * (wI i * wM i) := by
          simp only [Matrix.mul_assoc]
      _ = bo C D := by rw [wI_mul_wM hi h2]; simp
  exact bo_inj (by rw [← key, ← key, h])

@[expose] def yM : Matrix (Fin 4) (Fin 4) K := !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]

theorem yM_eq (hi : i * i = -1) (h2 : (2 : K) ≠ 0) : (yM : Matrix (Fin 4) (Fin 4) K) = psiO i X2 X2 := by
  have hi2 : i ^ 2 = -1 := by rw [sq]; exact hi
  unfold psiO
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [yM, wM, wI, bo, X2, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;>
    first | ring1 | (ring_nf; try simp only [hi2]; try ring1)

end Off

section Star

variable {i : K}

theorem bd_star (bar : K →+* K) (A B : Matrix (Fin 2) (Fin 2) K) :
    ((bd A B).map bar)ᵀ = bd ((A.map bar)ᵀ) ((B.map bar)ᵀ) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [bd]

theorem bd_jm_bd (P Q R S : Matrix (Fin 2) (Fin 2) K) :
    bd P Q * jm * bd R S = jm * bd (Q * R) (P * S) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [bd, jm, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two] <;> ring

theorem map_wM (bar : K →+* K) (hbi : bar i = i) : (wM i).map bar = wM i := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [wM, hbi]

theorem map_wI (bar : K →+* K) (hbi : bar i = i) : (wI i).map bar = wI i := by
  have hb2 : bar (2 : K) = 2 := map_ofNat bar 2
  ext a b
  fin_cases a <;> fin_cases b <;> simp [wI, hbi, map_div₀, hb2]

theorem wIT_mul_jm (hi : i * i = -1) (h2 : (2 : K) ≠ 0) : (wI i)ᵀ * jm = wM i := by
  rw [← wM_transpose_mul hi, ← Matrix.mul_assoc, ← Matrix.transpose_mul, wM_mul_wI hi h2,
    Matrix.transpose_one, Matrix.one_mul]

theorem psi_star_mul (hi : i * i = -1) (h2 : (2 : K) ≠ 0) (bar : K →+* K) (hbi : bar i = i)
    (A B A' B' : Matrix (Fin 2) (Fin 2) K) :
    ((psi i A B).map bar)ᵀ * psi i A' B' = psi i ((B.map bar)ᵀ * A') ((A.map bar)ᵀ * B') := by
  unfold psi
  rw [Matrix.map_mul, Matrix.map_mul, map_wM bar hbi, map_wI bar hbi, Matrix.transpose_mul,
    Matrix.transpose_mul, bd_star]
  calc (wI i)ᵀ * (bd ((A.map bar)ᵀ) ((B.map bar)ᵀ) * (wM i)ᵀ) * (wM i * bd A' B' * wI i)
      = (wI i)ᵀ * (bd ((A.map bar)ᵀ) ((B.map bar)ᵀ) * ((wM i)ᵀ * wM i) * bd A' B') * wI i := by
        simp only [Matrix.mul_assoc]
    _ = (wI i)ᵀ * (jm * bd ((B.map bar)ᵀ * A') ((A.map bar)ᵀ * B')) * wI i := by
        rw [wM_transpose_mul hi, bd_jm_bd]
    _ = wM i * bd ((B.map bar)ᵀ * A') ((A.map bar)ᵀ * B') * wI i := by
        rw [← Matrix.mul_assoc, wIT_mul_jm hi h2]

theorem psi_unitary_iff (hi : i * i = -1) (h2 : (2 : K) ≠ 0) (bar : K →+* K) (hbi : bar i = i)
    (A B : Matrix (Fin 2) (Fin 2) K) :
    ((psi i A B).map bar)ᵀ * psi i A B = 1 ↔ (A.map bar)ᵀ * B = 1 ∧ (B.map bar)ᵀ * A = 1 := by
  rw [psi_star_mul hi h2 bar hbi, ← psi_one hi h2]
  constructor
  · intro h
    obtain ⟨h1, h1'⟩ := psi_inj hi h2 h
    exact ⟨h1', h1⟩
  · rintro ⟨h1, h1'⟩
    rw [h1, h1']

theorem det_bd (A B : Matrix (Fin 2) (Fin 2) K) : (bd A B).det = A.det * B.det := by
  rw [Matrix.det_succ_row_zero]
  simp [bd, Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.det_fin_two, Fin.succAbove]
  ring

theorem psi_det (hi : i * i = -1) (h2 : (2 : K) ≠ 0) (A B : Matrix (Fin 2) (Fin 2) K) :
    (psi i A B).det = A.det * B.det := by
  unfold psi
  have h1 : (wM i).det * (wI i).det = 1 := by rw [← Matrix.det_mul, wM_mul_wI hi h2, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, det_bd]
  calc (wM i).det * (A.det * B.det) * (wI i).det = ((wM i).det * (wI i).det) * (A.det * B.det) := by ring
    _ = A.det * B.det := by rw [h1, one_mul]

end Star

theorem exists_psi_of_comm {i : K} (hi : i * i = -1) (h2 : (2 : K) ≠ 0) {g : Matrix (Fin 4) (Fin 4) K}
    (hg : g * GenLocU4Out.xi = GenLocU4Out.xi * g) : ∃ A B : Matrix (Fin 2) (Fin 2) K, g = psi i A B := by
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hMD : (wI i * g * wM i) * bd ((i : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ((-i) • 1) =
      bd ((i : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ((-i) • 1) * (wI i * g * wM i) := by
    calc (wI i * g * wM i) * bd ((i : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ((-i) • 1)
        = wI i * g * (GenLocU4Out.xi * wM i) := by rw [xi_wM hi]; simp only [Matrix.mul_assoc]
      _ = wI i * (g * GenLocU4Out.xi) * wM i := by simp only [Matrix.mul_assoc]
      _ = wI i * (GenLocU4Out.xi * g) * wM i := by rw [hg]
      _ = (wI i * GenLocU4Out.xi) * g * wM i := by simp only [Matrix.mul_assoc]
      _ = bd ((i : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ((-i) • 1) * (wI i * g * wM i) := by
          rw [wI_xi hi h2]; simp only [Matrix.mul_assoc]
  have hDE : bd ((i : K) • (1 : Matrix (Fin 2) (Fin 2) K)) ((-i) • 1) = (-i) • bd (-1 : Matrix (Fin 2) (Fin 2) K) 1 := by
    rw [bd_smul]; simp
  have hME : (wI i * g * wM i) * Matrix.diagonal ![-1, -1, 1, 1] = Matrix.diagonal ![-1, -1, 1, 1] * (wI i * g * wM i) := by
    rw [diag_eq_bd]
    rw [hDE, Matrix.mul_smul, Matrix.smul_mul] at hMD
    exact smul_right_injective _ (neg_ne_zero.2 hi0) hMD
  obtain ⟨A, B, hAB⟩ := exists_bd_of_comm h2 _ hME
  refine ⟨A, B, ?_⟩
  unfold psi
  rw [← hAB]
  calc g = (wM i * wI i) * g * (wM i * wI i) := by rw [wM_mul_wI hi h2]; simp
    _ = wM i * (wI i * g * wM i) * wI i := by simp only [Matrix.mul_assoc]

end GenLocU4Q2sPsi

end CFSG.GH74.Generic.BProg.B2
