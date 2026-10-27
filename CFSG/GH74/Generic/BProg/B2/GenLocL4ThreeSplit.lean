module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4ThreeMat
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutSplit
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.IVK.L2.BN
public import CFSG.GH74.GLS.IVK.L2.BorelFive
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma113
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
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.Generic.BProg.B1.Assembly2
public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutGraph
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutPlane
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.BProg.Theta32
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
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
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Matrix
open scoped MatrixGroups

namespace GenLocL4ThreeSplit

open GenLocL4Out GenLocL4ThreeMat

@[expose] def q02 : SL(4, ZMod 3) :=
  ⟨!![0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1], by decide⟩

@[expose] def m21 : SL(4, ZMod 3) := tv 2 1 (by decide) (-1)
@[expose] def m12 : SL(4, ZMod 3) := tv 1 2 (by decide) (-1)

theorem q02_x01 : (q02 : M4) * x01 = m21 * q02 := by decide
theorem q02_x10 : (q02 : M4) * x10 = m12 * q02 := by decide
theorem q02_x23 : (q02 : M4) * x23 = x03 * q02 := by decide
theorem q02_x32 : (q02 : M4) * x32 = x30 * q02 := by decide

theorem x21_eq : (x21 : M4) = m21 * m21 := by decide
theorem x12_eq : (x12 : M4) = m12 * m12 := by decide

theorem x02_word : (x02 : M4) = ([x01, x12, x01, x01, x12, x12].map fun g => (g : M4)).prod := by decide
theorem x13_word : (x13 : M4) = ([x10, x03, x10, x10, x03, x03].map fun g => (g : M4)).prod := by decide
theorem x20_word : (x20 : M4) = ([x21, x10, x21, x21, x10, x10].map fun g => (g : M4)).prod := by decide
theorem x31_word : (x31 : M4) = ([x30, x01, x30, x30, x01, x01].map fun g => (g : M4)).prod := by decide

theorem top_of_q02 (Γ : Subgroup SL(4, ZMod 3)) (h01 : x01 ∈ Γ) (h10 : x10 ∈ Γ) (h23 : x23 ∈ Γ)
    (h32 : x32 ∈ Γ) (hq : q02 ∈ Γ) : Γ = ⊤ := by
  have hm21 : m21 ∈ Γ := mem_of_conj hq h01 q02_x01
  have hm12 : m12 ∈ Γ := mem_of_conj hq h10 q02_x10
  have h03 : x03 ∈ Γ := mem_of_conj hq h23 q02_x23
  have h30 : x30 ∈ Γ := mem_of_conj hq h32 q02_x32
  have h21 : x21 ∈ Γ := mem_of_coe_mul hm21 hm21 x21_eq
  have h12 : x12 ∈ Γ := mem_of_coe_mul hm12 hm12 x12_eq
  have h02 : x02 ∈ Γ := mem_of_coe_prod _ (by simp [h01, h12]) x02_word
  have h13 : x13 ∈ Γ := mem_of_coe_prod _ (by simp [h10, h03]) x13_word
  have h20 : x20 ∈ Γ := mem_of_coe_prod _ (by simp [h21, h10]) x20_word
  have h31 : x31 ∈ Γ := mem_of_coe_prod _ (by simp [h30, h01]) x31_word
  exact top_of_root_elements' Γ h01 h02 h03 h10 h12 h13 h20 h21 h23 h30 h31 h32

@[expose] def dg (a0 a1 a2 a3 : ZMod 3) : M4 := !![a0, 0, 0, 0; 0, a1, 0, 0; 0, 0, a2, 0; 0, 0, 0, a3]

theorem diagonal_eq_dg (d : Fin 4 → ZMod 3) : (Matrix.diagonal d : M4) = dg (d 0) (d 1) (d 2) (d 3) :=
  diagonal_four d

@[expose] def q03 : SL(4, ZMod 3) := ⟨!![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; -1, 0, 0, 0], by decide⟩
@[expose] def q12 : SL(4, ZMod 3) := ⟨!![1, 0, 0, 0; 0, 0, 1, 0; 0, -1, 0, 0; 0, 0, 0, 1], by decide⟩
@[expose] def q13 : SL(4, ZMod 3) := ⟨!![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0], by decide⟩

@[expose] def sUi : SL(4, ZMod 3) := ⟨!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide⟩
@[expose] def sWi : SL(4, ZMod 3) := ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0], by decide⟩

@[expose] def bT : SL(4, ZMod 3) := ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1], by decide⟩
@[expose] def bTi : SL(4, ZMod 3) := ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, -1; 0, 0, -1, 1], by decide⟩
@[expose] def mixM : SL(4, ZMod 3) := ⟨!![0, 0, -1, -1; 0, 1, 0, 0; -1, 0, -1, 1; -1, 0, 1, -1], by decide⟩

theorem iso_q02 : ∀ a0 a1 a2 a3 : ZMod 3, a0 = a2 →
    (q02 : M4) * dg a0 a1 a2 a3 * (q02 : M4)ᵀ = dg a0 a1 a2 a3 := by decide
theorem iso_q03 : ∀ a0 a1 a2 a3 : ZMod 3, a0 = a3 →
    (q03 : M4) * dg a0 a1 a2 a3 * (q03 : M4)ᵀ = dg a0 a1 a2 a3 := by decide
theorem iso_q12 : ∀ a0 a1 a2 a3 : ZMod 3, a1 = a2 →
    (q12 : M4) * dg a0 a1 a2 a3 * (q12 : M4)ᵀ = dg a0 a1 a2 a3 := by decide
theorem iso_q13 : ∀ a0 a1 a2 a3 : ZMod 3, a1 = a3 →
    (q13 : M4) * dg a0 a1 a2 a3 * (q13 : M4)ᵀ = dg a0 a1 a2 a3 := by decide
theorem iso_mixM : ∀ s : ZMod 3, (mixM : M4) * dg s s (-s) (-s) * (mixM : M4)ᵀ = dg s s (-s) (-s) := by
  decide

theorem conj_q03 : (sWi : M4) * q03 = q02 * sWi := by decide
theorem conj_q12 : (sUi : M4) * q12 = q02 * sUi := by decide
theorem conj_q13 : ((sUi * sWi : SL(4, ZMod 3)) : M4) * q13 = q02 * (sUi * sWi : SL(4, ZMod 3)) := by
  decide
theorem q02_eq : (q02 : M4) = bTi * mixM * bT := by decide

theorem bad_pattern : ∀ a b c e : ZMod 3, a ≠ 0 → b ≠ 0 → c ≠ 0 → e ≠ 0 →
    (a ≠ c ∧ a ≠ e ∧ b ≠ c ∧ b ≠ e) → (b = a ∧ c = -a ∧ e = -a) := by decide

theorem comm_x01 : (x01 : M4) * tM = tM * x01 := by decide
theorem comm_x10 : (x10 : M4) * tM = tM * x10 := by decide
theorem comm_x23 : (x23 : M4) * tM = tM * x23 := by decide
theorem comm_x32 : (x32 : M4) * tM = tM * x32 := by decide
theorem comm_sUi : (sUi : M4) * tM = tM * sUi := by decide
theorem comm_sWi : (sWi : M4) * tM = tM * sWi := by decide
theorem comm_bT : (bT : M4) * tM = tM * bT := by decide
theorem comm_bTi : (bTi : M4) * tM = tM * bTi := by decide

theorem core_three (d : Fin 4 → ZMod 3) (hd : ∀ i, d i ≠ 0) (Γ : Subgroup SL(4, ZMod 3))
    (hC : ∀ x : SL(4, ZMod 3), (x : M4) * tM = tM * x → x ∈ Γ)
    (hO : ∀ r : SL(4, ZMod 3), (r : M4) * Matrix.diagonal d * (r : M4)ᵀ = Matrix.diagonal d → r ∈ Γ) :
    Γ = ⊤ := by
  have hO' : ∀ r : SL(4, ZMod 3), (r : M4) * dg (d 0) (d 1) (d 2) (d 3) * (r : M4)ᵀ =
      dg (d 0) (d 1) (d 2) (d 3) → r ∈ Γ := by
    intro r hr
    apply hO
    rw [diagonal_eq_dg]
    exact hr
  refine top_of_q02 Γ (hC _ comm_x01) (hC _ comm_x10) (hC _ comm_x23) (hC _ comm_x32) ?_
  by_cases c02 : d 0 = d 2
  · exact hO' q02 (iso_q02 _ _ _ _ c02)
  by_cases c03 : d 0 = d 3
  · exact mem_of_conj (hC _ comm_sWi) (hO' q03 (iso_q03 _ _ _ _ c03)) conj_q03
  by_cases c12 : d 1 = d 2
  · exact mem_of_conj (hC _ comm_sUi) (hO' q12 (iso_q12 _ _ _ _ c12)) conj_q12
  by_cases c13 : d 1 = d 3
  · exact mem_of_conj (Γ.mul_mem (hC _ comm_sUi) (hC _ comm_sWi)) (hO' q13 (iso_q13 _ _ _ _ c13)) conj_q13
  obtain ⟨e1, e2, e3⟩ := bad_pattern _ _ _ _ (hd 0) (hd 1) (hd 2) (hd 3) ⟨c02, c03, c12, c13⟩
  have hM : mixM ∈ Γ := hO' mixM (by rw [e1, e2, e3]; exact iso_mixM _)
  exact mem_of_coe_mul3 (hC _ comm_bTi) hM (hC _ comm_bT) q02_eq

theorem conj_comm (Pm Pi x Dd : M4) (hPiP : Pi * Pm = 1) (hx : x * Dd = Dd * x) :
    Pm * x * Pi * (Pm * Dd * Pi) = Pm * Dd * Pi * (Pm * x * Pi) := by
  calc Pm * x * Pi * (Pm * Dd * Pi) = Pm * x * (Pi * Pm) * Dd * Pi := by simp only [Matrix.mul_assoc]
    _ = Pm * (x * Dd) * Pi := by rw [hPiP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = Pm * (Dd * x) * Pi := by rw [hx]
    _ = Pm * Dd * (Pi * Pm) * x * Pi := by rw [hPiP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem conj_iso (Pm Pi r Dd : M4) (hPiP : Pi * Pm = 1) (hr : r * Dd * rᵀ = Dd) :
    Pm * r * Pi * (Pm * Dd * Pmᵀ) * (Pm * r * Pi)ᵀ = Pm * Dd * Pmᵀ := by
  have hPt : Pmᵀ * Piᵀ = 1 := by rw [← Matrix.transpose_mul, hPiP, Matrix.transpose_one]
  calc Pm * r * Pi * (Pm * Dd * Pmᵀ) * (Pm * r * Pi)ᵀ
      = Pm * r * (Pi * Pm) * Dd * (Pmᵀ * Piᵀ) * rᵀ * Pmᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = Pm * (r * Dd * rᵀ) * Pmᵀ := by rw [hPiP, hPt]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Pm * Dd * Pmᵀ := by rw [hr]

end GenLocL4ThreeSplit

local notation "K3" => ZMod 3

open CFSG.ComponentClassification.CatalogueBHigherLinearAction in
theorem gen_split_three (B g : Matrix (Fin 4) (Fin 4) K3)
    (hBt : Bᵀ = B) (hdet : B.det ≠ 0) (hgg : g * g = 1) (hg1 : g ≠ 1) (hgm1 : g ≠ -1) (hgdet : g.det = 1)
    (hgB : g * B = B * gᵀ) (Γ : Subgroup SL(4, K3))
    (h1 : ∀ x : SL(4, K3), (x : Matrix (Fin 4) (Fin 4) K3) * g = g * (x : Matrix (Fin 4) (Fin 4) K3) → x ∈ Γ)
    (h2 : ∀ x : SL(4, K3), (x : Matrix (Fin 4) (Fin 4) K3) * B * (x : Matrix (Fin 4) (Fin 4) K3)ᵀ = B → x ∈ Γ) :
    Γ = ⊤ := by
  have hF4 : Nat.card (ZMod 3) % 4 = 3 := by simp
  obtain ⟨P, d, hd, hBP, hgP⟩ := GenLocL4Out.split_frame hF4 B g hBt hdet hgg hg1 hgm1 hgdet hgB
  have hPP : (P : Matrix (Fin 4) (Fin 4) K3) * ((P⁻¹ : GL (Fin 4) K3) : Matrix (Fin 4) (Fin 4) K3) = 1 :=
    GenLocL4Out.PiP' P
  have hPiP : ((P⁻¹ : GL (Fin 4) K3) : Matrix (Fin 4) (Fin 4) K3) * (P : Matrix (Fin 4) (Fin 4) K3) = 1 :=
    GenLocL4Out.PPi P
  have hgP' : g * (P : Matrix (Fin 4) (Fin 4) K3) = (P : Matrix (Fin 4) (Fin 4) K3) * GenLocL4ThreeMat.tM := hgP
  have hg_eq : g = (P : Matrix (Fin 4) (Fin 4) K3) * GenLocL4ThreeMat.tM *
      ((P⁻¹ : GL (Fin 4) K3) : Matrix (Fin 4) (Fin 4) K3) := by
    calc g = g * ((P : Matrix (Fin 4) (Fin 4) K3) * ((P⁻¹ : GL (Fin 4) K3) : Matrix (Fin 4) (Fin 4) K3)) := by
          rw [hPP, Matrix.mul_one]
      _ = (g * (P : Matrix (Fin 4) (Fin 4) K3)) * ((P⁻¹ : GL (Fin 4) K3) : Matrix (Fin 4) (Fin 4) K3) := by
          rw [Matrix.mul_assoc]
      _ = _ := by rw [hgP']
  have hC : ∀ x : SL(4, K3), (x : Matrix (Fin 4) (Fin 4) K3) * GenLocL4ThreeMat.tM =
      GenLocL4ThreeMat.tM * (x : Matrix (Fin 4) (Fin 4) K3) →
      x ∈ Γ.comap (slConjugation 4 K3 P).toMonoidHom := by
    intro x hx
    show (slConjugation 4 K3 P).toMonoidHom x ∈ Γ
    apply h1
    rw [GenLocL4Out.coe_conj, hg_eq]
    exact GenLocL4ThreeSplit.conj_comm _ _ _ _ hPiP hx
  have hO : ∀ r : SL(4, K3), (r : Matrix (Fin 4) (Fin 4) K3) * Matrix.diagonal d *
      (r : Matrix (Fin 4) (Fin 4) K3)ᵀ = Matrix.diagonal d →
      r ∈ Γ.comap (slConjugation 4 K3 P).toMonoidHom := by
    intro r hr
    show (slConjugation 4 K3 P).toMonoidHom r ∈ Γ
    apply h2
    rw [GenLocL4Out.coe_conj, hBP]
    exact GenLocL4ThreeSplit.conj_iso _ _ _ _ hPiP hr
  exact GenLocL4Out.top_of_conj Γ P (GenLocL4ThreeSplit.core_three d hd _ hC hO)

end CFSG.GH74.Generic.BProg.B2
