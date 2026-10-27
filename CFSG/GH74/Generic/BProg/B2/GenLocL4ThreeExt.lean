module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4ThreeMat
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutExt
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

namespace GenLocL4ThreeExt

open GenLocL4Out GenLocL4ThreeMat

@[expose] def g9 : SL(4, ZMod 3) :=
  ⟨!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0], by decide⟩
@[expose] def g15 : SL(4, ZMod 3) :=
  ⟨!![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0], by decide⟩
@[expose] def g16 : SL(4, ZMod 3) :=
  ⟨!![0, 0, -1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0], by decide⟩
@[expose] def g17 : SL(4, ZMod 3) :=
  ⟨!![0, 0, 0, -1; 0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0], by decide⟩
@[expose] def g25 : SL(4, ZMod 3) :=
  ⟨!![0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0], by decide⟩
@[expose] def g76 : SL(4, ZMod 3) :=
  ⟨!![0, -1, 0, 1; 1, 0, -1, 0; 0, 0, -1, 0; 0, 0, 0, -1], by decide⟩
@[expose] def g77 : SL(4, ZMod 3) :=
  ⟨!![0, -1, 0, -1; 1, 0, 1, 0; 0, 0, -1, 0; 0, 0, 0, -1], by decide⟩
@[expose] def g78 : SL(4, ZMod 3) :=
  ⟨!![0, -1, 1, 0; 1, 0, 0, 1; 0, 0, -1, 0; 0, 0, 0, -1], by decide⟩
@[expose] def g79 : SL(4, ZMod 3) :=
  ⟨!![0, -1, -1, 0; 1, 0, 0, -1; 0, 0, -1, 0; 0, 0, 0, -1], by decide⟩
@[expose] def g84 : SL(4, ZMod 3) :=
  ⟨!![0, 1, 1, 0; -1, 0, 0, 1; 0, 0, 0, 1; 0, 0, -1, 0], by decide⟩
@[expose] def g86 : SL(4, ZMod 3) :=
  ⟨!![0, 1, 0, 1; -1, 0, -1, 0; 0, 0, 0, 1; 0, 0, -1, 0], by decide⟩
@[expose] def g87 : SL(4, ZMod 3) :=
  ⟨!![0, 1, 0, -1; -1, 0, 1, 0; 0, 0, 0, 1; 0, 0, -1, 0], by decide⟩
@[expose] def g113 : SL(4, ZMod 3) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, -1, 0; 0, 1, 0, -1], by decide⟩
@[expose] def g114 : SL(4, ZMod 3) :=
  ⟨!![0, 1, 0, 0; -1, 0, 0, 0; 1, 0, -1, 0; 0, 1, 0, -1], by decide⟩
@[expose] def g117 : SL(4, ZMod 3) :=
  ⟨!![-1, 0, 0, 0; 0, -1, 0, 0; 1, 0, -1, 0; 0, 1, 0, -1], by decide⟩
@[expose] def g119 : SL(4, ZMod 3) :=
  ⟨!![0, -1, 0, 0; 1, 0, 0, 0; 1, 0, -1, 0; 0, 1, 0, -1], by decide⟩
@[expose] def g32 : SL(4, ZMod 3) :=
  ⟨!![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, -1, -1], by decide⟩
@[expose] def g33 : SL(4, ZMod 3) :=
  ⟨!![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, -1, -1], by decide⟩
@[expose] def g34 : SL(4, ZMod 3) :=
  ⟨!![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, -1; 0, 0, 0, -1], by decide⟩
@[expose] def g36 : SL(4, ZMod 3) :=
  ⟨!![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 1; 0, 0, 0, 1], by decide⟩
@[expose] def g38 : SL(4, ZMod 3) :=
  ⟨!![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 1, 1], by decide⟩
@[expose] def g39 : SL(4, ZMod 3) :=
  ⟨!![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 1, 1], by decide⟩
@[expose] def g40 : SL(4, ZMod 3) :=
  ⟨!![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 1; 0, 0, 0, -1], by decide⟩
@[expose] def g41 : SL(4, ZMod 3) :=
  ⟨!![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 1, -1], by decide⟩
@[expose] def g44 : SL(4, ZMod 3) :=
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 1, -1], by decide⟩
@[expose] def g45 : SL(4, ZMod 3) :=
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 1; 0, 0, 0, -1], by decide⟩

theorem core_ext_three (Γ : Subgroup SL(4, ZMod 3))
    (hC : ∀ x : SL(4, ZMod 3), (x : M4) * jM = jM * (x : M4) → x ∈ Γ)
    (hB : ∀ x : SL(4, ZMod 3), (x : M4) * BjM * (x : M4)ᵀ = BjM → x ∈ Γ)
    (hM : ∀ x : SL(4, ZMod 3), (x : M4) * (jM * BjM) * (x : M4)ᵀ = jM * BjM → x ∈ Γ) :
    Γ = ⊤ := by
  have e9 : g9 ∈ Γ := hC _ (by decide)
  have e15 : g15 ∈ Γ := hC _ (by decide)
  have e16 : g16 ∈ Γ := hC _ (by decide)
  have e17 : g17 ∈ Γ := hC _ (by decide)
  have e25 : g25 ∈ Γ := hC _ (by decide)
  have e76 : g76 ∈ Γ := hC _ (by decide)
  have e77 : g77 ∈ Γ := hC _ (by decide)
  have e78 : g78 ∈ Γ := hC _ (by decide)
  have e79 : g79 ∈ Γ := hC _ (by decide)
  have e84 : g84 ∈ Γ := hC _ (by decide)
  have e86 : g86 ∈ Γ := hC _ (by decide)
  have e87 : g87 ∈ Γ := hC _ (by decide)
  have e113 : g113 ∈ Γ := hC _ (by decide)
  have e114 : g114 ∈ Γ := hC _ (by decide)
  have e117 : g117 ∈ Γ := hC _ (by decide)
  have e119 : g119 ∈ Γ := hC _ (by decide)
  have e32 : g32 ∈ Γ := hB _ (by decide)
  have e33 : g33 ∈ Γ := hB _ (by decide)
  have e34 : g34 ∈ Γ := hB _ (by decide)
  have e36 : g36 ∈ Γ := hB _ (by decide)
  have e38 : g38 ∈ Γ := hB _ (by decide)
  have e39 : g39 ∈ Γ := hB _ (by decide)
  have e40 : g40 ∈ Γ := hM _ (by decide)
  have e41 : g41 ∈ Γ := hM _ (by decide)
  have e44 : g44 ∈ Γ := hM _ (by decide)
  have e45 : g45 ∈ Γ := hM _ (by decide)
  have h01 : x01 ∈ Γ :=
    mem_of_coe_prod [g17, g44, g32, g25] (by simp [e17, e44, e32, e25]) (by decide)
  have h02 : x02 ∈ Γ :=
    mem_of_coe_prod [g32, g77, g32, g79] (by simp [e32, e77, e79]) (by decide)
  have h03 : x03 ∈ Γ :=
    mem_of_coe_prod [g86, g39, g87, g36] (by simp [e86, e39, e87, e36]) (by decide)
  have h10 : x10 ∈ Γ :=
    mem_of_coe_prod [g25, g32, g40, g16] (by simp [e25, e32, e40, e16]) (by decide)
  have h12 : x12 ∈ Γ :=
    mem_of_coe_prod [g32, g78, g32, g76] (by simp [e32, e78, e76]) (by decide)
  have h13 : x13 ∈ Γ :=
    mem_of_coe_prod [g84, g39, g84, g36] (by simp [e84, e39, e36]) (by decide)
  have h20 : x20 ∈ Γ :=
    mem_of_coe_prod [g114, g45, g119, g40] (by simp [e114, e45, e119, e40]) (by decide)
  have h21 : x21 ∈ Γ :=
    mem_of_coe_prod [g117, g34, g117, g34] (by simp [e117, e34]) (by decide)
  have h23 : x23 ∈ Γ :=
    mem_of_coe_prod [g15, g40, g38] (by simp [e15, e40, e38]) (by decide)
  have h30 : x30 ∈ Γ :=
    mem_of_coe_prod [g113, g32, g117, g33] (by simp [e113, e32, e117, e33]) (by decide)
  have h31 : x31 ∈ Γ :=
    mem_of_coe_prod [g114, g44, g119, g41] (by simp [e114, e44, e119, e41]) (by decide)
  have h32 : x32 ∈ Γ :=
    mem_of_coe_prod [g9, g39, g45] (by simp [e9, e39, e45]) (by decide)
  exact top_of_root_elements' Γ h01 h02 h03 h10 h12 h13 h20 h21 h23 h30 h31 h32

@[expose] def Mext (κ a b c d : ZMod 3) : M4 := bd2 (κ • !![0, 1; 1, 0]) !![a, b; c, d]

@[expose] def hcand : List M4 :=
  [bd2 !![1, 1; -1, 1] !![1, 0; 0, 1], bd2 !![1, 1; -1, 1] !![1, -1; 1, 1],
   bd2 !![1, 1; -1, 1] !![1, 1; -1, 1], bd2 !![1, 1; -1, 1] !![0, -1; 1, 0],
   bd2 !![1, -1; 1, 1] !![1, 0; 0, 1], bd2 !![1, -1; 1, 1] !![1, -1; 1, 1],
   bd2 !![1, -1; 1, 1] !![1, 1; -1, 1], bd2 !![1, -1; 1, 1] !![0, -1; 1, 0]]

theorem exists_h : ∀ κ a b c d : ZMod 3, κ ≠ 0 → (Mext κ a b c d)ᵀ = Mext κ a b c d →
    jM * Mext κ a b c d = Mext κ a b c d * jMᵀ → ¬ IsSquare (Mext κ a b c d).det →
    ∃ h ∈ hcand, h * jM = jM * h ∧ h * BjM * hᵀ = Mext κ a b c d ∧ h.det ≠ 0 := by
  decide

theorem frame_facts {Pm Pi B g M jj : M4} (hPP : Pm * Pi = 1) (hPiP : Pi * Pm = 1) (hBt : Bᵀ = B)
    (hgB : g * B = B * gᵀ) (hBP : B = Pm * M * Pmᵀ) (hgP : g * Pm = Pm * jj) :
    Mᵀ = M ∧ jj * M = M * jjᵀ := by
  have hM : M = Pi * B * Piᵀ := (conj_form_aux hPP hPiP).1 hBP.symm
  have e1 : Pm * Mᵀ * Pmᵀ = B := by
    have := congrArg Matrix.transpose hBP
    rw [hBt, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [this, Matrix.mul_assoc]
  have e2 : Pm * (jj * M) * Pmᵀ = g * B := by
    calc Pm * (jj * M) * Pmᵀ = (Pm * jj) * M * Pmᵀ := by simp only [Matrix.mul_assoc]
      _ = (g * Pm) * M * Pmᵀ := by rw [hgP]
      _ = g * (Pm * M * Pmᵀ) := by simp only [Matrix.mul_assoc]
      _ = g * B := by rw [← hBP]
  have e3 : Pm * (M * jjᵀ) * Pmᵀ = B * gᵀ := by
    have h1 : Pmᵀ * gᵀ = jjᵀ * Pmᵀ := by rw [← Matrix.transpose_mul, hgP, Matrix.transpose_mul]
    calc Pm * (M * jjᵀ) * Pmᵀ = Pm * M * (jjᵀ * Pmᵀ) := by simp only [Matrix.mul_assoc]
      _ = Pm * M * (Pmᵀ * gᵀ) := by rw [h1]
      _ = (Pm * M * Pmᵀ) * gᵀ := by simp only [Matrix.mul_assoc]
      _ = B * gᵀ := by rw [← hBP]
  refine ⟨?_, ?_⟩
  · rw [(conj_form_aux hPP hPiP).1 e1, hM]
  · rw [(conj_form_aux hPP hPiP).1 e2, (conj_form_aux hPP hPiP).1 e3, hgB]

theorem not_isSquare_det_of_frame {Pm M B : M4} (hBP : B = Pm * M * Pmᵀ) (hBd : ¬ IsSquare B.det) :
    ¬ IsSquare M.det := by
  rintro ⟨s, hs⟩
  apply hBd
  refine ⟨Pm.det * s, ?_⟩
  rw [hBP, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hs]
  ring

theorem ext_frame_three (B g : M4) (hBt : Bᵀ = B) (hdet : B.det ≠ 0) (hBd : ¬ IsSquare B.det)
    (hgg : g * g = (-1 : ZMod 3) • (1 : M4)) (hgB : g * B = B * gᵀ) :
    ∃ P : GL (Fin 4) (ZMod 3), B = (P : M4) * BjM * (P : M4)ᵀ ∧ g * (P : M4) = (P : M4) * jM := by
  have hF4 : Nat.card (ZMod 3) % 4 = 3 := by simp
  obtain ⟨P, κ, B2, hκ, hBP, hgP⟩ := ext_frame hF4 B g hBt hdet hBd hgg hgB
  have hjj : bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] = jM := by decide
  have hgP' : g * (P : M4) = (P : M4) * jM := hgP.trans (congrArg _ hjj)
  have hPP : (P : M4) * ((P⁻¹ : GL (Fin 4) (ZMod 3)) : M4) = 1 := coe_mul_inv P
  have hPiP : ((P⁻¹ : GL (Fin 4) (ZMod 3)) : M4) * (P : M4) = 1 := coe_inv_mul P
  obtain ⟨hMt, hMj⟩ := frame_facts hPP hPiP hBt hgB hBP hgP'
  have hMd := not_isSquare_det_of_frame hBP hBd
  have hMe : bd2 (κ • !![0, 1; 1, 0]) B2 = Mext κ (B2 0 0) (B2 0 1) (B2 1 0) (B2 1 1) := by
    unfold Mext
    rw [← Matrix.eta_fin_two B2]
  obtain ⟨h, -, hjh, hhB, hdh⟩ := exists_h κ (B2 0 0) (B2 0 1) (B2 1 0) (B2 1 1) hκ (by rw [← hMe]; exact hMt)
    (by rw [← hMe]; exact hMj) (by rw [← hMe]; exact hMd)
  refine ⟨P * Matrix.GeneralLinearGroup.mkOfDetNeZero h hdh, ?_, ?_⟩
  · show B = (P : M4) * h * BjM * ((P : M4) * h)ᵀ
    rw [hBP, hMe, ← hhB, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  · show g * ((P : M4) * h) = (P : M4) * h * jM
    rw [← Matrix.mul_assoc, hgP', Matrix.mul_assoc, Matrix.mul_assoc, hjh]

end GenLocL4ThreeExt

local notation "K3" => ZMod 3

open CFSG.ComponentClassification.CatalogueBHigherLinearAction in
theorem classExt_three : ∀ (B g : Matrix (Fin 4) (Fin 4) K3), Bᵀ = B → B.det ≠ 0 → ¬ IsSquare B.det →
    g * g = (-1 : K3) • (1 : Matrix (Fin 4) (Fin 4) K3) → g * B = B * gᵀ → ∀ Γ : Subgroup SL(4, K3),
      (∀ x : SL(4, K3), (x : Matrix (Fin 4) (Fin 4) K3) * g = g * (x : Matrix (Fin 4) (Fin 4) K3) → x ∈ Γ) →
      (∀ x : SL(4, K3), (x : Matrix (Fin 4) (Fin 4) K3) * B * (x : Matrix (Fin 4) (Fin 4) K3)ᵀ = B → x ∈ Γ) →
      (∀ x : SL(4, K3), (x : Matrix (Fin 4) (Fin 4) K3) * (g * B) * (x : Matrix (Fin 4) (Fin 4) K3)ᵀ = g * B →
        x ∈ Γ) →
      Γ = ⊤ := by
  intro B g hBt hdet hBd hgg hgB Γ h1 h2 h3
  obtain ⟨P, hBP, hgP⟩ := GenLocL4ThreeExt.ext_frame_three B g hBt hdet hBd hgg hgB
  have hPP : (P : Matrix (Fin 4) (Fin 4) K3) * ((P⁻¹ : GL (Fin 4) K3) : Matrix (Fin 4) (Fin 4) K3) = 1 :=
    GenLocL4Out.coe_mul_inv P
  have hPiP : ((P⁻¹ : GL (Fin 4) K3) : Matrix (Fin 4) (Fin 4) K3) * (P : Matrix (Fin 4) (Fin 4) K3) = 1 :=
    GenLocL4Out.coe_inv_mul P
  set Pm : Matrix (Fin 4) (Fin 4) K3 := (P : Matrix (Fin 4) (Fin 4) K3)
  set Pi : Matrix (Fin 4) (Fin 4) K3 := ((P⁻¹ : GL (Fin 4) K3) : Matrix (Fin 4) (Fin 4) K3)
  have hPt' : Pmᵀ * Piᵀ = 1 := by rw [← Matrix.transpose_mul, hPiP, Matrix.transpose_one]
  have eg : Pi * g * Pm = GenLocL4ThreeMat.jM := by
    rw [Matrix.mul_assoc, hgP, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have eB : Pi * B * Piᵀ = GenLocL4ThreeMat.BjM := by
    rw [hBP]
    calc Pi * (Pm * GenLocL4ThreeMat.BjM * Pmᵀ) * Piᵀ =
        (Pi * Pm) * GenLocL4ThreeMat.BjM * (Pmᵀ * Piᵀ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPiP, hPt', Matrix.one_mul, Matrix.mul_one]
  have egB : Pi * (g * B) * Piᵀ = GenLocL4ThreeMat.jM * GenLocL4ThreeMat.BjM := by
    rw [← eg, ← eB]
    calc Pi * (g * B) * Piᵀ = Pi * g * (Pm * Pi) * B * Piᵀ := by
          rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine GenLocL4Out.top_of_conj Γ P (GenLocL4ThreeExt.core_ext_three
    (Γ.comap (slConjugation 4 K3 P).toMonoidHom) ?_ ?_ ?_)
  · intro x hx
    show (slConjugation 4 K3 P).toMonoidHom x ∈ Γ
    exact h1 _ ((GenLocL4Out.conj_commute_iff P x g).2 (by rw [eg]; exact hx))
  · intro x hx
    show (slConjugation 4 K3 P).toMonoidHom x ∈ Γ
    exact h2 _ ((GenLocL4Out.conj_form_iff P x B).2 (by rw [eB]; exact hx))
  · intro x hx
    show (slConjugation 4 K3 P).toMonoidHom x ∈ Γ
    exact h3 _ ((GenLocL4Out.conj_form_iff P x (g * B)).2 (by rw [egB]; exact hx))

end CFSG.GH74.Generic.BProg.B2
