module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4ThreeMat
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutDa
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

namespace GenLocL4ThreeDa

open GenLocL4Out GenLocL4ThreeMat

@[expose] def BDa : M4 := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1]

@[expose] def gA1 : SL(4, ZMod 3) :=
  ⟨!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 1; 0, 0, 1, 1], by decide⟩

@[expose] def gA2 : SL(4, ZMod 3) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 1; 0, 0, 1, 1], by decide⟩

@[expose] def gA3 : SL(4, ZMod 3) :=
  ⟨!![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, -1, -1], by decide⟩

@[expose] def gB1 : SL(4, ZMod 3) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, -1; 0, 0, -1, 1], by decide⟩

@[expose] def gB2 : SL(4, ZMod 3) :=
  ⟨!![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 1, -1], by decide⟩

@[expose] def gB3 : SL(4, ZMod 3) :=
  ⟨!![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, -1; 0, 0, 0, 1], by decide⟩

@[expose] def gC1 : SL(4, ZMod 3) :=
  ⟨!![-1, -1, 1, 0; 1, -1, 0, 1; 1, 1, 1, 1; -1, 1, -1, 1], by decide⟩

@[expose] def gC2 : SL(4, ZMod 3) :=
  ⟨!![1, -1, -1, -1; 1, 1, 1, -1; 0, -1, 1, -1; 1, 0, 1, 1], by decide⟩

theorem w01 : (x01 : M4) =
    ([gA3, gA1, gC2, gB1, gC1, gA3, gC2, gB3, gC1, gA3, gC2, gB1, gC1].map
      fun g => (g : M4)).prod := by
  decide

theorem w02 : (x02 : M4) =
    ([gA1, gC1, gA1, gC2, gA1, gB3, gC2, gB3, gA3, gC2, gB3].map
      fun g => (g : M4)).prod := by
  decide

theorem w03 : (x03 : M4) =
    ([gA1, gC2, gA3, gB3, gC2, gB3, gA2, gC2, gA1, gC1, gB2].map
      fun g => (g : M4)).prod := by
  decide

theorem w10 : (x10 : M4) =
    ([gA1, gC2, gB1, gC1, gA3, gC2, gB3, gC1, gA3, gC2, gB1, gC1, gA3].map
      fun g => (g : M4)).prod := by
  decide

theorem w12 : (x12 : M4) =
    ([gA1, gB2, gC1, gA3, gC2, gC1, gB2, gA3, gC2, gA1, gC1].map
      fun g => (g : M4)).prod := by
  decide

theorem w13 : (x13 : M4) =
    ([gB2, gC2, gA3, gA2, gC2, gB2, gC1, gA3, gC2, gC1].map
      fun g => (g : M4)).prod := by
  decide

theorem w20 : (x20 : M4) =
    ([gA1, gA3, gB2, gA3, gC1, gA1, gC2, gB3, gC1, gA2, gC2].map
      fun g => (g : M4)).prod := by
  decide

theorem w21 : (x21 : M4) =
    ([gA3, gC2, gA3, gC1, gB1, gB3, gC1, gA3, gA2, gC1, gB2].map
      fun g => (g : M4)).prod := by
  decide

theorem w23 : (x23 : M4) =
    ([gA1, gA3, gB2, gA3, gB2].map
      fun g => (g : M4)).prod := by
  decide

theorem w30 : (x30 : M4) =
    ([gB3, gC1, gA3, gC2, gC1, gB3, gC2, gA3, gA2, gC2].map
      fun g => (g : M4)).prod := by
  decide

theorem w31 : (x31 : M4) =
    ([gA2, gA3, gB2, gA3, gC1, gA2, gC2, gB2, gC1, gA1, gC2].map
      fun g => (g : M4)).prod := by
  decide

theorem w32 : (x32 : M4) =
    ([gB1, gB3, gA3, gB2, gA3].map
      fun g => (g : M4)).prod := by
  decide

theorem core_three (Γ : Subgroup SL(4, ZMod 3))
    (h1 : ∀ x : SL(4, ZMod 3), (x : M4) * tM = tM * (x : M4) →
      (x : M4) * BDa * (x : M4)ᵀ = BDa → x ∈ Γ)
    (h2 : ∀ x : SL(4, ZMod 3), (x : M4) * tM = tM * (x : M4) →
      (x : M4) * (jM * BDa) * (x : M4)ᵀ = jM * BDa → x ∈ Γ)
    (h3 : ∀ x : SL(4, ZMod 3), (x : M4) * jM = jM * (x : M4) →
      (x : M4) * BDa * (x : M4)ᵀ = BDa → x ∈ Γ) :
    Γ = ⊤ := by
  have mA1 : gA1 ∈ Γ := h1 _ (by decide) (by decide)
  have mA2 : gA2 ∈ Γ := h1 _ (by decide) (by decide)
  have mA3 : gA3 ∈ Γ := h1 _ (by decide) (by decide)
  have mB1 : gB1 ∈ Γ := h2 _ (by decide) (by decide)
  have mB2 : gB2 ∈ Γ := h2 _ (by decide) (by decide)
  have mB3 : gB3 ∈ Γ := h2 _ (by decide) (by decide)
  have mC1 : gC1 ∈ Γ := h3 _ (by decide) (by decide)
  have mC2 : gC2 ∈ Γ := h3 _ (by decide) (by decide)
  have h01 : x01 ∈ Γ := mem_of_coe_prod _ (by simp [mA1, mA3, mB1, mB3, mC1, mC2]) w01
  have h02 : x02 ∈ Γ := mem_of_coe_prod _ (by simp [mA1, mA3, mB3, mC1, mC2]) w02
  have h03 : x03 ∈ Γ :=
    mem_of_coe_prod _ (by simp [mA1, mA2, mA3, mB2, mB3, mC1, mC2]) w03
  have h10 : x10 ∈ Γ := mem_of_coe_prod _ (by simp [mA1, mA3, mB1, mB3, mC1, mC2]) w10
  have h12 : x12 ∈ Γ := mem_of_coe_prod _ (by simp [mA1, mA3, mB2, mC1, mC2]) w12
  have h13 : x13 ∈ Γ := mem_of_coe_prod _ (by simp [mA2, mA3, mB2, mC1, mC2]) w13
  have h20 : x20 ∈ Γ :=
    mem_of_coe_prod _ (by simp [mA1, mA2, mA3, mB2, mB3, mC1, mC2]) w20
  have h21 : x21 ∈ Γ :=
    mem_of_coe_prod _ (by simp [mA2, mA3, mB1, mB2, mB3, mC1, mC2]) w21
  have h23 : x23 ∈ Γ := mem_of_coe_prod _ (by simp [mA1, mA3, mB2]) w23
  have h30 : x30 ∈ Γ := mem_of_coe_prod _ (by simp [mA2, mA3, mB3, mC1, mC2]) w30
  have h31 : x31 ∈ Γ := mem_of_coe_prod _ (by simp [mA1, mA2, mA3, mB2, mC1, mC2]) w31
  have h32 : x32 ∈ Γ := mem_of_coe_prod _ (by simp [mA3, mB1, mB2, mB3]) w32
  exact top_of_root_elements' Γ h01 h02 h03 h10 h12 h13 h20 h21 h23 h30 h31 h32

@[expose] def q1 (κ : ZMod 3) : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  if κ = 1 then 1 else !![0, -1; 1, 0]

@[expose] def q2 (p q : ZMod 3) : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  if p = 1 then (if q = 1 then 1 else !![1, -1; 1, 1])
  else (if q = 1 then !![1, 1; -1, 1] else !![0, -1; 1, 0])

theorem frame_norm : ∀ κ p q : ZMod 3, κ ≠ 0 → p ≠ 0 → q ≠ 0 →
    (bd2 (q1 κ) (q2 p q)).det ≠ 0 ∧ jM * bd2 (q1 κ) (q2 p q) = bd2 (q1 κ) (q2 p q) * jM ∧
      tM * bd2 (q1 κ) (q2 p q) = bd2 (q1 κ) (q2 p q) * tM ∧
      bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p] =
        bd2 (q1 κ) (q2 p q) * BDa * (bd2 (q1 κ) (q2 p q))ᵀ := by
  decide

theorem Gt_eq : (Gt : M4) = tM := by decide

theorem bd2_C0 :
    bd2 (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 3)) !![0, -1; 1, 0] = jM := by
  decide

theorem da_frame_three (B X i : M4) (hBt : Bᵀ = B) (hBns : ¬ IsSquare B.det) (hXX : X * X = 1)
    (hX1 : X ≠ 1) (hXm1 : X ≠ -1) (hii : i * i = (-1 : ZMod 3) • (1 : M4))
    (hXi : X * i = i * X) (hXB : X * B = B * Xᵀ) (hiB : i * B = B * iᵀ) :
    ∃ P : GL (Fin 4) (ZMod 3), B = (P : M4) * BDa * (P : M4)ᵀ ∧ i * (P : M4) = (P : M4) * jM ∧
      (X * (P : M4) = (P : M4) * tM ∨ X * (P : M4) = -((P : M4) * tM)) := by
  have hF4 : Nat.card (ZMod 3) % 4 = 3 := by simp
  obtain ⟨P, κ, p, q, hκ, hn, hBP, hiP, hXP⟩ :=
    da_frame hF4 B X i hBt hBns hXX hX1 hXm1 hii hXi hXB hiB
  have hp : p ≠ 0 := fun h => hn ⟨q, by rw [h]; ring⟩
  have hq : q ≠ 0 := fun h => hn ⟨p, by rw [h]; ring⟩
  obtain ⟨hdet, hQj, hQt, hQB⟩ := frame_norm κ p q hκ hp hq
  rw [Gt_eq] at hXP
  rw [bd2_C0] at hiP
  refine ⟨P * Matrix.GeneralLinearGroup.mkOfDetNeZero (bd2 (q1 κ) (q2 p q)) hdet, ?_, ?_, ?_⟩
  · show B = ((P : M4) * bd2 (q1 κ) (q2 p q)) * BDa * ((P : M4) * bd2 (q1 κ) (q2 p q))ᵀ
    rw [Matrix.transpose_mul]
    calc B = (P : M4) * bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p] * (P : M4)ᵀ := hBP
      _ = _ := by rw [hQB]; simp only [Matrix.mul_assoc]
  · show i * ((P : M4) * bd2 (q1 κ) (q2 p q)) = ((P : M4) * bd2 (q1 κ) (q2 p q)) * jM
    rw [← Matrix.mul_assoc, hiP, Matrix.mul_assoc, hQj, ← Matrix.mul_assoc]
  · rcases hXP with h | h
    · left
      show X * ((P : M4) * bd2 (q1 κ) (q2 p q)) = ((P : M4) * bd2 (q1 κ) (q2 p q)) * tM
      rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, hQt, ← Matrix.mul_assoc]
    · right
      show X * ((P : M4) * bd2 (q1 κ) (q2 p q)) = -(((P : M4) * bd2 (q1 κ) (q2 p q)) * tM)
      rw [← Matrix.mul_assoc, h, Matrix.neg_mul, Matrix.mul_assoc, hQt, ← Matrix.mul_assoc]

end GenLocL4ThreeDa

local notation "K3" => ZMod 3

open CFSG.ComponentClassification.CatalogueBHigherLinearAction in
theorem classDa_three : ∀ (B X i : Matrix (Fin 4) (Fin 4) K3), Bᵀ = B → B.det ≠ 0 →
    ¬ IsSquare B.det → X * X = 1 → X.det = 1 → X ≠ 1 → X ≠ -1 →
    i * i = (-1 : K3) • (1 : Matrix (Fin 4) (Fin 4) K3) → X * i = i * X →
    X * B = B * Xᵀ → i * B = B * iᵀ → ∀ Γ : Subgroup SL(4, K3),
      (∀ x : SL(4, K3), (x : Matrix (Fin 4) (Fin 4) K3) * X = X * (x : Matrix (Fin 4) (Fin 4) K3) →
        (x : Matrix (Fin 4) (Fin 4) K3) * B * (x : Matrix (Fin 4) (Fin 4) K3)ᵀ = B → x ∈ Γ) →
      (∀ x : SL(4, K3), (x : Matrix (Fin 4) (Fin 4) K3) * X = X * (x : Matrix (Fin 4) (Fin 4) K3) →
        (x : Matrix (Fin 4) (Fin 4) K3) * (i * B) * (x : Matrix (Fin 4) (Fin 4) K3)ᵀ = i * B →
          x ∈ Γ) →
      (∀ x : SL(4, K3), (x : Matrix (Fin 4) (Fin 4) K3) * i = i * (x : Matrix (Fin 4) (Fin 4) K3) →
        (x : Matrix (Fin 4) (Fin 4) K3) * B * (x : Matrix (Fin 4) (Fin 4) K3)ᵀ = B → x ∈ Γ) →
      Γ = ⊤ := by
  intro B X i hBt hBdet hBd hXX hXdet hX1 hXm1 hii hXi hXB hiB Γ hP1 hP2 hP3
  obtain ⟨P, hBP, hiP, hXP⟩ :=
    GenLocL4ThreeDa.da_frame_three B X i hBt hBd hXX hX1 hXm1 hii hXi hXB hiB
  have hPP : (P : Matrix (Fin 4) (Fin 4) K3) *
      ((P⁻¹ : GL (Fin 4) K3) : Matrix (Fin 4) (Fin 4) K3) = 1 := GenLocL4Out.PiP' P
  have hPiP : ((P⁻¹ : GL (Fin 4) K3) : Matrix (Fin 4) (Fin 4) K3) *
      (P : Matrix (Fin 4) (Fin 4) K3) = 1 := GenLocL4Out.PPi P
  set Pm : Matrix (Fin 4) (Fin 4) K3 := (P : Matrix (Fin 4) (Fin 4) K3)
  set Pi : Matrix (Fin 4) (Fin 4) K3 := ((P⁻¹ : GL (Fin 4) K3) : Matrix (Fin 4) (Fin 4) K3)
  have hPt : Piᵀ * Pmᵀ = 1 := by rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  have hPt' : Pmᵀ * Piᵀ = 1 := by rw [← Matrix.transpose_mul, hPiP, Matrix.transpose_one]
  have ei : Pi * i * Pm = GenLocL4ThreeMat.jM := by
    rw [Matrix.mul_assoc, hiP, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have eB : Pi * B * Piᵀ = GenLocL4ThreeDa.BDa := by
    rw [hBP]
    calc Pi * (Pm * GenLocL4ThreeDa.BDa * Pmᵀ) * Piᵀ =
        (Pi * Pm) * GenLocL4ThreeDa.BDa * (Pmᵀ * Piᵀ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPiP, hPt', Matrix.one_mul, Matrix.mul_one]
  have eiB : Pi * (i * B) * Piᵀ = GenLocL4ThreeMat.jM * GenLocL4ThreeDa.BDa := by
    rw [← ei, ← eB]
    calc Pi * (i * B) * Piᵀ = Pi * i * (Pm * Pi) * B * Piᵀ := by
          rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  have eX : Pi * X * Pm = GenLocL4ThreeMat.tM ∨ Pi * X * Pm = -GenLocL4ThreeMat.tM := by
    rcases hXP with h | h
    · left
      rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
    · right
      rw [Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have hcommX : ∀ z : SL(4, K3), (z : Matrix (Fin 4) (Fin 4) K3) * GenLocL4ThreeMat.tM =
      GenLocL4ThreeMat.tM * (z : Matrix (Fin 4) (Fin 4) K3) →
      ((slConjugation 4 K3 P).toMonoidHom z : Matrix (Fin 4) (Fin 4) K3) * X =
        X * ((slConjugation 4 K3 P).toMonoidHom z : Matrix (Fin 4) (Fin 4) K3) := by
    intro z hz
    refine (GenLocL4Out.conj_commute_iff P z X).2 ?_
    rcases eX with e | e
    · rw [e]; exact hz
    · rw [e, Matrix.mul_neg, Matrix.neg_mul, hz]
  refine GenLocL4Out.top_of_conj Γ P
    (GenLocL4ThreeDa.core_three (Γ.comap (slConjugation 4 K3 P).toMonoidHom) ?_ ?_ ?_)
  · intro x hx1 hx2
    show (slConjugation 4 K3 P).toMonoidHom x ∈ Γ
    exact hP1 _ (hcommX x hx1) ((GenLocL4Out.conj_form_iff P x B).2 (by rw [eB]; exact hx2))
  · intro x hx1 hx2
    show (slConjugation 4 K3 P).toMonoidHom x ∈ Γ
    exact hP2 _ (hcommX x hx1)
      ((GenLocL4Out.conj_form_iff P x (i * B)).2 (by rw [eiB]; exact hx2))
  · intro x hx1 hx2
    show (slConjugation 4 K3 P).toMonoidHom x ∈ Γ
    exact hP3 _ ((GenLocL4Out.conj_commute_iff P x i).2 (by rw [ei]; exact hx1))
      ((GenLocL4Out.conj_form_iff P x B).2 (by rw [eB]; exact hx2))

end CFSG.GH74.Generic.BProg.B2
