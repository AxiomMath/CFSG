module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4QRank2
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
public import CFSG.GH74.Generic.BProg.B2.GenLoc4Defs
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

open Matrix Matrix.SpecialLinearGroup CFSG GenLocL4Q
open scoped commutatorElement

namespace GenLocL4Q

variable {F : Type} [Field F]

theorem top_of_offblock (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (e02 : ∀ t : F, tv 0 2 (by decide) t ∈ Γ) (e03 : ∀ t : F, tv 0 3 (by decide) t ∈ Γ)
    (e12 : ∀ t : F, tv 1 2 (by decide) t ∈ Γ) (e13 : ∀ t : F, tv 1 3 (by decide) t ∈ Γ)
    (e20 : ∀ t : F, tv 2 0 (by decide) t ∈ Γ) (e21 : ∀ t : F, tv 2 1 (by decide) t ∈ Γ)
    (e30 : ∀ t : F, tv 3 0 (by decide) t ∈ Γ) (e31 : ∀ t : F, tv 3 1 (by decide) t ∈ Γ) : Γ = ⊤ := by
  have e01 : ∀ t : F, tv 0 1 (by decide) t ∈ Γ := fun t => by
    have key := comm_mem Γ (e02 t) (e21 1)
    rw [comm_tv (by decide) (by decide) (by decide), mul_one] at key
    exact key
  have e10 : ∀ t : F, tv 1 0 (by decide) t ∈ Γ := fun t => by
    have key := comm_mem Γ (e12 t) (e20 1)
    rw [comm_tv (by decide) (by decide) (by decide), mul_one] at key
    exact key
  have e23 : ∀ t : F, tv 2 3 (by decide) t ∈ Γ := fun t => by
    have key := comm_mem Γ (e20 t) (e03 1)
    rw [comm_tv (by decide) (by decide) (by decide), mul_one] at key
    exact key
  have e32 : ∀ t : F, tv 3 2 (by decide) t ∈ Γ := fun t => by
    have key := comm_mem Γ (e31 t) (e12 1)
    rw [comm_tv (by decide) (by decide) (by decide), mul_one] at key
    exact key
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (K := F) (n := 4),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, t, rfl⟩
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact e01 t | exact e02 t | exact e03 t | exact e10 t | exact e12 t | exact e13 t
    | exact e20 t | exact e21 t | exact e23 t | exact e30 t | exact e31 t | exact e32 t

@[expose] def Uel (M : Matrix (Fin 2) (Fin 2) F) : Matrix.SpecialLinearGroup (Fin 4) F :=
  tv 0 2 (by decide) (M 0 0) * tv 0 3 (by decide) (M 0 1) * tv 1 2 (by decide) (M 1 0) *
    tv 1 3 (by decide) (M 1 1)

@[expose] def Lel (M : Matrix (Fin 2) (Fin 2) F) : Matrix.SpecialLinearGroup (Fin 4) F :=
  tv 2 0 (by decide) (M 0 0) * tv 2 1 (by decide) (M 0 1) * tv 3 0 (by decide) (M 1 0) *
    tv 3 1 (by decide) (M 1 1)

theorem Uel_coe (M : Matrix (Fin 2) (Fin 2) F) :
    ((Uel M : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      !![1, 0, M 0 0, M 0 1; 0, 1, M 1 0, M 1 1; 0, 0, 1, 0; 0, 0, 0, 1] := by
  unfold Uel tv
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]

theorem Lel_coe (M : Matrix (Fin 2) (Fin 2) F) :
    ((Lel M : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      !![1, 0, 0, 0; 0, 1, 0, 0; M 0 0, M 0 1, 1, 0; M 1 0, M 1 1, 0, 1] := by
  unfold Lel tv
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]

theorem Uel_add (M N : Matrix (Fin 2) (Fin 2) F) : Uel M * Uel N = Uel (M + N) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Uel_coe, Uel_coe, Uel_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply]
  all_goals ring

theorem Lel_add (M N : Matrix (Fin 2) (Fin 2) F) : Lel M * Lel N = Lel (M + N) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Lel_coe, Lel_coe, Lel_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply]

@[expose] def bd (P Q : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![P 0 0, P 0 1, 0, 0; P 1 0, P 1 1, 0, 0; 0, 0, Q 0 0, Q 0 1; 0, 0, Q 1 0, Q 1 1]

theorem bd_mul (P Q P' Q' : Matrix (Fin 2) (Fin 2) F) : bd P Q * bd P' Q' = bd (P * P') (Q * Q') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem Uel_comm_bd (M P Q : Matrix (Fin 2) (Fin 2) F) (h : M * Q = P * M) :
    ((Uel M : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * bd P Q =
      bd P Q * (Uel M : Matrix.SpecialLinearGroup (Fin 4) F) := by
  rw [Uel_coe]
  have h00 := congr_fun (congr_fun h 0) 0
  have h01 := congr_fun (congr_fun h 0) 1
  have h10 := congr_fun (congr_fun h 1) 0
  have h11 := congr_fun (congr_fun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first | exact h00 | exact h01 | exact h10 | exact h11

theorem Lel_comm_bd (M P Q : Matrix (Fin 2) (Fin 2) F) (h : M * P = Q * M) :
    ((Lel M : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * bd P Q =
      bd P Q * (Lel M : Matrix.SpecialLinearGroup (Fin 4) F) := by
  rw [Lel_coe]
  have h00 := congr_fun (congr_fun h 0) 0
  have h01 := congr_fun (congr_fun h 0) 1
  have h10 := congr_fun (congr_fun h 1) 0
  have h11 := congr_fun (congr_fun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first | exact h00 | exact h01 | exact h10 | exact h11

@[expose] def Y1 (c p s' : F) : Matrix (Fin 2) (Fin 2) F := !![p, -(c * s'); s', -p]

@[expose] def C2 (c : F) : Matrix (Fin 2) (Fin 2) F := !![0, c; 1, 0]

macro "mat2" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;> simp [C2, Y1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring))

theorem C2_Y1 (c p s' : F) : C2 c * Y1 c p s' = -(Y1 c p s' * C2 c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C2, Y1, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem Y1_sq (c p s' : F) : Y1 c p s' * Y1 c p s' = (p ^ 2 - c * s' ^ 2) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Y1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem C2_sq (c : F) : C2 c * C2 c = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C2, Matrix.mul_apply, Fin.sum_univ_two]

theorem Uel_four (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F)) (B0 B1 B2 B3 : Matrix (Fin 2) (Fin 2) F)
    (h0 : ∀ t : F, Uel (t • B0) ∈ Γ) (h1 : ∀ t : F, Uel (t • B1) ∈ Γ) (h2 : ∀ t : F, Uel (t • B2) ∈ Γ)
    (h3 : ∀ t : F, Uel (t • B3) ∈ Γ) (μ0 μ1 μ2 μ3 : F) :
    Uel (μ0 • B0 + μ1 • B1 + μ2 • B2 + μ3 • B3) ∈ Γ := by
  rw [← Uel_add (μ0 • B0 + μ1 • B1 + μ2 • B2) (μ3 • B3), ← Uel_add (μ0 • B0 + μ1 • B1) (μ2 • B2),
    ← Uel_add (μ0 • B0) (μ1 • B1)]
  exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem (h0 _) (h1 _)) (h2 _)) (h3 _)

theorem Lel_four (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F)) (B0 B1 B2 B3 : Matrix (Fin 2) (Fin 2) F)
    (h0 : ∀ t : F, Lel (t • B0) ∈ Γ) (h1 : ∀ t : F, Lel (t • B1) ∈ Γ) (h2 : ∀ t : F, Lel (t • B2) ∈ Γ)
    (h3 : ∀ t : F, Lel (t • B3) ∈ Γ) (μ0 μ1 μ2 μ3 : F) :
    Lel (μ0 • B0 + μ1 • B1 + μ2 • B2 + μ3 • B3) ∈ Γ := by
  rw [← Lel_add (μ0 • B0 + μ1 • B1 + μ2 • B2) (μ3 • B3), ← Lel_add (μ0 • B0 + μ1 • B1) (μ2 • B2),
    ← Lel_add (μ0 • B0) (μ1 • B1)]
  exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem (h0 _) (h1 _)) (h2 _)) (h3 _)

theorem mat_comb (c p s' : F) (hc : c ≠ 0) (h2 : (2 : F) ≠ 0) (hm : p ^ 2 - c * s' ^ 2 ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) F) :
    M = ((M 0 0 + M 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) F) +
      ((M 0 1 + c * M 1 0) / (2 * c)) • C2 c +
      ((p * (M 0 0 - M 1 1) + s' * (M 0 1 - c * M 1 0)) / (2 * (p ^ 2 - c * s' ^ 2))) • Y1 c p s' +
      (-(c * s' * (M 0 0 - M 1 1) + p * (M 0 1 - c * M 1 0)) / (2 * c * (p ^ 2 - c * s' ^ 2))) •
        (C2 c * Y1 c p s') := by
  have hm' : p ^ 2 - s' ^ 2 * c ≠ 0 := by intro h; apply hm; linear_combination h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C2, Y1]
  all_goals (field_simp; ring)

theorem top_of_split_model (h2 : (2 : F) ≠ 0) {c p s' : F} (hc : c ≠ 0) (hm : p ^ 2 - c * s' ^ 2 ≠ 0)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (H1 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * bd (C2 c) (C2 c) = bd (C2 c) (C2 c) * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * bd (Y1 c p s') (Y1 c p s') =
        bd (Y1 c p s') (Y1 c p s') * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H2 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * bd (C2 c) (C2 c) = bd (C2 c) (C2 c) * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * bd (Y1 c p s') (-(Y1 c p s')) =
        bd (Y1 c p s') (-(Y1 c p s')) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H3 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * bd (Y1 c p s') (Y1 c p s') =
        bd (Y1 c p s') (Y1 c p s') * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * bd (C2 c) (-(C2 c)) = bd (C2 c) (-(C2 c)) * (g : Matrix (Fin 4) (Fin 4) F) →
        g ∈ Γ)
    (H4 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * bd (C2 c * Y1 c p s') (C2 c * Y1 c p s') =
        bd (C2 c * Y1 c p s') (C2 c * Y1 c p s') * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * bd (C2 c) (-(C2 c)) = bd (C2 c) (-(C2 c)) * (g : Matrix (Fin 4) (Fin 4) F) →
        g ∈ Γ) : Γ = ⊤ := by
  have hCY := C2_Y1 c p s'
  have hU0 : ∀ t : F, Uel (t • (1 : Matrix (Fin 2) (Fin 2) F)) ∈ Γ := fun t =>
    H1 _ (Uel_comm_bd _ _ _ (by mat2))
      (Uel_comm_bd _ _ _ (by mat2))
  have hU1 : ∀ t : F, Uel (t • C2 c) ∈ Γ := fun t =>
    H2 _ (Uel_comm_bd _ _ _ (by mat2))
      (Uel_comm_bd _ _ _ (by mat2))
  have hU2 : ∀ t : F, Uel (t • Y1 c p s') ∈ Γ := fun t =>
    H3 _ (Uel_comm_bd _ _ _ (by mat2))
      (Uel_comm_bd _ _ _ (by mat2))
  have hU3 : ∀ t : F, Uel (t • (C2 c * Y1 c p s')) ∈ Γ := fun t =>
    H4 _ (Uel_comm_bd _ _ _ (by mat2))
      (Uel_comm_bd _ _ _ (by mat2))
  have hL0 : ∀ t : F, Lel (t • (1 : Matrix (Fin 2) (Fin 2) F)) ∈ Γ := fun t =>
    H1 _ (Lel_comm_bd _ _ _ (by mat2)) (Lel_comm_bd _ _ _ (by mat2))
  have hL1 : ∀ t : F, Lel (t • C2 c) ∈ Γ := fun t =>
    H2 _ (Lel_comm_bd _ _ _ (by mat2)) (Lel_comm_bd _ _ _ (by mat2))
  have hL2 : ∀ t : F, Lel (t • Y1 c p s') ∈ Γ := fun t =>
    H3 _ (Lel_comm_bd _ _ _ (by mat2)) (Lel_comm_bd _ _ _ (by mat2))
  have hL3 : ∀ t : F, Lel (t • (C2 c * Y1 c p s')) ∈ Γ := fun t =>
    H4 _ (Lel_comm_bd _ _ _ (by mat2)) (Lel_comm_bd _ _ _ (by mat2))
  have hUall : ∀ M : Matrix (Fin 2) (Fin 2) F, Uel M ∈ Γ := fun M => by
    have h := Uel_four Γ 1 (C2 c) (Y1 c p s') (C2 c * Y1 c p s') hU0 hU1 hU2 hU3
      ((M 0 0 + M 1 1) / 2) ((M 0 1 + c * M 1 0) / (2 * c))
      ((p * (M 0 0 - M 1 1) + s' * (M 0 1 - c * M 1 0)) / (2 * (p ^ 2 - c * s' ^ 2)))
      (-(c * s' * (M 0 0 - M 1 1) + p * (M 0 1 - c * M 1 0)) / (2 * c * (p ^ 2 - c * s' ^ 2)))
    rwa [← mat_comb c p s' hc h2 hm M] at h
  have hLall : ∀ M : Matrix (Fin 2) (Fin 2) F, Lel M ∈ Γ := fun M => by
    have h := Lel_four Γ 1 (C2 c) (Y1 c p s') (C2 c * Y1 c p s') hL0 hL1 hL2 hL3
      ((M 0 0 + M 1 1) / 2) ((M 0 1 + c * M 1 0) / (2 * c))
      ((p * (M 0 0 - M 1 1) + s' * (M 0 1 - c * M 1 0)) / (2 * (p ^ 2 - c * s' ^ 2)))
      (-(c * s' * (M 0 0 - M 1 1) + p * (M 0 1 - c * M 1 0)) / (2 * c * (p ^ 2 - c * s' ^ 2)))
    rwa [← mat_comb c p s' hc h2 hm M] at h
  have tz : ∀ (i j : Fin 4) (h : i ≠ j), tv i j h (0 : F) = 1 := fun i j h => by
    apply Subtype.ext; simp [tv]
  refine top_of_offblock Γ (fun t => ?_) (fun t => ?_) (fun t => ?_) (fun t => ?_)
    (fun t => ?_) (fun t => ?_) (fun t => ?_) (fun t => ?_)
  · have := hUall !![t, 0; 0, 0]
    simpa [Uel, tz] using this
  · have := hUall !![0, t; 0, 0]
    simpa [Uel, tz] using this
  · have := hUall !![0, 0; t, 0]
    simpa [Uel, tz] using this
  · have := hUall !![0, 0; 0, t]
    simpa [Uel, tz] using this
  · have := hLall !![t, 0; 0, 0]
    simpa [Lel, tz] using this
  · have := hLall !![0, t; 0, 0]
    simpa [Lel, tz] using this
  · have := hLall !![0, 0; t, 0]
    simpa [Lel, tz] using this
  · have := hLall !![0, 0; 0, t]
    simpa [Lel, tz] using this

end GenLocL4Q

end CFSG.GH74.Generic.BProg.B2
