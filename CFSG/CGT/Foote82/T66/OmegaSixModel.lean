module

public import Certificates.Certificate919001
public import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.CGT.Foote82.T66.MC2Arith

public section

namespace CFSG.CGT.Foote82.OmegaSix

open Matrix CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec.Z6NA
  CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem involCheck_holds : involCheck () = true :=
  Certificates.certificate919001.1

theorem isomCheck_holds : isomCheck () = true :=
  Certificates.certificate919001.2.1

theorem commCheck_holds : commCheck () = true :=
  Certificates.certificate919001.2.2.1

theorem enumCheck_holds : enumCheck () = true :=
  Certificates.certificate919001.2.2.2.1

theorem relCheck_holds : relCheck () = true :=
  Certificates.certificate919001.2.2.2.2

theorem involCheck_spec :
    aMat * aMat = 1 ∧ bMat * (bMat * (bMat * (bMat * bMat))) = 1 ∧ c1Mat * c1Mat = 1 ∧
      c2Mat * c2Mat = 1 ∧ d1Mat * d1Mat = 1 ∧ d2Mat * d2Mat = 1 := by
  have h := involCheck_holds
  simp only [involCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

@[expose] def aGL : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ⟨aMat, aMat, involCheck_spec.1, involCheck_spec.1⟩

@[expose] def bGL : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ⟨bMat, bMat * (bMat * (bMat * bMat)), involCheck_spec.2.1, by
    simp only [mul_assoc]
    exact involCheck_spec.2.1⟩

@[expose] def c1GL : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ⟨c1Mat, c1Mat, involCheck_spec.2.2.1, involCheck_spec.2.2.1⟩

@[expose] def c2GL : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ⟨c2Mat, c2Mat, involCheck_spec.2.2.2.1, involCheck_spec.2.2.2.1⟩

@[expose] def d1GL : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ⟨d1Mat, d1Mat, involCheck_spec.2.2.2.2.1, involCheck_spec.2.2.2.2.1⟩

@[expose] def d2GL : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ⟨d2Mat, d2Mat, involCheck_spec.2.2.2.2.2, involCheck_spec.2.2.2.2.2⟩

theorem q6_eq (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) :
    q6 v = CFSG.PGLModel.minusQuadForm 2 (1 : ZMod 2) 1 v := by
  simp only [q6, CFSG.PGLModel.minusQuadForm, Fin.sum_univ_two, one_mul]

theorem mem_orthogonalMinus_of_isomB {A : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (h : isomB (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) = true) :
    A ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1 := by
  apply Subgroup.subset_closure
  intro v
  have hv := (decide_eq_true_eq.mp h) v
  rwa [q6_eq, q6_eq] at hv

theorem isomCheck_spec :
    c1GL ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1 ∧
      c2GL ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1 ∧
      d1GL ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1 ∧
      d2GL ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1 := by
  have h := isomCheck_holds
  simp only [isomCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨mem_orthogonalMinus_of_isomB h1, mem_orthogonalMinus_of_isomB h2,
    mem_orthogonalMinus_of_isomB h3, mem_orthogonalMinus_of_isomB h4⟩

theorem aGL_eq : aGL = ⁅c1GL, c2GL⁆ := by
  have h := commCheck_holds
  simp only [commCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  refine Units.ext ?_
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul]
  exact h.1.symm

theorem bGL_eq : bGL = ⁅d1GL, d2GL⁆ := by
  have h := commCheck_holds
  simp only [commCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  refine Units.ext ?_
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul]
  exact h.2.symm

theorem aGL_mem : aGL ∈ omegaMinusTwo 2 := by
  rw [aGL_eq]
  exact Subgroup.commutator_mem_commutator isomCheck_spec.1 isomCheck_spec.2.1

theorem bGL_mem : bGL ∈ omegaMinusTwo 2 := by
  rw [bGL_eq]
  exact Subgroup.commutator_mem_commutator isomCheck_spec.2.2.1 isomCheck_spec.2.2.2

theorem q6_mulVec_of_mem {A : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (hA : A ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1) (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) :
    q6 ((A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ v) = q6 v := by
  replace hA : A ∈ Subgroup.closure {A : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) | ∀ v,
      CFSG.PGLModel.minusQuadForm 2 (1 : ZMod 2) 1
        ((A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ v) =
      CFSG.PGLModel.minusQuadForm 2 (1 : ZMod 2) 1 v} := hA
  rw [q6_eq, q6_eq]
  induction hA using Subgroup.closure_induction generalizing v with
  | mem A hA => exact hA v
  | one => rw [Units.val_one, one_mulVec]
  | mul A B _ _ hA hB => rw [Units.val_mul, ← mulVec_mulVec, hA, hB]
  | inv A _ hA =>
    rw [← hA, mulVec_mulVec, Units.mul_inv, one_mulVec]

theorem omegaMinusTwo_le_orthogonalMinus :
    omegaMinusTwo 2 ≤ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1 :=
  Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem conj_mulVec (T x : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2))
    (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) :
    ((T * x * T⁻¹ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ
      ((T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ v) =
      (T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ
        ((x : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ v) := by
  rw [mulVec_mulVec, Units.val_mul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one,
    ← mulVec_mulVec]

theorem conj_mem_omegaMinusTwo {g y : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (hg : g ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1) (hy : y ∈ omegaMinusTwo 2) :
    g * y * g⁻¹ ∈ omegaMinusTwo 2 := by
  have h : g * y * g⁻¹ = ⁅g, y⁆ * y := by
    rw [commutatorElement_def]
    group
  rw [h]
  exact mul_mem (Subgroup.commutator_mem_commutator hg (omegaMinusTwo_le_orthogonalMinus hy)) hy

@[expose] def gen6 (i : ℕ) : ↥(omegaMinusTwo 2) :=
  if i = 0 then ⟨aGL, aGL_mem⟩ else ⟨bGL, bGL_mem⟩

theorem genA6_size : (genA6 ()).size = 2 := rfl

theorem genA6_get :
    ∀ j < (genA6 ()).size, (genA6 ())[j]! = glArr (gen6 j) := by
  intro j hj
  rw [genA6_size] at hj
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · rfl
  · rfl

theorem isActArr_gen6 :
    ∀ i < 2, FoxH1.IsActArr (fun (g : ↥(omegaMinusTwo 2)) a =>
      ((g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ a)
      64 cvec (gen6 i) (genA6 ())[i]! := by
  intro i hi
  rw [genA6_get i (by rw [genA6_size]; exact hi), glArr]
  exact isActArr_marr fun v => rfl

theorem omegaEnum_spec :
    enumOK (omegaEnum ()) (genA6 ()) = true ∧ (omegaEnum ()).elems.size = 25920 := by
  have h := enumCheck_holds
  simp only [enumCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem closure_gen6 :
    Subgroup.closure (gen6 '' Set.Iio 2) = ⊤ := by
  have hcard := card_closure_eq_of_enumOK (isArrCode_glArr (omegaMinusTwo 2)) genA6_get
    omegaEnum_spec.1
  rw [omegaEnum_spec.2, genA6_size] at hcard
  apply Subgroup.eq_top_of_card_eq
  rw [hcard, MC2.card_omegaMinusTwo_two]

theorem exists_glArr_eq {i : ℕ}
    (hi : i < (omegaEnum ()).elems.size) :
    ∃ x : ↥(omegaMinusTwo 2), glArr x = (omegaEnum ()).elems[i]! := by
  have htree : treeOK (omegaEnum ()) (genA6 ()) = true := by
    have h := omegaEnum_spec.1
    simp only [enumOK, Bool.and_eq_true] at h
    exact h.1.1
  obtain ⟨x, -, hx⟩ := exists_mem_closure_of_treeOK (isArrCode_glArr (omegaMinusTwo 2)) genA6_get
    htree i hi
  exact ⟨x, hx⟩

theorem lookup_glArr_isSome (x : ↥(omegaMinusTwo 2)) :
    ((omegaEnum ()).lookup (glArr x)).isSome := by
  refine lookup_isSome_of_mem_closure (isArrCode_glArr (omegaMinusTwo 2)) genA6_get
    omegaEnum_spec.1 ?_
  rw [genA6_size, closure_gen6]
  exact Subgroup.mem_top x

theorem relators_letters : ∀ w ∈ relators, ∀ i ∈ w, i < 2 := by
  decide

theorem relators_spec :
    ∀ w ∈ relators, (∀ i ∈ w, i < 2) ∧ (w.map gen6).prod = 1 := by
  intro w hw
  refine ⟨relators_letters w hw, (isArrCode_glArr (omegaMinusTwo 2)).injective ?_⟩
  have h := relCheck_holds
  simp only [relCheck, List.all_eq_true, beq_iff_eq] at h
  rw [arr_prod_map (isArrCode_glArr (omegaMinusTwo 2)) w fun i hi =>
      genA6_get i (by rw [genA6_size]; exact relators_letters w hw i hi),
    (isArrCode_glArr (omegaMinusTwo 2)).one, h w hw]

end CFSG.CGT.Foote82.OmegaSix
