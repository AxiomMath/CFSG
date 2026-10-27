module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeLeviModel

public section

namespace CFSG.ClassicalInvolution.RouteD.NodeModel

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_elt mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ClassicalInvolution.RouteD.LeviModel
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] noncomputable def Eu (F : Type) [Field F] : Mat4 F :=
  Matrix.single (Sum.inl 0) (Sum.inr 0) 1

@[expose] noncomputable def El (F : Type) [Field F] : Mat4 F :=
  Matrix.single (Sum.inr 0) (Sum.inl 0) 1

theorem mat_longBlock_zero_upper (c : F) :
    mat 2 F (longBlock F 2 0 (sl2Upper c)) = 1 + c • Eu F := by
  rw [longBlock_sl2Upper, mat_elt_positiveLong, Matrix.transvection, Eu, Matrix.smul_single,
    smul_eq_mul, mul_one]

theorem mat_longBlock_zero_lower (c : F) :
    mat 2 F (longBlock F 2 0 (sl2Lower c)) = 1 + c • El F := by
  rw [longBlock_sl2Lower, mat_elt_negativeLong, Matrix.transvection, El, Matrix.smul_single,
    smul_eq_mul, mul_one]

theorem map_Eu (σ : F ≃+* F) : (Eu F).map σ = Eu F := by
  ext a b
  simp [Eu, Matrix.single_apply]

theorem sigma_eq_one_of_long (A : gsp 2 F) (σ : F ≃+* F)
    (hfix : ∀ c : F, conjSp 2 F A (fieldSp 2 F σ (longBlock F 2 0 (sl2Upper c))) =
      longBlock F 2 0 (sl2Upper c)) : σ = 1 := by
  set a : Mat4 F := ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) with ha
  set b : Mat4 F := (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) with hb
  have hab : a * b = 1 := by
    rw [ha, hb, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hup : ∀ s : F, a * (1 + σ s • Eu F) * b = 1 + s • Eu F := by
    intro s
    have h := congrArg (mat 2 F) (hfix s)
    rw [mat_conjSp_fieldSp, mat_longBlock_zero_upper, ← ha, ← hb,
      map_one_add_smul σ s (map_Eu σ)] at h
    exact h
  have h1 : a * Eu F * b = Eu F := by
    have h := hup 1
    simp only [map_one, one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hab,
      Matrix.mul_assoc] at h
    have h' : a * (Eu F * b) = Eu F := add_left_cancel h
    rwa [← Matrix.mul_assoc] at h'
  have key : ∀ s : F, σ s • Eu F = s • Eu F := by
    intro s
    have h := hup s
    have e : a * (1 + σ s • Eu F) * b = 1 + σ s • (a * Eu F * b) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hab, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_assoc]
    rw [e, h1] at h
    exact add_left_cancel h
  refine RingEquiv.ext fun s => ?_
  have := congrFun (congrFun (key s) (Sum.inl 0)) (Sum.inr 0)
  simpa [Eu, Matrix.single_apply] using this

theorem shape_of_comm_long {a : Mat4 F} (h1 : a * Eu F = Eu F * a) (h2 : a * El F = El F * a) :
    a (Sum.inl 1) (Sum.inl 0) = 0 ∧ a (Sum.inr 1) (Sum.inl 0) = 0 ∧ a (Sum.inr 0) (Sum.inl 0) = 0 ∧
    a (Sum.inr 0) (Sum.inl 1) = 0 ∧ a (Sum.inr 0) (Sum.inr 1) = 0 ∧ a (Sum.inl 1) (Sum.inr 0) = 0 ∧
    a (Sum.inr 1) (Sum.inr 0) = 0 ∧ a (Sum.inl 0) (Sum.inr 0) = 0 ∧ a (Sum.inl 0) (Sum.inl 1) = 0 ∧
    a (Sum.inl 0) (Sum.inr 1) = 0 := by
  have e := fun i j => congrFun (congrFun h1 i) j
  have f := fun i j => congrFun (congrFun h2 i) j
  have e1 := e (Sum.inl 1) (Sum.inr 0)
  have e2 := e (Sum.inr 1) (Sum.inr 0)
  have e3 := e (Sum.inr 0) (Sum.inr 0)
  have e4 := e (Sum.inl 0) (Sum.inl 1)
  have e5 := e (Sum.inl 0) (Sum.inr 1)
  have f1 := f (Sum.inl 1) (Sum.inl 0)
  have f2 := f (Sum.inr 1) (Sum.inl 0)
  have f3 := f (Sum.inl 0) (Sum.inl 0)
  have f4 := f (Sum.inr 0) (Sum.inl 1)
  have f5 := f (Sum.inr 0) (Sum.inr 1)
  simp [Eu, El, Matrix.mul_apply, Matrix.single_apply] at e1 e2 e3 e4 e5 f1 f2 f3 f4 f5
  exact ⟨e1, e2, e3, e4.symm, e5.symm, f1, f2, f3, f4.symm, f5.symm⟩

theorem offDiag_of_torus {a : Mat4 F} (s : Fˣ) (hs : (s : F) ≠ ((s⁻¹ : Fˣ) : F))
    (hcomm : a * mat 2 F (longBlock F 2 1 (CFSG.ClassicalInvolution.WeakCT.torusHom F s)) =
      mat 2 F (longBlock F 2 1 (CFSG.ClassicalInvolution.WeakCT.torusHom F s)) * a) :
    a (Sum.inl 1) (Sum.inr 1) = 0 ∧ a (Sum.inr 1) (Sum.inl 1) = 0 := by
  rw [mat_longBlock, CFSG.ClassicalInvolution.WeakCT.coe_torusHom, blockMat_torusDiag] at hcomm
  rw [Units.val_inv_eq_inv_val] at hs
  have hne : (s : F)⁻¹ - (s : F) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have e1 := congrFun (congrFun hcomm (Sum.inl 1)) (Sum.inr 1)
  have e2 := congrFun (congrFun hcomm (Sum.inr 1)) (Sum.inl 1)
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e1 e2
  simp at e1 e2
  refine ⟨?_, ?_⟩
  · have : ((s : F)⁻¹ - (s : F)) * a (Sum.inl 1) (Sum.inr 1) = 0 := by
      linear_combination e1
    exact (mul_eq_zero.mp this).resolve_left hne
  · have : ((s : F)⁻¹ - (s : F)) * a (Sum.inr 1) (Sum.inl 1) = 0 := by
      linear_combination -e2
    exact (mul_eq_zero.mp this).resolve_left hne

theorem mat_comm_of_conj_fix (A : gsp 2 F) (x : StatedSp 2 F)
    (h : conjSp 2 F A (fieldSp 2 F 1 x) = x) :
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) * mat 2 F x =
      mat 2 F x * ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) := by
  have hba : (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h' := congrArg (mat 2 F) h
  rw [mat_conjSp_fieldSp, map_one_ringEquiv] at h'
  exact comm_of_conj_eq hba h'

theorem isDiag_of_entries {a : Mat4 F} (s1 : a (Sum.inl 0) (Sum.inl 1) = 0)
    (s2 : a (Sum.inl 0) (Sum.inr 0) = 0) (s3 : a (Sum.inl 0) (Sum.inr 1) = 0)
    (s4 : a (Sum.inl 1) (Sum.inl 0) = 0) (s5 : a (Sum.inl 1) (Sum.inr 0) = 0)
    (s6 : a (Sum.inl 1) (Sum.inr 1) = 0) (s7 : a (Sum.inr 0) (Sum.inl 0) = 0)
    (s8 : a (Sum.inr 0) (Sum.inl 1) = 0) (s9 : a (Sum.inr 0) (Sum.inr 1) = 0)
    (s10 : a (Sum.inr 1) (Sum.inl 0) = 0) (s11 : a (Sum.inr 1) (Sum.inl 1) = 0)
    (s12 : a (Sum.inr 1) (Sum.inr 0) = 0) : a.IsDiag := by
  intro i j hij
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp_all

theorem mat_comm_of_conj_fix' (A : gsp 2 F) (x : StatedSp 2 F) (h : conjSp 2 F A x = x) :
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) * mat 2 F x =
      mat 2 F x * ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) :=
  mat_comm_of_conj_fix A x (by rw [map_one, MulAut.one_apply]; exact h)

theorem diag_of_fix_long_torus (A : gsp 2 F) (σ : F ≃+* F)
    (hfix : ∀ B : SL(2, F), conjSp 2 F A (fieldSp 2 F σ (longBlock F 2 0 B)) = longBlock F 2 0 B)
    (s : Fˣ) (hs : (s : F) ≠ ((s⁻¹ : Fˣ) : F))
    (hT : conjSp 2 F A (fieldSp 2 F σ
      (longBlock F 2 1 (CFSG.ClassicalInvolution.WeakCT.torusHom F s))) =
        longBlock F 2 1 (CFSG.ClassicalInvolution.WeakCT.torusHom F s)) :
    σ = 1 ∧ ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F).IsDiag := by
  have hσ := sigma_eq_one_of_long A σ (fun c => hfix (sl2Upper c))
  subst hσ
  refine ⟨rfl, ?_⟩
  have h1 : ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) * Eu F =
      Eu F * ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) := by
    have h := mat_comm_of_conj_fix A _ (hfix (sl2Upper 1))
    rw [mat_longBlock_zero_upper] at h
    simp only [one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  have h2 : ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) * El F =
      El F * ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) := by
    have h := mat_comm_of_conj_fix A _ (hfix (sl2Lower 1))
    rw [mat_longBlock_zero_lower] at h
    simp only [one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := shape_of_comm_long h1 h2
  obtain ⟨t1, t2⟩ := offDiag_of_torus s hs (mat_comm_of_conj_fix A _ hT)
  exact isDiag_of_entries s9 s8 s10 s1 s6 t1 s3 s4 s5 s2 t2 s7

theorem fix_shortBlock_dichotomy (h2 : (2 : F) ≠ 0) (A : gsp 2 F) (σ : F ≃+* F)
    (hfix : ∀ B : SL(2, F), conjSp 2 F A (fieldSp 2 F σ (shortBlock F fin_two_zero_ne_one B)) =
      shortBlock F fin_two_zero_ne_one B) :
    σ = 1 ∧ ((((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F).IsDiag ∧
      conjSp 2 F A (longInv F 2 0) = longInv F 2 0) ∨
      conjSp 2 F A (longInv F 2 0) = longInv F 2 1) := by
  obtain ⟨hσ, hcase⟩ := conj_longInv_of_centralizes_shortBlock h2 A σ hfix
  refine ⟨hσ, ?_⟩
  subst hσ
  rcases hcase with h | h
  · refine Or.inl ⟨?_, h⟩
    have h1 : ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) * E01 F =
        E01 F * ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) := by
      have h := mat_comm_of_conj_fix A _ (hfix (sl2Upper 1))
      rw [mat_shortBlock_upper] at h
      simp only [one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
      exact add_left_cancel h
    have h2' : ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) * E10 F =
        E10 F * ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) := by
      have h := mat_comm_of_conj_fix A _ (hfix (sl2Lower 1))
      rw [mat_shortBlock_lower] at h
      simp only [one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
      exact add_left_cancel h
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ := shape_of_comm h1 h2'
    have hD := mat_comm_of_conj_fix' A _ h
    rw [mat_longInv] at hD
    have e1 := congrFun (congrFun hD (Sum.inl 0)) (Sum.inr 1)
    have e2 := congrFun (congrFun hD (Sum.inr 1)) (Sum.inl 0)
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e1 e2
    simp [mem_coords] at e1 e2
    have t1 : ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) (Sum.inl 0) (Sum.inr 1) = 0 := by
      have : (2 : F) * ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) (Sum.inl 0) (Sum.inr 1) = 0 := by
        linear_combination e1
      exact (mul_eq_zero.mp this).resolve_left h2
    have t2 : ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) (Sum.inr 1) (Sum.inl 0) = 0 := by
      have : (2 : F) * ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) (Sum.inr 1) (Sum.inl 0) = 0 := by
        linear_combination -e2
      exact (mul_eq_zero.mp this).resolve_left h2
    exact isDiag_of_entries s1 s2 t1 s3 (by rw [s11, t1, neg_zero]) s4 s5
      (by rw [s12, t2, neg_zero]) s6 t2 s7 s8
  · exact Or.inr h

theorem isDiag_mul_comm {a b : Mat4 F} (ha : a.IsDiag) (hb : b.IsDiag) : a * b = b * a := by
  rw [← (Matrix.isDiag_iff_diagonal_diag a).mp ha, ← (Matrix.isDiag_iff_diagonal_diag b).mp hb,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem mul_comm_of_isDiag {A B : gsp 2 F} (hA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F).IsDiag)
    (hB : ((B : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F).IsDiag) : A * B = B * A := by
  apply Subtype.ext
  apply Units.ext
  exact isDiag_mul_comm hA hB

theorem conjSp_commutator_of_isDiag {A B : gsp 2 F}
    (hA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F).IsDiag)
    (hB : ((B : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F).IsDiag) (x : StatedSp 2 F) :
    conjSp 2 F A (conjSp 2 F B (conjSp 2 F A⁻¹ (conjSp 2 F B⁻¹ x))) = x := by
  have h : A * B * A⁻¹ * B⁻¹ = 1 := by
    rw [mul_comm_of_isDiag hA hB]
    group
  have := congrArg (fun C => conjSp 2 F C x) h
  simpa [map_mul, MulAut.mul_apply] using this

end CFSG.ClassicalInvolution.RouteD.NodeModel
