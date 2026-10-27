module

public import CFSG.ClassicalInvolution.Asc77.AscSCH12
public import CFSG.RankThree.CentralLift.DefiningSymplectic

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical CFSG.RankThree.CentralLift
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (leviSp coe_leviSp)

variable {F : Type} [Field F]

@[expose] def spE0 : F →+ symMatrices 2 F where
  toFun s := ⟨Matrix.single 0 0 s, by rw [mem_symMatrices, Matrix.transpose_single]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' s t := Subtype.ext (Matrix.single_add 0 0 s t)

@[expose] def spE1 : F →+ symMatrices 2 F where
  toFun s := ⟨Matrix.single 1 1 s, by rw [mem_symMatrices, Matrix.transpose_single]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' s t := Subtype.ext (Matrix.single_add 1 1 s t)

@[expose] def spE2 : F →+ symMatrices 2 F where
  toFun s := ⟨Matrix.single 0 1 s + Matrix.single 1 0 s, by
    rw [mem_symMatrices, Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single,
      add_comm]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' s t := Subtype.ext (by
    simp only [AddSubgroup.coe_add, Matrix.single_add]
    abel)

theorem coe_spE0 (s : F) : ((spE0 s : symMatrices 2 F) : Matrix (Fin 2) (Fin 2) F) =
    Matrix.single 0 0 s := rfl

theorem coe_spE1 (s : F) : ((spE1 s : symMatrices 2 F) : Matrix (Fin 2) (Fin 2) F) =
    Matrix.single 1 1 s := rfl

theorem coe_spE2 (s : F) : ((spE2 s : symMatrices 2 F) : Matrix (Fin 2) (Fin 2) F) =
    Matrix.single 0 1 s + Matrix.single 1 0 s := rfl

theorem symMatrices_two_decomp (v : symMatrices 2 F) :
    v = spE0 ((v : Matrix (Fin 2) (Fin 2) F) 0 0) + spE1 ((v : Matrix (Fin 2) (Fin 2) F) 1 1) +
      spE2 ((v : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have hv : ((v : Matrix (Fin 2) (Fin 2) F)) 1 0 = (v : Matrix (Fin 2) (Fin 2) F) 0 1 :=
    congrFun (congrFun v.2 0) 1
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_spE0, coe_spE1, coe_spE2, hv]

theorem torus_conj_siegelSp {r : ℕ} (a : Fin r → Fˣ) (v w : symMatrices r F)
    (hw : (w : Matrix (Fin r) (Fin r) F) = Matrix.diagonal (fun i => (a i : F)) * v *
      Matrix.diagonal (fun i => (a i : F))) :
    (⟨torusGL a, torusGL_mem_statedSp a⟩ : StatedSp r F) *
      siegelSpHom r F (Multiplicative.ofAdd v) *
      (⟨torusGL a, torusGL_mem_statedSp a⟩ : StatedSp r F)⁻¹ =
      siegelSpHom r F (Multiplicative.ofAdd w) := by
  apply Subtype.ext
  change torusGL a * siegelGL (v : Matrix (Fin r) (Fin r) F) * (torusGL a)⁻¹ =
    siegelGL (w : Matrix (Fin r) (Fin r) F)
  rw [torusGL_conj_siegelGL, hw]

theorem levi_conj_siegelSp {r : ℕ} (A : GL (Fin r) F) (v w : symMatrices r F)
    (hw : (w : Matrix (Fin r) (Fin r) F) = (A : Matrix (Fin r) (Fin r) F) * v *
      (A : Matrix (Fin r) (Fin r) F)ᵀ) :
    leviSp A * siegelSpHom r F (Multiplicative.ofAdd v) * (leviSp A)⁻¹ =
      siegelSpHom r F (Multiplicative.ofAdd w) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_leviSp_conj A (x := siegelSpHom r F (Multiplicative.ofAdd v)) (B := v) rfl, ← hw]
  rfl

@[expose] def spTorus (a : Fin 2 → Fˣ) : StatedSp 2 F := ⟨torusGL a, torusGL_mem_statedSp a⟩

theorem spTorus_spE0 (a : Fin 2 → Fˣ) (s : F) :
    spTorus a * siegelSpHom 2 F (Multiplicative.ofAdd (spE0 s)) * (spTorus a)⁻¹ =
      siegelSpHom 2 F (Multiplicative.ofAdd (spE0 ((a 0 : F) ^ 2 * s))) :=
  torus_conj_siegelSp a _ _ (by
    rw [coe_spE0, coe_spE0, diagonal_mul_single_mul_diagonal])

theorem spTorus_spE1 (a : Fin 2 → Fˣ) (s : F) :
    spTorus a * siegelSpHom 2 F (Multiplicative.ofAdd (spE1 s)) * (spTorus a)⁻¹ =
      siegelSpHom 2 F (Multiplicative.ofAdd (spE1 ((a 1 : F) ^ 2 * s))) :=
  torus_conj_siegelSp a _ _ (by
    rw [coe_spE1, coe_spE1, diagonal_mul_single_mul_diagonal])

theorem spTorus_spE2 (a : Fin 2 → Fˣ) (s : F) :
    spTorus a * siegelSpHom 2 F (Multiplicative.ofAdd (spE2 s)) * (spTorus a)⁻¹ =
      siegelSpHom 2 F (Multiplicative.ofAdd (spE2 ((a 0 : F) * (a 1 : F) * s))) :=
  torus_conj_siegelSp a _ _ (by
    have := diagonal_mul_offGen_mul_diagonal (fun x : F => x) (fun i => (a i : F)) 0 1 s rfl
    rw [coe_spE2, coe_spE2]
    exact this.symm)

section Pairing

variable {E : Type*} [Group E] {π : E →* StatedSp 2 F} (hπ : Function.Surjective π)
  (hZ : π.ker ≤ Subgroup.center E)

theorem liftPair_add3 {Y X V : Type*} [Group Y] [Group X] {φ : Y →* X}
    (hφ : Function.Surjective φ) [AddCommGroup V] (ρ : Multiplicative V →* X)
    (hZ : φ.ker ≤ Subgroup.center Y) (u₁ u₂ u₃ w₁ w₂ w₃ : V) :
    liftPair hφ ρ (u₁ + u₂ + u₃) (w₁ + w₂ + w₃) =
      (liftPair hφ ρ u₁ w₁ * liftPair hφ ρ u₁ w₂ * liftPair hφ ρ u₁ w₃) *
      (liftPair hφ ρ u₂ w₁ * liftPair hφ ρ u₂ w₂ * liftPair hφ ρ u₂ w₃) *
      (liftPair hφ ρ u₃ w₁ * liftPair hφ ρ u₃ w₂ * liftPair hφ ρ u₃ w₃) := by
  simp only [liftPair_add_left hφ ρ hZ, liftPair_add_right hφ ρ hZ]

theorem self_of_conj {Y X V : Type*} [Group Y] [Group X] {φ : Y →* X}
    (hφ : Function.Surjective φ) [AddCommGroup V] (ρ : Multiplicative V →* X)
    (hZ : φ.ker ≤ Subgroup.center Y) (eA eB eC : F →+ V) (g : X)
    (hg : ∀ y, g * ρ (Multiplicative.ofAdd (eB y)) * g⁻¹ =
      ρ (Multiplicative.ofAdd (eA y + eB y + eC y)))
    (hAB : ∀ s t, liftPair hφ ρ (eA s) (eB t) = 1) (hBA : ∀ s t, liftPair hφ ρ (eB s) (eA t) = 1)
    (hAC : ∀ s t, liftPair hφ ρ (eA s) (eC t) = 1) (hCA : ∀ s t, liftPair hφ ρ (eC s) (eA t) = 1)
    (hBC : ∀ s t, liftPair hφ ρ (eB s) (eC t) = 1) (hCB : ∀ s t, liftPair hφ ρ (eC s) (eB t) = 1)
    (hCC : ∀ s t, liftPair hφ ρ (eC s) (eC t) = 1) (y y' : F) :
    liftPair hφ ρ (eA y) (eA y') = 1 := by
  have h := liftPair_conj' hφ ρ hZ g (hg y) (hg y')
  rw [liftPair_add3 hφ ρ hZ] at h
  simp only [hAB, hBA, hAC, hCA, hBC, hCB, hCC, one_mul, mul_one] at h
  exact mul_eq_right.1 h

@[expose] def glU (x : F) : GL (Fin 2) F :=
  Matrix.SpecialLinearGroup.toGL ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def glL (x : F) : GL (Fin 2) F :=
  Matrix.SpecialLinearGroup.toGL ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_glU (x : F) : ((glU x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] :=
  rfl

theorem coe_glL (x : F) : ((glL x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; x, 1] :=
  rfl

theorem levi_glU_spE1 (y : F) :
    leviSp (glU (1 : F)) * siegelSpHom 2 F (Multiplicative.ofAdd (spE1 y)) *
      (leviSp (glU (1 : F)))⁻¹ =
      siegelSpHom 2 F (Multiplicative.ofAdd (spE0 y + spE1 y + spE2 y)) :=
  levi_conj_siegelSp _ _ _ (by
    simp only [AddSubgroup.coe_add, coe_spE0, coe_spE1, coe_spE2, coe_glU]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply,
        Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue] <;>
      simp)

theorem levi_glL_spE0 (y : F) :
    leviSp (glL (1 : F)) * siegelSpHom 2 F (Multiplicative.ofAdd (spE0 y)) *
      (leviSp (glL (1 : F)))⁻¹ =
      siegelSpHom 2 F (Multiplicative.ofAdd (spE1 y + spE0 y + spE2 y)) :=
  levi_conj_siegelSp _ _ _ (by
    simp only [AddSubgroup.coe_add, coe_spE0, coe_spE1, coe_spE2, coe_glL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply,
        Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue] <;>
      simp)

include hZ in
theorem siegelSp_liftPair_eq_one (hCp : IsPGroup 3 π.ker) (u : F) (hu0 : u ≠ 0)
    (hu2 : u ^ 2 ≠ 1) (v w : symMatrices 2 F) :
    liftPair hπ (siegelSpHom 2 F) v w = 1 := by
  have hu1 : u ≠ 1 := fun h => hu2 (by rw [h, one_pow])
  let ua : Fˣ := Units.mk0 u hu0
  have c01 : ∀ s t, liftPair hπ (siegelSpHom 2 F) (spE0 s) (spE1 t) = 1 := fun s t =>
    liftPair_eq_one_of_scale_right hπ (siegelSpHom 2 F) hZ spE0 spE1 (spTorus ![1, ua]) (u ^ 2) hu2
      (fun s => by rw [spTorus_spE0]; simp)
      (fun t => by rw [spTorus_spE1]; simp [ua]) s t
  have c10 : ∀ s t, liftPair hπ (siegelSpHom 2 F) (spE1 s) (spE0 t) = 1 := fun s t =>
    liftPair_eq_one_of_scale_left hπ (siegelSpHom 2 F) hZ spE1 spE0 (spTorus ![1, ua]) (u ^ 2) hu2
      (fun s => by rw [spTorus_spE1]; simp [ua])
      (fun t => by rw [spTorus_spE0]; simp) s t
  have c02 : ∀ s t, liftPair hπ (siegelSpHom 2 F) (spE0 s) (spE2 t) = 1 := fun s t =>
    liftPair_eq_one_of_scale_right hπ (siegelSpHom 2 F) hZ spE0 spE2 (spTorus ![1, ua]) u hu1
      (fun s => by rw [spTorus_spE0]; simp)
      (fun t => by rw [spTorus_spE2]; simp [ua]) s t
  have c20 : ∀ s t, liftPair hπ (siegelSpHom 2 F) (spE2 s) (spE0 t) = 1 := fun s t =>
    liftPair_eq_one_of_scale_left hπ (siegelSpHom 2 F) hZ spE2 spE0 (spTorus ![1, ua]) u hu1
      (fun s => by rw [spTorus_spE2]; simp [ua])
      (fun t => by rw [spTorus_spE0]; simp) s t
  have c12 : ∀ s t, liftPair hπ (siegelSpHom 2 F) (spE1 s) (spE2 t) = 1 := fun s t =>
    liftPair_eq_one_of_scale_right hπ (siegelSpHom 2 F) hZ spE1 spE2 (spTorus ![ua, 1]) u hu1
      (fun s => by rw [spTorus_spE1]; simp)
      (fun t => by rw [spTorus_spE2]; simp [ua]) s t
  have c21 : ∀ s t, liftPair hπ (siegelSpHom 2 F) (spE2 s) (spE1 t) = 1 := fun s t =>
    liftPair_eq_one_of_scale_left hπ (siegelSpHom 2 F) hZ spE2 spE1 (spTorus ![ua, 1]) u hu1
      (fun s => by rw [spTorus_spE2]; simp [ua])
      (fun t => by rw [spTorus_spE1]; simp) s t
  have s2 : ∀ s t, liftPair hπ (siegelSpHom 2 F) (spE2 s) (spE2 t) = 1 :=
    liftPair_self_eq_one_of_full hπ (siegelSpHom 2 F) hZ (p := 3) (by norm_num) hCp spE2
      (fun c hc => ⟨spTorus ![Units.mk0 c hc, 1], fun s => by rw [spTorus_spE2]; simp⟩)
  have s0 : ∀ s t, liftPair hπ (siegelSpHom 2 F) (spE0 s) (spE0 t) = 1 := fun s t =>
    self_of_conj hπ (siegelSpHom 2 F) hZ spE0 spE1 spE2 (leviSp (glU (1 : F))) levi_glU_spE1
      c01 c10 c02 c20 c12 c21 s2 s t
  have s1 : ∀ s t, liftPair hπ (siegelSpHom 2 F) (spE1 s) (spE1 t) = 1 := fun s t =>
    self_of_conj hπ (siegelSpHom 2 F) hZ spE1 spE0 spE2 (leviSp (glL (1 : F))) levi_glL_spE0
      c10 c01 c12 c21 c02 c20 s2 s t
  rw [symMatrices_two_decomp v, symMatrices_two_decomp w, liftPair_add3 hπ (siegelSpHom 2 F) hZ]
  simp only [c01, c10, c02, c20, c12, c21, s0, s1, s2, one_mul]

end Pairing

end CFSG.ClassicalInvolution.Asc77.SCH
