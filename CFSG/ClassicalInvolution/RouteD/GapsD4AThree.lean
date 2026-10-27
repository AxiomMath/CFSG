module

public import CFSG.ClassicalInvolution.RouteD.GapsD4A

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.WeakCT CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply det_blockMat blockMat_mul blockMat_one
  blockMat_comm)
open scoped MatrixGroups Matrix

variable {F : Type} [Field F]

theorem exists_block_diagonalizer_three (h2 : (2 : F) ≠ 0) (G : Matrix (Fin 4) (Fin 4) F)
    (z02 : G 0 2 = 0) (z03 : G 0 3 = 0) (z12 : G 1 2 = 0) (z13 : G 1 3 = 0)
    (z20 : G 2 0 = 0) (z21 : G 2 1 = 0) (z30 : G 3 0 = 0) (z31 : G 3 1 = 0)
    (z23 : G 2 3 = 0) (z32 : G 3 2 = 0) (h33 : G 3 3 = G 2 2) (hlam : G 2 2 ≠ 0) (c : F)
    (hGG : G * G = c • (1 : Matrix (Fin 4) (Fin 4) F))
    (hscal : G 0 1 = 0 → G 1 0 = 0 → G 0 0 = G 1 1 → False) :
    ∃ P : Matrix (Fin 2) (Fin 2) F, P.det ≠ 0 ∧
      G * blockMat 4 0 P = blockMat 4 0 P * Matrix.diagonal ![-G 2 2, G 2 2, G 2 2, G 2 2] := by
  have hc22 : c = G 2 2 * G 2 2 := by
    have := congrFun (congrFun hGG 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_four, z20, z21, z23] at this
    exact this.symm
  set lam : F := G 2 2 with hlamdef
  set U : Matrix (Fin 2) (Fin 2) F := !![G 0 0, G 0 1; G 1 0, G 1 1] with hUdef
  have hU : U * U = (lam * lam) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j
    · have := congrFun (congrFun hGG 0) 0
      simp [Matrix.mul_apply, Fin.sum_univ_four, z02, z03, z20, z30] at this
      simp [hUdef, Matrix.mul_apply, Fin.sum_univ_two, ← hc22]
      linear_combination this
    · have := congrFun (congrFun hGG 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_four, z21, z31] at this
      simp [hUdef, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination this
    · have := congrFun (congrFun hGG 1) 0
      simp [Matrix.mul_apply, Fin.sum_univ_four, z12, z13, z20, z30] at this
      simp [hUdef, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination this
    · have := congrFun (congrFun hGG 1) 1
      simp [Matrix.mul_apply, Fin.sum_univ_four, z12, z13, z21, z31] at this
      simp [hUdef, Matrix.mul_apply, Fin.sum_univ_two, ← hc22]
      linear_combination this
  have hne1 : U ≠ lam • 1 := by
    intro h
    refine hscal ?_ ?_ ?_
    · simpa [hUdef] using congrFun (congrFun h 0) 1
    · simpa [hUdef] using congrFun (congrFun h 1) 0
    · have a1 := congrFun (congrFun h 0) 0
      have a2 := congrFun (congrFun h 1) 1
      simp [hUdef] at a1 a2
      rw [a1, a2]
  have hne2 : U ≠ (-lam) • 1 := by
    intro h
    refine hscal ?_ ?_ ?_
    · simpa [hUdef] using congrFun (congrFun h 0) 1
    · simpa [hUdef] using congrFun (congrFun h 1) 0
    · have a1 := congrFun (congrFun h 0) 0
      have a2 := congrFun (congrFun h 1) 1
      simp [hUdef] at a1 a2
      rw [a1, a2]
  obtain ⟨P, hPdet, hUP⟩ := exists_diagonalizer_two h2 lam hlam U hU hne1 hne2
  have e00 : G 0 0 * P 0 0 + G 0 1 * P 1 0 = P 0 0 * -lam := by
    simpa [hUdef, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] using
      congrFun (congrFun hUP 0) 0
  have e01 : G 0 0 * P 0 1 + G 0 1 * P 1 1 = P 0 1 * lam := by
    simpa [hUdef, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] using
      congrFun (congrFun hUP 0) 1
  have e10 : G 1 0 * P 0 0 + G 1 1 * P 1 0 = P 1 0 * -lam := by
    simpa [hUdef, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] using
      congrFun (congrFun hUP 1) 0
  have e11 : G 1 0 * P 0 1 + G 1 1 * P 1 1 = P 1 1 * lam := by
    simpa [hUdef, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] using
      congrFun (congrFun hUP 1) 1
  have hid := block_conj_identity G lam P z02 z03 z12 z13 z20 z21 z30 z31 z23 z32 rfl h33 e00 e01
    e10 e11
  exact ⟨P, hPdet, hid⟩

@[expose] noncomputable def blockGL (P : Matrix (Fin 2) (Fin 2) F) (hP : P.det ≠ 0) :
    GL (Fin (3 + 1)) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (blockMat (3 + 1) 0 P) (by
    rw [det_blockMat (by omega)]; exact hP)

theorem coe_blockGL (P : Matrix (Fin 2) (Fin 2) F) (hP : P.det ≠ 0) :
    ((blockGL P hP : GL (Fin (3 + 1)) F) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) =
      blockMat (3 + 1) 0 P := rfl

theorem conj_blockGL_zero (P : Matrix (Fin 2) (Fin 2) F) (hP : P.det ≠ 0) (A : SL(2, F)) :
    slConjugation (3 + 1) F (blockGL P hP) (blockSL2 F 3 ⟨0, by omega⟩ A) =
      blockSL2 F 3 ⟨0, by omega⟩
        (slConjugation 2 F (Matrix.GeneralLinearGroup.mkOfDetNeZero P hP) A) := by
  refine Subtype.ext ?_
  rw [slConjugation_matrix]
  show ((blockGL P hP : GL (Fin (3 + 1)) F) : Matrix (Fin 4) (Fin 4) F) *
      blockMat 4 0 (A : Matrix (Fin 2) (Fin 2) F) *
        (((blockGL P hP)⁻¹ : GL (Fin (3 + 1)) F) : Matrix (Fin 4) (Fin 4) F) =
    blockMat 4 0 ((slConjugation 2 F (Matrix.GeneralLinearGroup.mkOfDetNeZero P hP) A : SL(2, F)) :
      Matrix (Fin 2) (Fin 2) F)
  apply conj_eq_of_mul_eq
  rw [coe_blockGL, ← blockMat_mul (by omega), ← blockMat_mul (by omega)]
  congr 1
  have hinvP : (((Matrix.GeneralLinearGroup.mkOfDetNeZero P hP)⁻¹ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) * P = 1 :=
    Units.inv_mul (Matrix.GeneralLinearGroup.mkOfDetNeZero P hP)
  rw [slConjugation_matrix]
  calc P * (A : Matrix (Fin 2) (Fin 2) F)
      = P * (A : Matrix (Fin 2) (Fin 2) F) *
          ((((Matrix.GeneralLinearGroup.mkOfDetNeZero P hP)⁻¹ : GL (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) * P) := by rw [hinvP, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]; rfl

theorem conj_blockGL_two (P : Matrix (Fin 2) (Fin 2) F) (hP : P.det ≠ 0) (A : SL(2, F)) :
    slConjugation (3 + 1) F (blockGL P hP) (blockSL2 F 3 ⟨2, by omega⟩ A) =
      blockSL2 F 3 ⟨2, by omega⟩ A := by
  refine Subtype.ext ?_
  rw [slConjugation_matrix]
  apply conj_eq_of_mul_eq
  have hx : ((blockSL2 F 3 ⟨2, by omega⟩ A : SL(3 + 1, F)) :
      Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) = blockMat (3 + 1) 2 (A : Matrix (Fin 2) (Fin 2) F) :=
    rfl
  rw [coe_blockGL, hx]
  exact blockMat_comm (m := 3 + 1) (Or.inl (by omega)) P (A : Matrix (Fin 2) (Fin 2) F)

theorem map_range_conj_blockGL (P : Matrix (Fin 2) (Fin 2) F) (hP : P.det ≠ 0) :
    (blockSL2 F 3 ⟨0, by omega⟩).range.map (slConjugation (3 + 1) F (blockGL P hP)).toMonoidHom =
      (blockSL2 F 3 ⟨0, by omega⟩).range := by
  ext y
  simp only [Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨_, (conj_blockGL_zero P hP A).symm⟩
  · rintro ⟨A, rfl⟩
    refine ⟨_, ⟨(slConjugation 2 F (Matrix.GeneralLinearGroup.mkOfDetNeZero P hP)).symm A, rfl⟩, ?_⟩
    rw [conj_blockGL_zero, MulEquiv.apply_symm_apply]

theorem partner_chart_three [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    {X : Type} [Group X] (θ : SL(3 + 1, F) →* X)
    (hker : θ.ker ≤ Subgroup.center SL(3 + 1, F)) (σ : X ≃* X) (hσ : ∀ x, σ (σ x) = x)
    (g : GL (Fin (3 + 1)) F) (hg : ∀ x, σ (θ x) = θ (slConjugation (3 + 1) F g x))
    (hfix : ∀ A : SL(2, F), σ (θ (blockSL2 F 3 ⟨2, by omega⟩ A)) =
      θ (blockSL2 F 3 ⟨2, by omega⟩ A))
    (hmove : ∃ A : SL(2, F), σ (θ (blockSL2 F 3 ⟨0, by omega⟩ A)) ≠
      θ (blockSL2 F 3 ⟨0, by omega⟩ A)) :
    ∃ h : GL (Fin (3 + 1)) F,
      (blockSL2 F 3 ⟨0, by omega⟩).range.map (slConjugation (3 + 1) F h).toMonoidHom =
        (blockSL2 F 3 ⟨0, by omega⟩).range ∧
      (∀ A : SL(2, F), slConjugation (3 + 1) F h (blockSL2 F 3 ⟨2, by omega⟩ A) =
        blockSL2 F 3 ⟨2, by omega⟩ A) ∧
      ∀ x, σ (θ (slConjugation (3 + 1) F h x)) =
        θ (slConjugation (3 + 1) F h (slConjugation (3 + 1) F (partnerDiag 3 1) x)) := by
  have h4 : 4 ≤ Nat.card F := by omega
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  have hP2 : Group.IsPerfect SL(2, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  have hPn : Group.IsPerfect SL(3 + 1, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by omega)
  have hfixed : ∀ A : SL(2, F), slConjugation (3 + 1) F g (blockSL2 F 3 ⟨2, by omega⟩ A) =
      blockSL2 F 3 ⟨2, by omega⟩ A := by
    intro A
    have := hom_eq_of_central_ker θ hker (L := SL(2, F))
      ((slConjugation (3 + 1) F g).toMonoidHom.comp (blockSL2 F 3 ⟨2, by omega⟩))
      (blockSL2 F 3 ⟨2, by omega⟩)
      (fun A => by rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hg, hfix A])
    exact DFunLike.congr_fun this A
  obtain ⟨c1, c2⟩ := commute_of_fixes_block g ⟨2, by omega⟩ hfixed
  obtain ⟨e1, e2, e3, e4, e5⟩ := block_of_commute_single _ c1 c2
  have eC : (⟨2, by omega⟩ : Fin 3).castSucc = (2 : Fin (3 + 1)) := rfl
  have eS : (⟨2, by omega⟩ : Fin 3).succ = (3 : Fin (3 + 1)) := rfl
  simp only [eC, eS] at e1 e2 e3 e4 e5
  set G : Matrix (Fin 4) (Fin 4) F := (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) with hG
  have z02 : G 0 2 = 0 := e2 0 (by decide)
  have z12 : G 1 2 = 0 := e2 1 (by decide)
  have z32 : G 3 2 = 0 := e2 3 (by decide)
  have z03 : G 0 3 = 0 := e3 0 (by decide)
  have z13 : G 1 3 = 0 := e3 1 (by decide)
  have z23 : G 2 3 = 0 := e3 2 (by decide)
  have z20 : G 2 0 = 0 := e4 0 (by decide)
  have z21 : G 2 1 = 0 := e4 1 (by decide)
  have z30 : G 3 0 = 0 := e5 0 (by decide)
  have z31 : G 3 1 = 0 := e5 1 (by decide)
  have h33 : G 3 3 = G 2 2 := e1.symm
  have hlam : G 2 2 ≠ 0 := by
    intro h0
    apply det_ne_zero_of_gl g
    refine Matrix.det_eq_zero_of_row_eq_zero (2 : Fin 4) fun j => ?_
    by_cases hj : j = 2
    · rw [hj]; exact h0
    · exact e4 j hj
  have hsq : ∀ x, slConjugation (3 + 1) F g (slConjugation (3 + 1) F g x) = x := by
    have := hom_eq_of_central_ker θ hker (L := SL(3 + 1, F))
      ((slConjugation (3 + 1) F g).toMonoidHom.comp (slConjugation (3 + 1) F g).toMonoidHom)
      (MonoidHom.id _)
      (fun x => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
        rw [← hg, ← hg, hσ])
    intro x
    exact DFunLike.congr_fun this x
  have hgg : ∀ x, slConjugation (3 + 1) F (g * g) x = x := fun x => by
    rw [map_mul, MulAut.mul_apply]; exact hsq x
  obtain ⟨c, hc⟩ := exists_smul_one_of_commute_single ((g * g : GL (Fin (3 + 1)) F) :
    Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) (by omega)
    (fun i j hij => commute_single_of_conj_fixed (g * g) hij (hgg _))
  have hGG : G * G = c • (1 : Matrix (Fin 4) (Fin 4) F) := by
    rw [hG, ← Units.val_mul]; exact hc
  have hscal : G 0 1 = 0 → G 1 0 = 0 → G 0 0 = G 1 1 → False := by
    intro hb hc' hd
    have hoff : ∀ i j : Fin (3 + 1), i ≠ j → (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) i j = 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | assumption
    obtain ⟨u, hu⟩ := exists_diagGL_of_offdiag_zero g hoff
    have hu01 : u ⟨0, by omega⟩ = u ⟨1, by omega⟩ := by
      have h1 : (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) 0 0 = u ⟨0, by omega⟩ := by
        rw [hu, coe_diagGL]; simp
      have h2 : (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) 1 1 = u ⟨1, by omega⟩ := by
        rw [hu, coe_diagGL]; simp
      exact Units.ext (by rw [← h1, ← h2]; exact hd)
    obtain ⟨A, hA⟩ := hmove
    apply hA
    rw [hg, hu, slConjugation_diagGL_blockSL2 u ⟨0, by omega⟩ hu01 A]
  obtain ⟨P, hPdet, hid⟩ := exists_block_diagonalizer_three h2 G z02 z03 z12 z13 z20 z21 z30 z31
    z23 z32 h33 hlam c hGG hscal
  set lamU : Fˣ := Units.mk0 (G 2 2) hlam with hlamU
  have hD : g * blockGL P hPdet = blockGL P hPdet * diagGL (fun i => lamU * partnerEnt 3 1 i) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_diagGL, coe_blockGL]
    show G * blockMat 4 0 P = blockMat 4 0 P * _
    have hdiag : (![-G 2 2, G 2 2, G 2 2, G 2 2] : Fin 4 → F) =
        fun i => ((lamU * partnerEnt 3 1 i : Fˣ) : F) := by
      funext i
      fin_cases i <;> simp [partnerEnt, hlamU]
    rw [hid, hdiag]
  refine ⟨blockGL P hPdet, map_range_conj_blockGL P hPdet, conj_blockGL_two P hPdet, ?_⟩
  intro x
  rw [hg, ← MulAut.mul_apply, ← map_mul, hD, map_mul, MulAut.mul_apply]
  congr 2
  exact slConjugation_diagGL_congr (fun i => lamU * partnerEnt 3 1 i) (partnerEnt 3 1) lamU
    (fun i => rfl) x

end CFSG.ClassicalInvolution.RouteD.Gaps
