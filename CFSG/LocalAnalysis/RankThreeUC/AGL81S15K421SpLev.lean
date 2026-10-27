module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpPl

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpProof

open Matrix K421MonoProof K421OrbProof K421LinProof K421CGProof K421SpCWProof

section Lev

variable {F : Type} [Field F] [CharP F 2]

@[expose] def levMat (A B : Matrix (Fin 3) (Fin 3) F) : Matrix Idx Idx F :=
  Matrix.of fun i j => if i.2 = j.2 then (if i.2 = 0 then A i.1 j.1 else B i.1 j.1) else 0

theorem levMat_mul (A B A' B' : Matrix (Fin 3) (Fin 3) F) :
    levMat A B * levMat A' B' = levMat (A * A') (B * B') := by
  ext ⟨i, a⟩ ⟨k, c⟩
  simp only [levMat, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases a <;> fin_cases c <;> simp [Matrix.mul_apply]

theorem levMat_one : levMat (1 : Matrix (Fin 3) (Fin 3) F) 1 = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> simp [levMat, Matrix.one_apply]

theorem levMat_symp {A B : Matrix (Fin 3) (Fin 3) F} (hAB : Aᵀ * B = 1) (hBA : Bᵀ * A = 1) :
    (levMat A B)ᵀ * JF F * levMat A B = JF F := by
  ext ⟨i, a⟩ ⟨k, c⟩
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    levMat, JF, bc, JI, Jm, Matrix.of_apply, Matrix.map_apply]
  fin_cases a <;> fin_cases c
  all_goals simp
  · have h := congrFun (congrFun hAB i) k
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  · have h := congrFun (congrFun hBA i) k
    simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem levMat_comm_bd3 {A B : Matrix (Fin 3) (Fin 3) F} {a b c : Matrix (Fin 2) (Fin 2) F}
    (h : ∀ (i j : Fin 3) (s t : Fin 2),
      (if s = 0 then A i j else B i j) * (![a, b, c] j) s t =
        (![a, b, c] i) s t * (if t = 0 then A i j else B i j)) :
    levMat A B * bd3 a b c = bd3 a b c * levMat A B := by
  ext ⟨i, s⟩ ⟨j, t⟩
  have h' := h i j s t
  simp only [levMat, bd3, bd, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  fin_cases s <;> fin_cases t <;> simp_all

theorem levMat_mul_bd3_apply (A B : Matrix (Fin 3) (Fin 3) F) (a b c : Matrix (Fin 2) (Fin 2) F)
    (i j : Fin 3) (s t : Fin 2) :
    (levMat A B * bd3 a b c) (i, s) (j, t) =
      (if s = 0 then A i j else B i j) * (![a, b, c] j) s t := by
  simp only [levMat, bd3, bd, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  fin_cases s <;> simp

theorem levMat_inj_left {A B A' B' : Matrix (Fin 3) (Fin 3) F} (h : levMat A B = levMat A' B') :
    A = A' := by
  ext i j
  have := congrFun (congrFun h (i, 0)) (j, 0)
  simpa [levMat] using this

@[expose] def ext2 (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, 1]

theorem ext2_mul (M N : Matrix (Fin 2) (Fin 2) F) : ext2 M * ext2 N = ext2 (M * N) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ext2, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem ext2_one : ext2 (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ext2]

theorem ext2_transpose (M : Matrix (Fin 2) (Fin 2) F) : (ext2 M)ᵀ = ext2 Mᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ext2]

@[expose] def lev : Matrix.SpecialLinearGroup (Fin 2) F →* ↥(SpI F) :=
  spHom (fun M => levMat (ext2 (M : Matrix (Fin 2) (Fin 2) F))
      (ext2 (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ)))
    (fun M N => by
      simp only [levMat_mul, ext2_mul, Matrix.SpecialLinearGroup.coe_mul, _root_.mul_inv_rev,
        Matrix.transpose_mul])
    (by simp [ext2_one, levMat_one])
    (fun M => levMat_symp
      (by
        rw [ext2_transpose, ext2_mul, ← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul,
          inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, ext2_one])
      (by
        rw [ext2_transpose, Matrix.transpose_transpose, ext2_mul, ← Matrix.SpecialLinearGroup.coe_mul,
          inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, ext2_one]))

theorem lev_val (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    (((lev M : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F) =
      levMat (ext2 (M : Matrix (Fin 2) (Fin 2) F))
        (ext2 (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ)) := rfl

end Lev

section Split

variable {F : Type} [Field F] [CharP F 2] {ω : F}

@[expose] def Pm (ω : F) : Matrix (Fin 2) (Fin 2) F := !![1, 1; ω, ω ^ 2]

@[expose] def Dm (ω : F) : Matrix (Fin 2) (Fin 2) F := !![ω, 0; 0, ω ^ 2]

theorem det_Pm (hω : ω ^ 2 + ω + 1 = 0) : (Pm ω).det = 1 := by
  have h2 := two_eq_zero_F F
  simp only [Matrix.det_fin_two, Pm]
  simp
  linear_combination hω - (ω + 1) * h2

theorem det_Dm (hω : ω ^ 2 + ω + 1 = 0) : (Dm ω).det = 1 := by
  simp only [Matrix.det_fin_two, Dm]
  simp
  linear_combination (ω - 1) * hω

theorem CP_eq (hω : ω ^ 2 + ω + 1 = 0) : tm F 0 1 * Pm ω = Pm ω * Dm ω := by
  have h2 := two_eq_zero_F F
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, Pm, Dm, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -hω + (ω + 1) * h2
  · linear_combination (1 - ω ^ 2 + ω) * hω - ω * h2

@[expose] def PS (hω : ω ^ 2 + ω + 1 = 0) : Matrix.SpecialLinearGroup (Fin 2) F := ⟨Pm ω, det_Pm hω⟩

@[expose] def DS (hω : ω ^ 2 + ω + 1 = 0) : Matrix.SpecialLinearGroup (Fin 2) F := ⟨Dm ω, det_Dm hω⟩

@[expose] def gP (hω : ω ^ 2 + ω + 1 = 0) : ↥(SpI F) :=
  placeHom (G := Matrix.SpecialLinearGroup (Fin 2) F) (MonoidHom.id _) (MonoidHom.id _) 1 (PS hω)

@[expose] def y2 (hω : ω ^ 2 + ω + 1 = 0) : ↥(SpI F) :=
  placeHom (G := Matrix.SpecialLinearGroup (Fin 2) F) (MonoidHom.id _) (MonoidHom.id _) 1 (DS hω)

theorem gP_val (hω : ω ^ 2 + ω + 1 = 0) :
    ((gP hω : ↥(SpI F)) : GL Idx F).val = bd3 (Pm ω) (Pm ω) 1 := rfl

theorem y2_val (hω : ω ^ 2 + ω + 1 = 0) :
    ((y2 hω : ↥(SpI F)) : GL Idx F).val = bd3 (Dm ω) (Dm ω) 1 := rfl

theorem conj_y2 (hω : ω ^ 2 + ω + 1 = 0) :
    (gP hω)⁻¹ * (monoSp F).av (rep 1) * ((gP hω)⁻¹)⁻¹ = y2 hω := by
  rw [inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul]
  apply Subtype.ext
  apply Units.ext
  show ((((monoSp F).av (rep 1) : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F) *
      ((gP hω : ↥(SpI F)) : GL Idx F).val = ((gP hω : ↥(SpI F)) : GL Idx F).val *
        ((y2 hω : ↥(SpI F)) : GL Idx F).val
  rw [av_rep1, gP_val, y2_val, bd3_mul, bd3_mul, CP_eq hω]

theorem lev_commute_y2 (hω : ω ^ 2 + ω + 1 = 0) (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    lev M * y2 hω = y2 hω * lev M := by
  apply Subtype.ext
  apply Units.ext
  show ((lev M : ↥(SpI F)) : GL Idx F).val * ((y2 hω : ↥(SpI F)) : GL Idx F).val =
    ((y2 hω : ↥(SpI F)) : GL Idx F).val * ((lev M : ↥(SpI F)) : GL Idx F).val
  rw [lev_val, y2_val]
  apply levMat_comm_bd3
  intro i j s t
  fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;> simp [ext2, Dm] <;> ring

theorem lev_commute_plane (M g : Matrix.SpecialLinearGroup (Fin 2) F) :
    lev M * placeHom (F := F) 1 1 (MonoidHom.id _) g =
      placeHom (F := F) 1 1 (MonoidHom.id _) g * lev M := by
  apply Subtype.ext
  apply Units.ext
  show ((lev M : ↥(SpI F)) : GL Idx F).val *
      ((placeHom (F := F) 1 1 (MonoidHom.id _) g : ↥(SpI F)) : GL Idx F).val =
    ((placeHom (F := F) 1 1 (MonoidHom.id _) g : ↥(SpI F)) : GL Idx F).val *
      ((lev M : ↥(SpI F)) : GL Idx F).val
  rw [lev_val, placeHom_val]
  apply levMat_comm_bd3
  intro i j s t
  fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;> simp [ext2] <;> ring

@[expose] def levPlane : (Matrix.SpecialLinearGroup (Fin 2) F ×
    Matrix.SpecialLinearGroup (Fin 2) F) →* ↥(SpI F) :=
  MonoidHom.noncommCoprod lev (placeHom (F := F) 1 1 (MonoidHom.id _))
    (fun M g => lev_commute_plane M g)

theorem levPlane_apply (M g : Matrix.SpecialLinearGroup (Fin 2) F) :
    levPlane (M, g) = lev M * placeHom (F := F) 1 1 (MonoidHom.id _) g := rfl

theorem levPlane_injective : Function.Injective (levPlane (F := F)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨M, g⟩ h
  have h' : lev M * placeHom (F := F) 1 1 (MonoidHom.id _) g = 1 := by
    rw [← levPlane_apply]
    exact h
  have hmat : ((lev M : ↥(SpI F)) : GL Idx F).val *
      ((placeHom (F := F) 1 1 (MonoidHom.id _) g : ↥(SpI F)) : GL Idx F).val = 1 :=
    congrArg (fun y : ↥(SpI F) => ((y : GL Idx F) : Matrix Idx Idx F)) h'
  rw [lev_val, placeHom_val] at hmat
  have hg : g = 1 := by
    apply Subtype.ext
    ext s t
    have := congrFun (congrFun hmat (2, s)) (2, t)
    rw [levMat_mul_bd3_apply] at this
    fin_cases s <;> fin_cases t <;> simpa [ext2, Matrix.one_apply] using this
  have hM : M = 1 := by
    apply Subtype.ext
    ext i j
    have := congrFun (congrFun hmat (i.castSucc, 0)) (j.castSucc, 0)
    rw [levMat_mul_bd3_apply] at this
    fin_cases i <;> fin_cases j <;> simpa [ext2, Matrix.one_apply] using this
  exact Prod.ext hM hg

theorem rankTwoAt_y2 [Finite F] {p : ℕ} (hω : ω ^ 2 + ω + 1 = 0)
    (hp : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F)) : RankTwoAt p (y2 hω) := by
  refine ⟨Matrix.SpecialLinearGroup (Fin 2) F, Matrix.SpecialLinearGroup (Fin 2) F, inferInstance,
    inferInstance, inferInstance, inferInstance, levPlane, levPlane_injective, ?_, hp, hp⟩
  rintro _ ⟨⟨M, g⟩, rfl⟩
  have h1 : lev M ∈ Subgroup.centralizer ({y2 hω} : Set ↥(SpI F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (lev_commute_y2 hω M).symm
  have h2 : placeHom (F := F) 1 1 (MonoidHom.id _) g ∈
      Subgroup.centralizer ({y2 hω} : Set ↥(SpI F)) :=
    mem_centralizer_of_bd3 (y2_val hω) (placeHom_val _ _ _ g) (by simp) (by simp) (by simp)
  rw [levPlane_apply]
  exact Subgroup.mul_mem _ h1 h2

theorem rankTwoAt_rep1_split [Finite F] {p : ℕ} (hω : ω ^ 2 + ω + 1 = 0)
    (hp : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F)) :
    RankTwoAt p ((monoSp F).av (rep 1)) :=
  RankTwoAt.conj (conj_y2 hω) (rankTwoAt_y2 hω hp)

end Split

end K421SpProof

end CFSG.LocalAnalysis.RankThreeUC.S15
