module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

section Gens

variable {F : Type} [Field F]

@[expose] def s4Da : SL(3, F) := ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

@[expose] def s4Db : SL(3, F) := ⟨!![-1, 0, 0; 0, 1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

@[expose] def s4P : SL(3, F) := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

@[expose] def s4S : SL(3, F) := ⟨!![0, -1, 0; -1, 0, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

theorem coe_s4Da : ((s4Da : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, -1, 0; 0, 0, -1] := rfl
theorem coe_s4Db : ((s4Db : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := rfl
theorem coe_s4P : ((s4P : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl
theorem coe_s4S : ((s4S : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![0, -1, 0; -1, 0, 0; 0, 0, -1] := rfl

theorem s4Da_mul_self : (s4Da : SL(3, F)) * s4Da = 1 :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_s4Da, Matrix.mul_apply, Fin.sum_univ_three]

theorem s4Db_mul_self : (s4Db : SL(3, F)) * s4Db = 1 :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_s4Db, Matrix.mul_apply, Fin.sum_univ_three]

theorem s4S_mul_self : (s4S : SL(3, F)) * s4S = 1 :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_s4S, Matrix.mul_apply, Fin.sum_univ_three]

theorem s4P_pow_three : (s4P : SL(3, F)) * s4P * s4P = 1 :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_s4P, Matrix.mul_apply, Fin.sum_univ_three]


theorem s4Da_inv : (s4Da : SL(3, F))⁻¹ = s4Da := inv_eq_of_mul_eq_one_right s4Da_mul_self
theorem s4Db_inv : (s4Db : SL(3, F))⁻¹ = s4Db := inv_eq_of_mul_eq_one_right s4Db_mul_self
theorem s4S_inv : (s4S : SL(3, F))⁻¹ = s4S := inv_eq_of_mul_eq_one_right s4S_mul_self
theorem s4P_inv : (s4P : SL(3, F))⁻¹ = s4P * s4P :=
  inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact s4P_pow_three)

theorem comm_s4S_s4P : ⁅(s4S : SL(3, F)), (s4P : SL(3, F))⁆ = s4P :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [commutatorElement_def, s4S_inv, s4P_inv]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, coe_s4S, coe_s4P, Matrix.mul_apply, Fin.sum_univ_three]

theorem comm_s4P_s4Db : ⁅(s4P : SL(3, F)), (s4Db : SL(3, F))⁆ = s4Da :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [commutatorElement_def, s4Db_inv, s4P_inv]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, coe_s4Da, coe_s4Db, coe_s4P, Matrix.mul_apply, Fin.sum_univ_three]

theorem comm_s4P_sDc : ⁅(s4P : SL(3, F)), (s4Da : SL(3, F)) * s4Db⁆ = s4Db :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [commutatorElement_def, _root_.mul_inv_rev, s4Db_inv, s4Da_inv, s4P_inv]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, coe_s4Da, coe_s4Db, coe_s4P, Matrix.mul_apply, Fin.sum_univ_three]

theorem s4Da_inv_transpose : ((s4Da : SL(3, F))⁻¹).transpose = s4Da :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [s4Da_inv]
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_transpose, coe_s4Da]

theorem s4Db_inv_transpose : ((s4Db : SL(3, F))⁻¹).transpose = s4Db :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [s4Db_inv]
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_transpose, coe_s4Db]

theorem s4S_inv_transpose : ((s4S : SL(3, F))⁻¹).transpose = s4S :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [s4S_inv]
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_transpose, coe_s4S]

theorem s4P_inv_transpose : ((s4P : SL(3, F))⁻¹).transpose = s4P :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [s4P_inv]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_mul, coe_s4P]

theorem map_s4Da (σ : F ≃+* F) : SpecialLinearGroup.map σ.toRingHom (s4Da : SL(3, F)) = s4Da :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe, coe_s4Da]

theorem map_s4Db (σ : F ≃+* F) : SpecialLinearGroup.map σ.toRingHom (s4Db : SL(3, F)) = s4Db :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe, coe_s4Db]

theorem map_s4P (σ : F ≃+* F) : SpecialLinearGroup.map σ.toRingHom (s4P : SL(3, F)) = s4P :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe, coe_s4P]

theorem map_s4S (σ : F ≃+* F) : SpecialLinearGroup.map σ.toRingHom (s4S : SL(3, F)) = s4S :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe, coe_s4S]

end Gens


section Commutant

variable {F : Type} [Field F]

theorem s4_eq_zero_of_neg_eq_self (h2 : (2 : F) ≠ 0) {x : F} (h : -x = x) : x = 0 := by
  have : (2 : F) * x = 0 := by linear_combination (-1 : F) * h
  exact (mul_eq_zero.1 this).resolve_left h2

theorem s4_eq_scalar_of_commute_gens (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 3) (Fin 3) F}
    (ha : M * ((s4Da : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = ((s4Da : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M)
    (hb : M * ((s4Db : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = ((s4Db : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M)
    (hp : M * ((s4P : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = ((s4P : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M) :
    ∃ c : F, M = Matrix.scalar (Fin 3) c := by
  have h01 := congrFun (congrFun ha 0) 1
  have h02 := congrFun (congrFun ha 0) 2
  have h10 := congrFun (congrFun ha 1) 0
  have h20 := congrFun (congrFun ha 2) 0
  have h12 := congrFun (congrFun hb 1) 2
  have h21 := congrFun (congrFun hb 2) 1
  have p02 := congrFun (congrFun hp 0) 2
  have p10 := congrFun (congrFun hp 1) 0
  have p21 := congrFun (congrFun hp 2) 1
  simp [coe_s4Da, coe_s4Db, coe_s4P, Matrix.mul_apply, Fin.sum_univ_three] at h01 h02 h10 h20 h12 h21 p02 p10 p21
  have e01 := s4_eq_zero_of_neg_eq_self h2 h01
  have e02 := s4_eq_zero_of_neg_eq_self h2 h02
  have e10 := s4_eq_zero_of_neg_eq_self h2 h10.symm
  have e20 := s4_eq_zero_of_neg_eq_self h2 h20.symm
  have e12 := s4_eq_zero_of_neg_eq_self h2 h12
  have e21 := s4_eq_zero_of_neg_eq_self h2 h21.symm
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e01, e02, e10, e20, e12, e21, p02.symm, p10]

end Commutant


section S4

variable {F : Type} [Field F]

@[expose] def s4imgGens (F : Type) [Field F] : Set (projectiveSL 3 F) :=
  {proj 3 F s4Da, proj 3 F s4Db, proj 3 F s4P, proj 3 F s4S}

@[expose] def S4img (F : Type) [Field F] : Subgroup (projectiveSL 3 F) :=
  Subgroup.closure (s4imgGens F)

theorem proj_s4Da_mem : proj 3 F s4Da ∈ S4img F := Subgroup.subset_closure (by simp [s4imgGens])
theorem proj_s4Db_mem : proj 3 F s4Db ∈ S4img F := Subgroup.subset_closure (by simp [s4imgGens])
theorem proj_s4P_mem : proj 3 F s4P ∈ S4img F := Subgroup.subset_closure (by simp [s4imgGens])
theorem proj_s4S_mem : proj 3 F s4S ∈ S4img F := Subgroup.subset_closure (by simp [s4imgGens])

theorem s4img_fixed (α : MulAut (projectiveSL 3 F)) (h : ∀ g ∈ s4imgGens F, α g = g) :
    ∀ s ∈ S4img F, α s = s := by
  intro s hs
  induction hs using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => exact map_one α
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  | inv x _ hx => rw [map_inv, hx]

theorem fieldAut_proj_of {σ : F ≃+* F} {g : SL(3, F)} (h : SpecialLinearGroup.map σ.toRingHom g = g) :
    fieldAut 3 F σ (proj 3 F g) = proj 3 F g := by rw [fieldAut_proj, h]

theorem dualAut_proj_of {g : SL(3, F)} (h : (g⁻¹).transpose = g) :
    dualAut 3 F (proj 3 F g) = proj 3 F g := by rw [dualAut_proj, h]

theorem s4img_fixed_gf [Finite F] (_hF9 : Nat.card F = 9) (σ : F ≃+* F) (_hσ : ∀ x, σ x = x ^ 3) :
    ∀ s ∈ S4img F, (fieldAut 3 F σ * dualAut 3 F) s = s := by
  apply s4img_fixed
  rintro g (rfl | rfl | rfl | rfl)
  · rw [MulAut.mul_apply, dualAut_proj_of s4Da_inv_transpose, fieldAut_proj_of (map_s4Da σ)]
  · rw [MulAut.mul_apply, dualAut_proj_of s4Db_inv_transpose, fieldAut_proj_of (map_s4Db σ)]
  · rw [MulAut.mul_apply, dualAut_proj_of s4P_inv_transpose, fieldAut_proj_of (map_s4P σ)]
  · rw [MulAut.mul_apply, dualAut_proj_of s4S_inv_transpose, fieldAut_proj_of (map_s4S σ)]

end S4


section Nine

variable {F : Type} [Field F] [Finite F]

theorem two_ne_zero_of_card_nine (hF : Nat.card F = 9) : (2 : F) ≠ 0 := by
  have : Fintype F := Fintype.ofFinite F
  have hchar : CharP F 3 :=
    charP_of_card_eq_prime_pow (p := 3) (f := 2) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F 3] at h'
  omega

theorem pow_nine_eq_self (hF : Nat.card F = 9) (x : F) : x ^ 9 = x := by
  have : Fintype F := Fintype.ofFinite F
  rw [← hF, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem eq_one_of_pow_three_eq_one_nine (hF : Nat.card F = 9) {c : F} (h : c ^ 3 = 1) : c = 1 :=
  calc c = c ^ 9 := (pow_nine_eq_self hF c).symm
    _ = (c ^ 3) ^ 3 := by ring
    _ = 1 := by rw [h]; norm_num

theorem scalars_eq_bot_of_card_nine (hF : Nat.card F = 9) : scalars 3 F = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc3, hgc⟩ := mem_scalars.1 hg
  have h3 : (c : F) ^ 3 = 1 := by simpa using congrArg Units.val hc3
  have hc1 := eq_one_of_pow_three_eq_one_nine hF h3
  rw [Subgroup.mem_bot]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [hgc, hc1]
  simp

theorem proj_injective_of_card_nine (hF : Nat.card F = 9) : Function.Injective (proj 3 F) :=
  (MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_proj, scalars_eq_bot_of_card_nine hF])

theorem s4_eq_one_of_commute_gens (hF : Nat.card F = 9) {g : SL(3, F)} (ha : g * s4Da = s4Da * g)
    (hb : g * s4Db = s4Db * g) (hp : g * s4P = s4P * g) : g = 1 := by
  have h2 := two_ne_zero_of_card_nine hF
  obtain ⟨c, hc⟩ := s4_eq_scalar_of_commute_gens h2 (M := (g : Matrix (Fin 3) (Fin 3) F))
    (by rw [← Matrix.SpecialLinearGroup.coe_mul, ha, Matrix.SpecialLinearGroup.coe_mul])
    (by rw [← Matrix.SpecialLinearGroup.coe_mul, hb, Matrix.SpecialLinearGroup.coe_mul])
    (by rw [← Matrix.SpecialLinearGroup.coe_mul, hp, Matrix.SpecialLinearGroup.coe_mul])
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := g.2
  rw [hc, Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have hc1 := eq_one_of_pow_three_eq_one_nine hF hdet
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [hc, hc1]
  simp

theorem s4_eq_one_of_commute_proj_gens (hF : Nat.card F = 9) {y : projectiveSL 3 F}
    (ha : y * proj 3 F s4Da = proj 3 F s4Da * y) (hb : y * proj 3 F s4Db = proj 3 F s4Db * y)
    (hp : y * proj 3 F s4P = proj 3 F s4P * y) : y = 1 := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 F y
  have inj := proj_injective_of_card_nine hF
  have ha' : g * s4Da = s4Da * g := inj (by rw [map_mul, map_mul]; exact ha)
  have hb' : g * s4Db = s4Db * g := inj (by rw [map_mul, map_mul]; exact hb)
  have hp' : g * s4P = s4P * g := inj (by rw [map_mul, map_mul]; exact hp)
  rw [s4_eq_one_of_commute_gens hF ha' hb' hp', map_one]

end Nine

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
