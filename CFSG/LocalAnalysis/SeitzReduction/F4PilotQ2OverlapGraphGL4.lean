module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix

abbrev GL4M : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

abbrev GL4G : Type := GL (Fin 4) (ZMod 2)

@[expose] def gl4Mk (A B : GL4M) (h : A * B = 1) : GL4G :=
  ⟨A, B, h, mul_eq_one_comm.1 h⟩

@[simp] theorem coe_gl4Mk (A B : GL4M) (h : A * B = 1) : ((gl4Mk A B h : GL4G) : GL4M) = A :=
  rfl

@[expose] def gl4T0M : GL4M := !![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def gl4U0M : GL4M := !![1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def gl4T0 : GL4G := gl4Mk gl4T0M gl4T0M (by decide)

@[expose] def gl4U0 : GL4G := gl4Mk gl4U0M gl4U0M (by decide)

theorem gl4_eq_zero_of_mulVec_eq_zero (g : GL4G) {v : Fin 4 → ZMod 2}
    (h : (g : GL4M) *ᵥ v = 0) : v = 0 := by
  have h1 : ((g⁻¹ : GL4G) : GL4M) *ᵥ ((g : GL4M) *ᵥ v) = v := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  rw [← h1, h, mulVec_zero]

theorem gl4_t0_matrix_commute {g : GL4G} (hg : g ∈ Subgroup.centralizer {gl4T0}) :
    (g : GL4M) * gl4T0M = gl4T0M * (g : GL4M) := by
  have := congrArg (fun x : GL4G => (x : GL4M)) (Subgroup.mem_centralizer_singleton_iff.1 hg)
  simpa [gl4T0] using this

theorem gl4_t0_shape {g : GL4G} (hg : g ∈ Subgroup.centralizer {gl4T0}) :
    (g : GL4M) 1 0 = 0 ∧ (g : GL4M) 2 0 = 0 ∧ (g : GL4M) 3 0 = 0 ∧ (g : GL4M) 3 1 = 0 ∧
      (g : GL4M) 3 2 = 0 ∧ (g : GL4M) 0 0 = 1 ∧ (g : GL4M) 3 3 = 1 := by
  have hc := gl4_t0_matrix_commute hg
  have e : ∀ i j, ((g : GL4M) * gl4T0M) i j = (gl4T0M * (g : GL4M)) i j := fun i j => by
    rw [hc]
  have e13 := e 1 3
  have e23 := e 2 3
  have e33 := e 3 3
  have e01 := e 0 1
  have e02 := e 0 2
  have e03 := e 0 3
  simp [gl4T0M, Matrix.mul_apply, Fin.sum_univ_four] at e13 e23 e33 e01 e02 e03
  have h03 : (g : GL4M) 0 0 = (g : GL4M) 3 3 := by
    rw [add_comm ((g : GL4M) 0 0)] at e03
    exact add_left_cancel e03
  have h1 := e13
  have h2 := e23
  have h30 := e33
  have h31 := e01
  have h32 := e02
  have h00 : (g : GL4M) 0 0 = 1 := by
    have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    refine key _ fun h0 => ?_
    have hz : (g : GL4M) *ᵥ Pi.single 0 1 = 0 := by
      ext i
      fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four, h0, h1, h2, h30]
    exact (by decide : (Pi.single 0 1 : Fin 4 → ZMod 2) ≠ 0) (gl4_eq_zero_of_mulVec_eq_zero g hz)
  exact ⟨h1, h2, h30, h31, h32, h00, h03 ▸ h00⟩

@[expose] def gl4Mid (g : GL4M) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun a b => g a.succ.castSucc b.succ.castSucc

theorem gl4Mid_mul {g h : GL4M} (hg1 : g 1 0 = 0) (hg2 : g 2 0 = 0) (hh1 : h 3 1 = 0)
    (hh2 : h 3 2 = 0) : gl4Mid (g * h) = gl4Mid g * gl4Mid h := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gl4Mid, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, hg1, hg2, hh1, hh2]

theorem gl4Mid_one : gl4Mid 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem gl4Mid_mul_of_mem {g h : GL4G} (hg : g ∈ Subgroup.centralizer {gl4T0})
    (hh : h ∈ Subgroup.centralizer {gl4T0}) :
    gl4Mid ((g : GL4M) * (h : GL4M)) = gl4Mid (g : GL4M) * gl4Mid (h : GL4M) := by
  obtain ⟨g1, g2, -, -, -, -, -⟩ := gl4_t0_shape hg
  obtain ⟨-, -, -, h1, h2, -, -⟩ := gl4_t0_shape hh
  exact gl4Mid_mul g1 g2 h1 h2

@[expose] def gl4RhoT : Subgroup.centralizer {gl4T0} →* GL (Fin 2) (ZMod 2) where
  toFun g := ⟨gl4Mid (g : GL4G), gl4Mid ((g⁻¹ : Subgroup.centralizer {gl4T0}) : GL4G), by
    rw [← gl4Mid_mul_of_mem g.2 (g⁻¹).2, ← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel,
      Units.val_one, gl4Mid_one], by
    rw [← gl4Mid_mul_of_mem (g⁻¹).2 g.2, ← Units.val_mul, Subgroup.coe_inv, inv_mul_cancel,
      Units.val_one, gl4Mid_one]⟩
  map_one' := Units.ext (by simp [gl4Mid_one])
  map_mul' g h := Units.ext (by
    change gl4Mid ((g : GL4G) * (h : GL4G) : GL4G) = gl4Mid (g : GL4G) * gl4Mid (h : GL4G)
    rw [Units.val_mul, gl4Mid_mul_of_mem g.2 h.2])

@[expose] def gl4DT (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : GL4M :=
  !![1, 0, 0, 0; 0, M 0 0, M 0 1, 0; 0, M 1 0, M 1 1, 0; 0, 0, 0, 1]

theorem gl4DT_mul (M M' : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    gl4DT M * gl4DT M' = gl4DT (M * M') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl4DT, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem gl4DT_one : gl4DT 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem gl4DT_commute (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    gl4DT M * gl4T0M = gl4T0M * gl4DT M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl4DT, gl4T0M, Matrix.mul_apply, Fin.sum_univ_four]

theorem gl4RhoT_surjective : Function.Surjective gl4RhoT := by
  intro M
  have hM : gl4DT (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
      gl4DT ((M⁻¹ : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by
    rw [gl4DT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, gl4DT_one]
  refine ⟨⟨gl4Mk _ _ hM, ?_⟩, Units.ext ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    simp only [Units.val_mul, coe_gl4Mk, gl4T0]
    exact gl4DT_commute _
  · change gl4Mid (gl4DT (M : Matrix (Fin 2) (Fin 2) (ZMod 2))) = (M : Matrix _ _ _)
    ext a b
    fin_cases a <;> fin_cases b <;> rfl

@[expose] def gl4TM (c : Fin 5 → ZMod 2) : GL4M :=
  !![1, c 0, c 1, c 2; 0, 1, 0, c 3; 0, 0, 1, c 4; 0, 0, 0, 1]

@[expose] def gl4TInv (c : Fin 5 → ZMod 2) : Fin 5 → ZMod 2 :=
  ![c 0, c 1, c 2 + c 0 * c 3 + c 1 * c 4, c 3, c 4]

theorem gl4TM_facts : ∀ c : Fin 5 → ZMod 2, gl4TM c * gl4TM (gl4TInv c) = 1 := by
  decide +kernel

theorem gl4TM_commute (c : Fin 5 → ZMod 2) : gl4TM c * gl4T0M = gl4T0M * gl4TM c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl4TM, gl4T0M, Matrix.mul_apply, Fin.sum_univ_four, add_comm]

theorem gl4TM_mid (c : Fin 5 → ZMod 2) : gl4Mid (gl4TM c) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem gl4TM_injective : Function.Injective gl4TM := by
  intro c c' h
  funext k
  fin_cases k
  · exact congrFun (congrFun h 0) 1
  · exact congrFun (congrFun h 0) 2
  · exact congrFun (congrFun h 0) 3
  · exact congrFun (congrFun h 1) 3
  · exact congrFun (congrFun h 2) 3

@[expose] def gl4TElt (c : Fin 5 → ZMod 2) : gl4RhoT.ker :=
  ⟨⟨gl4Mk (gl4TM c) (gl4TM (gl4TInv c)) (gl4TM_facts c), by
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    simp only [Units.val_mul, coe_gl4Mk, gl4T0]
    exact gl4TM_commute c⟩, by
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    change gl4Mid (gl4TM c) = 1
    exact gl4TM_mid c⟩

theorem gl4TElt_surjective : Function.Surjective gl4TElt := by
  rintro ⟨⟨g, hg⟩, hker⟩
  have hmid : gl4Mid (g : GL4M) = 1 := by
    have := congrArg (fun x : GL (Fin 2) (ZMod 2) => (x : Matrix (Fin 2) (Fin 2) (ZMod 2)))
      (MonoidHom.mem_ker.1 hker)
    exact this
  have b11 : (g : GL4M) 1 1 = 1 := congrFun (congrFun hmid 0) 0
  have b12 : (g : GL4M) 1 2 = 0 := congrFun (congrFun hmid 0) 1
  have b21 : (g : GL4M) 2 1 = 0 := congrFun (congrFun hmid 1) 0
  have b22 : (g : GL4M) 2 2 = 1 := congrFun (congrFun hmid 1) 1
  obtain ⟨s10, s20, s30, s31, s32, s00, s33⟩ := gl4_t0_shape hg
  refine ⟨![(g : GL4M) 0 1, (g : GL4M) 0 2, (g : GL4M) 0 3, (g : GL4M) 1 3, (g : GL4M) 2 3], ?_⟩
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  change gl4TM _ = (g : GL4M)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl4TM, b11, b12, b21, b22, s10, s20, s30, s31, s32, s00, s33]

theorem gl4TElt_injective : Function.Injective gl4TElt := by
  intro c c' h
  apply gl4TM_injective
  have := congrArg (fun x : gl4RhoT.ker =>
    (((x : Subgroup.centralizer {gl4T0}) : GL4G) : GL4M)) h
  exact this

theorem gl4_card_ker_rhoT : Nat.card gl4RhoT.ker = 32 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨gl4TElt_injective, gl4TElt_surjective⟩),
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem gl4_card_centralizer_t0 : Nat.card (Subgroup.centralizer {gl4T0}) = 192 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup gl4RhoT.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ gl4RhoT_surjective).toEquiv,
    gl4_card_ker_rhoT, Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two] at h
  rw [h]
  norm_num

theorem gl4_u0_matrix_commute {g : GL4G} (hg : g ∈ Subgroup.centralizer {gl4U0}) :
    (g : GL4M) * gl4U0M = gl4U0M * (g : GL4M) := by
  have := congrArg (fun x : GL4G => (x : GL4M)) (Subgroup.mem_centralizer_singleton_iff.1 hg)
  simpa [gl4U0] using this

theorem gl4_u0_shape {g : GL4G} (hg : g ∈ Subgroup.centralizer {gl4U0}) :
    (g : GL4M) 2 0 = 0 ∧ (g : GL4M) 3 0 = 0 ∧ (g : GL4M) 2 1 = 0 ∧ (g : GL4M) 3 1 = 0 ∧
      (g : GL4M) 2 2 = (g : GL4M) 0 0 ∧ (g : GL4M) 2 3 = (g : GL4M) 0 1 ∧
      (g : GL4M) 3 2 = (g : GL4M) 1 0 ∧ (g : GL4M) 3 3 = (g : GL4M) 1 1 := by
  have hc := gl4_u0_matrix_commute hg
  have e : ∀ i j, ((g : GL4M) * gl4U0M) i j = (gl4U0M * (g : GL4M)) i j := fun i j => by
    rw [hc]
  have e22 := e 2 2
  have e32 := e 3 2
  have e23 := e 2 3
  have e33 := e 3 3
  have e02 := e 0 2
  have e03 := e 0 3
  have e12 := e 1 2
  have e13 := e 1 3
  simp [gl4U0M, Matrix.mul_apply, Fin.sum_univ_four] at e22 e32 e23 e33 e02 e03 e12 e13
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination e22
  · linear_combination e32
  · linear_combination e23
  · linear_combination e33
  · linear_combination -e02
  · linear_combination -e03
  · linear_combination -e12
  · linear_combination -e13

@[expose] def gl4Blk (g : GL4M) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun a b => g a.castSucc.castSucc b.castSucc.castSucc

theorem gl4Blk_mul (g : GL4M) {h : GL4M} (h20 : h 2 0 = 0) (h30 : h 3 0 = 0) (h21 : h 2 1 = 0)
    (h31 : h 3 1 = 0) : gl4Blk (g * h) = gl4Blk g * gl4Blk h := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gl4Blk, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, h20, h30, h21, h31]

theorem gl4Blk_one : gl4Blk 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem gl4Blk_mul_of_mem (g : GL4M) {h : GL4G} (hh : h ∈ Subgroup.centralizer {gl4U0}) :
    gl4Blk (g * (h : GL4M)) = gl4Blk g * gl4Blk (h : GL4M) := by
  obtain ⟨h20, h30, h21, h31, -⟩ := gl4_u0_shape hh
  exact gl4Blk_mul g h20 h30 h21 h31

@[expose] def gl4RhoU : Subgroup.centralizer {gl4U0} →* GL (Fin 2) (ZMod 2) where
  toFun g := ⟨gl4Blk (g : GL4G), gl4Blk ((g⁻¹ : Subgroup.centralizer {gl4U0}) : GL4G), by
    rw [← gl4Blk_mul_of_mem _ (g⁻¹).2, ← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel,
      Units.val_one, gl4Blk_one], by
    rw [← gl4Blk_mul_of_mem _ g.2, ← Units.val_mul, Subgroup.coe_inv, inv_mul_cancel,
      Units.val_one, gl4Blk_one]⟩
  map_one' := Units.ext (by simp [gl4Blk_one])
  map_mul' g h := Units.ext (by
    change gl4Blk ((g : GL4G) * (h : GL4G) : GL4G) = gl4Blk (g : GL4G) * gl4Blk (h : GL4G)
    rw [Units.val_mul, gl4Blk_mul_of_mem _ h.2])

@[expose] def gl4DU (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : GL4M :=
  !![M 0 0, M 0 1, 0, 0; M 1 0, M 1 1, 0, 0; 0, 0, M 0 0, M 0 1; 0, 0, M 1 0, M 1 1]

theorem gl4DU_mul (M M' : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    gl4DU M * gl4DU M' = gl4DU (M * M') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl4DU, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem gl4DU_one : gl4DU 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem gl4DU_commute (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    gl4DU M * gl4U0M = gl4U0M * gl4DU M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl4DU, gl4U0M, Matrix.mul_apply, Fin.sum_univ_four]

theorem gl4RhoU_surjective : Function.Surjective gl4RhoU := by
  intro M
  have hM : gl4DU (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
      gl4DU ((M⁻¹ : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by
    rw [gl4DU_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, gl4DU_one]
  refine ⟨⟨gl4Mk _ _ hM, ?_⟩, Units.ext ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    simp only [Units.val_mul, coe_gl4Mk, gl4U0]
    exact gl4DU_commute _
  · change gl4Blk (gl4DU (M : Matrix (Fin 2) (Fin 2) (ZMod 2))) = (M : Matrix _ _ _)
    ext a b
    fin_cases a <;> fin_cases b <;> rfl

@[expose] def gl4UM (c : Fin 4 → ZMod 2) : GL4M :=
  !![1, 0, c 0, c 1; 0, 1, c 2, c 3; 0, 0, 1, 0; 0, 0, 0, 1]

theorem gl4UM_facts : ∀ c : Fin 4 → ZMod 2, gl4UM c * gl4UM c = 1 := by
  decide +kernel

theorem gl4UM_commute (c : Fin 4 → ZMod 2) : gl4UM c * gl4U0M = gl4U0M * gl4UM c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl4UM, gl4U0M, Matrix.mul_apply, Fin.sum_univ_four, add_comm]

theorem gl4UM_blk (c : Fin 4 → ZMod 2) : gl4Blk (gl4UM c) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem gl4UM_injective : Function.Injective gl4UM := by
  intro c c' h
  funext k
  fin_cases k
  · exact congrFun (congrFun h 0) 2
  · exact congrFun (congrFun h 0) 3
  · exact congrFun (congrFun h 1) 2
  · exact congrFun (congrFun h 1) 3

@[expose] def gl4UElt (c : Fin 4 → ZMod 2) : gl4RhoU.ker :=
  ⟨⟨gl4Mk (gl4UM c) (gl4UM c) (gl4UM_facts c), by
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    simp only [Units.val_mul, coe_gl4Mk, gl4U0]
    exact gl4UM_commute c⟩, by
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    change gl4Blk (gl4UM c) = 1
    exact gl4UM_blk c⟩

theorem gl4UElt_surjective : Function.Surjective gl4UElt := by
  rintro ⟨⟨g, hg⟩, hker⟩
  have hblk : gl4Blk (g : GL4M) = 1 := by
    have := congrArg (fun x : GL (Fin 2) (ZMod 2) => (x : Matrix (Fin 2) (Fin 2) (ZMod 2)))
      (MonoidHom.mem_ker.1 hker)
    exact this
  have b00 : (g : GL4M) 0 0 = 1 := congrFun (congrFun hblk 0) 0
  have b01 : (g : GL4M) 0 1 = 0 := congrFun (congrFun hblk 0) 1
  have b10 : (g : GL4M) 1 0 = 0 := congrFun (congrFun hblk 1) 0
  have b11 : (g : GL4M) 1 1 = 1 := congrFun (congrFun hblk 1) 1
  obtain ⟨s20, s30, s21, s31, s22, s23, s32, s33⟩ := gl4_u0_shape hg
  refine ⟨![(g : GL4M) 0 2, (g : GL4M) 0 3, (g : GL4M) 1 2, (g : GL4M) 1 3], ?_⟩
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  change gl4UM _ = (g : GL4M)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl4UM, b00, b01, b10, b11, s20, s30, s21, s31, s22, s23, s32, s33]

theorem gl4UElt_injective : Function.Injective gl4UElt := by
  intro c c' h
  apply gl4UM_injective
  have := congrArg (fun x : gl4RhoU.ker =>
    (((x : Subgroup.centralizer {gl4U0}) : GL4G) : GL4M)) h
  exact this

theorem gl4_card_ker_rhoU : Nat.card gl4RhoU.ker = 16 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨gl4UElt_injective, gl4UElt_surjective⟩),
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem gl4_card_centralizer_u0 : Nat.card (Subgroup.centralizer {gl4U0}) = 96 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup gl4RhoU.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ gl4RhoU_surjective).toEquiv,
    gl4_card_ker_rhoU, Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two] at h
  rw [h]
  norm_num

end CFSG.SeitzReduction.F4Pilot
