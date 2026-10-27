module

public import CFSG.GroupTheory.GL52.OrderThreeConj
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix

@[expose] def ord3K2M (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : M5 :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, B 0 0, B 0 1, B 0 2; 0, 0, B 1 0, B 1 1, B 1 2;
    0, 0, B 2 0, B 2 1, B 2 2]

theorem ord3K2M_mul (B B' : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    ord3K2M B * ord3K2M B' = ord3K2M (B * B') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ord3K2M, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_three]

theorem ord3K2M_one : ord3K2M 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem ord3K2M_commute (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    ord3K2M B * ord3T2M = ord3T2M * ord3K2M B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ord3K2M, ord3T2M, Matrix.mul_apply, Fin.sum_univ_five]

@[expose] def ord3K2Hom : GL (Fin 3) (ZMod 2) →* G52 where
  toFun B := mk5 (ord3K2M B) (ord3K2M ((B⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix _ _ _)) (by
    rw [ord3K2M_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, ord3K2M_one])
  map_one' := Units.ext (by rw [coe_mk5, Units.val_one, Units.val_one, ord3K2M_one])
  map_mul' B B' := Units.ext (by
    rw [coe_mk5, Units.val_mul, Units.val_mul, coe_mk5, coe_mk5, ord3K2M_mul])

theorem coe_ord3K2Hom (B : GL (Fin 3) (ZMod 2)) :
    ((ord3K2Hom B : G52) : M5) = ord3K2M (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  rfl

@[expose] def ord3Blk3 (g : M5) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![g 2 2, g 2 3, g 2 4; g 3 2, g 3 3, g 3 4; g 4 2, g 4 3, g 4 4]

@[expose] def ord3Idx : Fin 3 → Fin 5 :=
  ![2, 3, 4]

theorem ord3K2M_injective : Function.Injective ord3K2M := by
  intro C C' h
  ext a b
  have := congrFun (congrFun h (ord3Idx a)) (ord3Idx b)
  fin_cases a <;> fin_cases b <;> simpa [ord3K2M, ord3Idx] using this

theorem ord3K2Hom_injective : Function.Injective ord3K2Hom := by
  intro B B' h
  have h' := congrArg (fun g : G52 => (g : M5)) h
  simp only [coe_ord3K2Hom] at h'
  exact Units.ext (ord3K2M_injective h')

@[expose] def ord3K2 : Subgroup G52 :=
  ord3K2Hom.range

theorem ord3_facts2 :
    (∀ v : V5, (ord3T2M * ord3T2M + ord3T2M + 1) *ᵥ v = 0 → v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0) ∧
    (∀ v : V5, (ord3T2M + 1) *ᵥ v = 0 → v 0 = 0 ∧ v 1 = 0) ∧
    (ord3T2M * ord3T2M + ord3T2M + 1) *ᵥ Pi.single 0 1 = 0 ∧
    (ord3T2M + 1) *ᵥ Pi.single 2 1 = 0 ∧ (ord3T2M + 1) *ᵥ Pi.single 3 1 = 0 ∧
    (ord3T2M + 1) *ᵥ Pi.single 4 1 = 0 ∧ ord3T2M *ᵥ Pi.single 0 1 = Pi.single 1 1 := by
  decide +kernel

theorem ord3_T2_orbit : ∀ v : V5, v ≠ 0 → v 2 = 0 → v 3 = 0 → v 4 = 0 →
    ∃ m : Fin 3, ord3T2M ^ (m : ℕ) *ᵥ Pi.single 0 1 = v := by
  decide +kernel

theorem ord3_T2_fix : ∀ m : Fin 3, ord3T2M ^ (m : ℕ) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
    (m : ℕ) = 0 := by
  decide +kernel

theorem ord3_T2_matrix_commute {g : G52} (hg : g ∈ Subgroup.centralizer {ord3T2}) :
    (g : M5) * ord3T2M = ord3T2M * (g : M5) := by
  have := congrArg (fun x : G52 => (x : M5)) (Subgroup.mem_centralizer_singleton_iff.1 hg)
  simpa [ord3T2] using this

theorem ord3_shape {y : G52} (hy : y ∈ Subgroup.centralizer {ord3T2})
    (hy0 : (y : M5) *ᵥ Pi.single 0 1 = Pi.single 0 1)
    (hy1 : (y : M5) *ᵥ Pi.single 1 1 = Pi.single 1 1) :
    (y : M5) = ord3K2M (ord3Blk3 (y : M5)) := by
  obtain ⟨-, kC, -, hC2, hC3, hC4, -⟩ := ord3_facts2
  have hc := ord3_T2_matrix_commute hy
  have hc1 : (y : M5) * (ord3T2M + 1) = (ord3T2M + 1) * (y : M5) := by
    rw [mul_add, add_mul, hc, mul_one, one_mul]
  obtain ⟨z20, z21⟩ := kC _ (by rw [← mulVec_comm hc1, hC2, mulVec_zero])
  obtain ⟨z30, z31⟩ := kC _ (by rw [← mulVec_comm hc1, hC3, mulVec_zero])
  obtain ⟨z40, z41⟩ := kC _ (by rw [← mulVec_comm hc1, hC4, mulVec_zero])
  simp only [mulVec_single_one, col_apply] at z20 z21 z30 z31 z40 z41
  have e : ∀ i : Fin 5, (y : M5) i 0 = (Pi.single 0 1 : V5) i ∧
      (y : M5) i 1 = (Pi.single 1 1 : V5) i := fun i => by
    have h0 := congrFun hy0 i
    have h1 := congrFun hy1 i
    simp only [mulVec_single_one, col_apply] at h0 h1
    exact ⟨h0, h1⟩
  obtain ⟨e00, e01⟩ := e 0
  obtain ⟨e10, e11⟩ := e 1
  obtain ⟨e20, e21⟩ := e 2
  obtain ⟨e30, e31⟩ := e 3
  obtain ⟨e40, e41⟩ := e 4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ord3K2M, ord3Blk3, e00, e01, e10, e11, e20, e21, e30, e31, e40, e41, z20, z21, z30,
      z31, z40, z41]

theorem ord3_mem_K2 {x : G52} (hx : x ∈ Subgroup.centralizer {ord3T2})
    (h0 : (x : M5) *ᵥ Pi.single 0 1 = Pi.single 0 1) : x ∈ ord3K2 := by
  obtain ⟨-, -, -, -, -, -, hT0⟩ := ord3_facts2
  have hc := ord3_T2_matrix_commute hx
  have h1 : (x : M5) *ᵥ Pi.single 1 1 = Pi.single 1 1 := by
    rw [← hT0, mulVec_comm hc, h0]
  have hx' : x⁻¹ ∈ Subgroup.centralizer {ord3T2} := inv_mem hx
  have h0' : ((x⁻¹ : G52) : M5) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    conv_lhs => rw [← h0]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have h1' : ((x⁻¹ : G52) : M5) *ᵥ Pi.single 1 1 = Pi.single 1 1 := by
    conv_lhs => rw [← h1]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hx0 := ord3_shape hx h0 h1
  have hxi := ord3_shape hx' h0' h1'
  have hBB : ord3Blk3 (x : M5) * ord3Blk3 ((x⁻¹ : G52) : M5) = 1 := by
    apply ord3K2M_injective
    rw [← ord3K2M_mul, ← hx0, ← hxi, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      ord3K2M_one]
  refine ⟨⟨ord3Blk3 (x : M5), ord3Blk3 ((x⁻¹ : G52) : M5), hBB, mul_eq_one_comm.1 hBB⟩,
    Units.ext ?_⟩
  rw [coe_ord3K2Hom]
  exact hx0.symm

theorem ord3_K2_le : ord3K2 ≤ Subgroup.centralizer {ord3T2} := by
  rintro _ ⟨B, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_ord3K2Hom]
  exact ord3K2M_commute _

theorem ord3_centralizer_T2 :
    IsInnerDirectProduct (Subgroup.zpowers ord3T2) ord3K2 (Subgroup.centralizer {ord3T2}) := by
  classical
  obtain ⟨kP, kC, hP0, -, -, -, -⟩ := ord3_facts2
  refine ⟨le_antisymm (sup_le ?_ ord3_K2_le) fun g hg => ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  ·
    have hc := ord3_T2_matrix_commute hg
    have hcP : (g : M5) * (ord3T2M * ord3T2M + ord3T2M + 1) =
        (ord3T2M * ord3T2M + ord3T2M + 1) * (g : M5) := by
      simp only [mul_add, add_mul, mul_one, one_mul, ← mul_assoc, hc]
      rw [mul_assoc, hc, ← mul_assoc]
    have hg0P : (ord3T2M * ord3T2M + ord3T2M + 1) *ᵥ ((g : M5) *ᵥ Pi.single 0 1) = 0 := by
      rw [← mulVec_comm hcP, hP0, mulVec_zero]
    obtain ⟨h2, h3, h4⟩ := kP _ hg0P
    have hne : (g : M5) *ᵥ Pi.single 0 1 ≠ 0 := fun h =>
      (by decide : (Pi.single 0 1 : V5) ≠ 0) (eq_zero_of_mulVec_eq_zero g h)
    obtain ⟨m, hm⟩ := ord3_T2_orbit _ hne h2 h3 h4
    have hgm : (ord3T2 ^ (m : ℕ))⁻¹ * g ∈ Subgroup.centralizer {ord3T2} :=
      mul_mem (inv_mem (pow_mem (Subgroup.mem_centralizer_singleton_iff.2 rfl) _)) hg
    have h0 : (((ord3T2 ^ (m : ℕ))⁻¹ * g : G52) : M5) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
      have hpow : (ord3T2M ^ (m : ℕ) : M5) = ((ord3T2 ^ (m : ℕ) : G52) : M5) := by
        rw [Units.val_pow_eq_pow_val]
        rfl
      rw [Units.val_mul, ← mulVec_mulVec, ← hm, mulVec_mulVec, hpow, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, one_mulVec]
    have hK := ord3_mem_K2 hgm h0
    have e : g = ord3T2 ^ (m : ℕ) * ((ord3T2 ^ (m : ℕ))⁻¹ * g) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
      (Subgroup.mem_sup_right hK)
  · refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxz, ⟨B, rfl⟩⟩ := Subgroup.mem_inf.1 hx
    rw [mem_zpowers_iff_mem_range_orderOf, orderOf_ord3T2] at hxz
    obtain ⟨m, hm, hmx⟩ := Finset.mem_image.1 hxz
    have he : ((ord3K2Hom B : G52) : M5) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
      rw [coe_ord3K2Hom]
      ext i
      fin_cases i <;> simp [ord3K2M, mulVec, dotProduct, Fin.sum_univ_five]
    rw [← hmx, Units.val_pow_eq_pow_val] at he
    have hm0 := ord3_T2_fix ⟨m, Finset.mem_range.1 hm⟩ he
    rw [Subgroup.mem_bot, ← hmx]
    simp only at hm0
    rw [hm0, pow_zero]
  · intro a ha b hb
    have hbC := ord3_K2_le hb
    rw [Subgroup.mem_centralizer_singleton_iff] at hbC
    have hle : Subgroup.zpowers ord3T2 ≤ Subgroup.centralizer {b} := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hbC.symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle ha)

theorem ord3_K2_equiv_GL : Nonempty (ord3K2 ≃* GL (Fin 3) (ZMod 2)) :=
  ⟨(MonoidHom.ofInjective ord3K2Hom_injective).symm⟩

theorem ord3_K2_equiv_PSL :
    Nonempty (ord3K2 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  exact ⟨(MonoidHom.ofInjective ord3K2Hom_injective).symm.trans e⟩

end CFSG.GroupTheory.GL52
