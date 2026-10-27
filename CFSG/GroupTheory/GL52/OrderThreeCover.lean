module

public import CFSG.GroupTheory.GL52.OrderThreeFour
public import CFSG.GroupTheory.GL52.SylowThree

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix

theorem coe_ord3T2 : ((ord3T2 : G52) : M5) = ord3T2M :=
  coe_mk5 _ _ _

theorem coe_ord3T4 : ((ord3T4 : G52) : M5) = ord3T4M :=
  coe_mk5 _ _ _

theorem ord3_trace_T4 : Matrix.trace ord3T4M = 1 := by
  decide +kernel

theorem trace_eq_of_isConj {a y : G52} (h : IsConj a y) :
    Matrix.trace (y : M5) = Matrix.trace (a : M5) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  rw [Units.val_mul, Units.val_mul, syl3_trace_conj]

theorem ord3_isConj_T2_of_trace {y : G52} (hy : orderOf y = 3)
    (ht : Matrix.trace (y : M5) = 0) : IsConj ord3T2 y := by
  rcases ord3_classify hy with ⟨-, hc⟩ | ⟨-, hc⟩
  · exact hc
  · rw [trace_eq_of_isConj hc, coe_ord3T4, ord3_trace_T4] at ht
    exact absurd ht (by decide)

theorem ord3_isConj_T4_of_trace {y : G52} (hy : orderOf y = 3)
    (ht : Matrix.trace (y : M5) = 1) : IsConj ord3T4 y := by
  rcases ord3_classify hy with ⟨-, hc⟩ | ⟨-, hc⟩
  · rw [trace_eq_of_isConj hc, coe_ord3T2, syl3_trace_ab.1] at ht
    exact absurd ht (by decide)
  · exact hc

theorem ord3_not_isConj_T4_T2 : ¬ IsConj ord3T4 ord3T2 := fun h => by
  have := trace_eq_of_isConj h
  rw [coe_ord3T2, coe_ord3T4, syl3_trace_ab.1, ord3_trace_T4] at this
  exact absurd this (by decide)

@[expose] def ord3DiagM : Matrix (Fin 2) (Fin 2) F4 :=
  Matrix.diagonal ![F4root, F4root ^ 2]

theorem ord3DiagM_det : ord3DiagM.det = 1 := by
  have h : F4root * F4root ^ 2 = 1 := by
    calc F4root * F4root ^ 2 = F4root ^ 3 := by ring
      _ = 1 := F4root_cube
  simpa [ord3DiagM, Matrix.det_diagonal, Fin.prod_univ_two] using h

@[expose] def ord3DiagSL : Matrix.SpecialLinearGroup (Fin 2) F4 :=
  ⟨ord3DiagM, ord3DiagM_det⟩

@[expose] def ord3DiagPhiM : M5 :=
  !![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]

theorem ord3_diagPhi_facts : ord3DiagPhiM ^ 3 = 1 ∧ ord3DiagPhiM ≠ 1 ∧
    Matrix.trace ord3DiagPhiM = 1 := by
  decide +kernel

theorem ord3PhiM_diag : ord3PhiM ord3DiagM = ord3DiagPhiM := by
  have h2 : F4L (F4root ^ 2) = !![1, 1; 1, 0] := by
    rw [map_pow, F4L_root]
    decide +kernel
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ord3PhiM, ord3DiagM, ord3DiagPhiM, F4L_root, F4Omega, h2]

theorem ord3_exists_T4_mem_K4 : ∃ y ∈ ord3K4, orderOf y = 3 ∧ IsConj ord3T4 y := by
  set y := ord3K4Hom ord3DiagSL with hy
  have hyM : (y : M5) = ord3DiagPhiM := by
    rw [hy, ← ord3PhiM_diag]
    rfl
  obtain ⟨h3, h1, ht⟩ := ord3_diagPhi_facts
  have hy3 : orderOf y = 3 := by
    refine orderOf_eq_prime (Units.ext ?_) fun h => h1 ?_
    · rw [Units.val_pow_eq_pow_val, hyM, Units.val_one, h3]
    · rw [← hyM, h, Units.val_one]
  refine ⟨y, ⟨ord3DiagSL, rfl⟩, hy3, ord3_isConj_T4_of_trace hy3 ?_⟩
  rw [hyM, ht]

theorem card_fixedPoints_of_orderOf_eq_three {α : Type*} [Finite α] (hα : Nat.card α = 5)
    {π : Equiv.Perm α} (hπ : orderOf π = 3) : Nat.card (Function.fixedPoints π) = 2 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers π) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hπ, pow_one])
  have hfix : MulAction.fixedPoints (Subgroup.zpowers π) α = Function.fixedPoints π := by
    ext x
    rw [MulAction.mem_fixedPoints, Function.mem_fixedPoints, Function.IsFixedPt]
    constructor
    · intro h
      exact h ⟨π, Subgroup.mem_zpowers π⟩
    · rintro h ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h k
  have hmod := hP.card_modEq_card_fixedPoints α
  rw [hfix, hα] at hmod
  have hne : π ≠ 1 := fun h => by
    rw [h, orderOf_one] at hπ
    exact absurd hπ (by norm_num)
  obtain ⟨x, hx⟩ : ∃ x, π x ≠ x := not_forall.mp fun h => hne (Equiv.ext h)
  have hlt : Nat.card (Function.fixedPoints π) < 5 := by
    rw [Nat.card_coe_set_eq, ← hα, ← Set.ncard_univ]
    refine Set.ncard_lt_ncard (Set.ssubset_univ_iff.mpr fun h => hx ?_) Set.finite_univ
    have hxm : x ∈ Function.fixedPoints π := by
      rw [h]
      exact Set.mem_univ x
    exact hxm
  unfold Nat.ModEq at hmod
  omega

open Projectivization

abbrev ord3P1 : Type :=
  Projectivization F4 (Fin 2 → F4)

theorem ord3_card_P1 : Nat.card ord3P1 = 5 := by
  have h := Projectivization.card_of_finrank_two F4 (Fin 2 → F4) (by simp)
  rw [card_F4] at h
  exact h

@[expose] def ord3P1Equiv : ord3P1 ≃ Fin 5 :=
  Finite.equivFinOfCardEq ord3_card_P1

@[expose] def ord3P1Perm : Matrix.SpecialLinearGroup (Fin 2) F4 →* Equiv.Perm (Fin 5) :=
  ord3P1Equiv.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (Matrix.SpecialLinearGroup (Fin 2) F4) ord3P1)

theorem ord3P1Perm_injective : Function.Injective ord3P1Perm := by
  have h : Function.Injective
      (MulAction.toPermHom (Matrix.SpecialLinearGroup (Fin 2) F4) ord3P1) := by
    rw [← MonoidHom.ker_eq_bot_iff, Projectivization.SL_mulAction_ker, ord3_center_SL2_F4]
  exact ord3P1Equiv.permCongrHom.injective.comp h

@[expose] def ord3PermMat : Equiv.Perm (Fin 5) →* G52 :=
  (Matrix.permMatrixHom : Equiv.Perm (Fin 5) →* M5).toHomUnits

theorem coe_ord3PermMat (σ : Equiv.Perm (Fin 5)) :
    ((ord3PermMat σ : G52) : M5) = σ⁻¹.permMatrix (ZMod 2) :=
  rfl

theorem ord3PermMat_injective : Function.Injective ord3PermMat := by
  intro σ τ h
  have h1 : σ⁻¹.permMatrix (ZMod 2) = τ⁻¹.permMatrix (ZMod 2) := by
    rw [← coe_ord3PermMat, ← coe_ord3PermMat, h]
  have h2 := PEquiv.toMatrix_injective h1
  have h3 : σ⁻¹ = τ⁻¹ := Equiv.ext fun x => by
    have := congrArg (fun f => f x) h2
    simpa [Equiv.toPEquiv_apply] using this
  exact inv_injective h3

@[expose] def ord3P1Hom : Matrix.SpecialLinearGroup (Fin 2) F4 →* G52 :=
  ord3PermMat.comp ord3P1Perm

theorem ord3P1Hom_injective : Function.Injective ord3P1Hom :=
  ord3PermMat_injective.comp ord3P1Perm_injective

@[expose] def ord3K5 : Subgroup G52 :=
  ord3P1Hom.range

theorem ord3_K5_equiv : Nonempty (ord3K5 ≃* Matrix.SpecialLinearGroup (Fin 2) F4) :=
  ⟨(MonoidHom.ofInjective ord3P1Hom_injective).symm⟩

theorem ord3_K4_equiv : Nonempty (ord3K4 ≃* Matrix.SpecialLinearGroup (Fin 2) F4) :=
  ⟨(MonoidHom.ofInjective ord3K4Hom_injective).symm⟩

theorem ord3_exists_T2_mem_K5 : ∃ y ∈ ord3K5, orderOf y = 3 ∧ IsConj ord3T2 y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F4 := Fintype.ofFinite F4
  obtain ⟨A, hA⟩ := exists_prime_orderOf_dvd_card' (G := Matrix.SpecialLinearGroup (Fin 2) F4) 3
    (by rw [ord3_card_SL2_F4]; norm_num)
  set y := ord3P1Hom A with hy
  have hy3 : orderOf y = 3 := by
    rw [hy, orderOf_injective ord3P1Hom ord3P1Hom_injective A, hA]
  have hπ : orderOf (ord3P1Perm A)⁻¹ = 3 := by
    rw [orderOf_inv, orderOf_injective ord3P1Perm ord3P1Perm_injective A, hA]
  have hfix := card_fixedPoints_of_orderOf_eq_three (by simp) hπ
  have ht : Matrix.trace (y : M5) = 0 := by
    rw [hy, ord3P1Hom, MonoidHom.comp_apply, coe_ord3PermMat, Matrix.trace_permutation,
      ← Nat.card_coe_set_eq, hfix]
    decide
  exact ⟨y, ⟨A, rfl⟩, hy3, ord3_isConj_T2_of_trace hy3 ht⟩

end CFSG.GroupTheory.GL52
