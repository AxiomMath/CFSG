module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4NSAlg
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4X

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4

open Matrix QuadraticAlgebra
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def om : QE F := ⟨0, 1⟩

theorem om_mul_self : (om : QE F) * om = -1 :=
  QuadraticAlgebra.ext (by simp [om]) (by simp [om])

theorem Phi_neg_om :
    Phi (!![-om, 0; 0, -om] : Matrix (Fin 2) (Fin 2) (QE F)) =
      ((u0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by
  rw [Phi_apply, coe_u0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [om]

theorem Phi_t0 :
    Phi (!![om, 0; 0, -om] : Matrix (Fin 2) (Fin 2) (QE F)) =
      ((t0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by
  rw [Phi_apply, coe_t0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [om]

theorem Phi_U1 :
    Phi (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (QE F)) =
      ((U1 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by
  rw [Phi_apply, coe_U1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_Phi_of_comm (g : Matrix (Fin 4) (Fin 4) F)
    (h : g * ((u0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      ((u0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * g) :
    ∃ N : Matrix (Fin 2) (Fin 2) (QE F), Phi N = g := by
  rw [coe_u0] at h
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e02 := congrFun (congrFun h 0) 2
  have e03 := congrFun (congrFun h 0) 3
  have e20 := congrFun (congrFun h 2) 0
  have e21 := congrFun (congrFun h 2) 1
  have e22 := congrFun (congrFun h 2) 2
  have e23 := congrFun (congrFun h 2) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e00 e01 e02 e03 e20 e21 e22 e23
  refine ⟨!![⟨g 0 0, g 1 0⟩, ⟨g 0 2, g 1 2⟩; ⟨g 2 0, g 3 0⟩, ⟨g 2 2, g 3 2⟩], ?_⟩
  rw [Phi_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first
    | linear_combination e00 | linear_combination (-1 : F) * e00
    | linear_combination e01 | linear_combination (-1 : F) * e01
    | linear_combination e02 | linear_combination (-1 : F) * e02
    | linear_combination e03 | linear_combination (-1 : F) * e03
    | linear_combination e20 | linear_combination (-1 : F) * e20
    | linear_combination e21 | linear_combination (-1 : F) * e21
    | linear_combination e22 | linear_combination (-1 : F) * e22
    | linear_combination e23

@[expose] def Qns (F : Type) [Field F] : Subgroup SL(4, F) :=
  (PhiSL : SL(2, QE F) →* SL(4, F)).range

theorem coe_PhiSL (M : SL(2, QE F)) :
    ((PhiSL M : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = Phi (M : Matrix (Fin 2) (Fin 2) (QE F)) :=
  rfl

theorem mem_Qns {p : SL(4, F)} : p ∈ Qns F ↔ ∃ M : SL(2, QE F), PhiSL M = p :=
  MonoidHom.mem_range

theorem Qns_comm {p : SL(4, F)} (hp : p ∈ Qns F) : p * u0 F = u0 F * p := by
  obtain ⟨M, rfl⟩ := mem_Qns.mp hp
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← Phi_neg_om,
    coe_PhiSL, ← map_mul, ← map_mul]
  congr 1
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem t0_mem_Qns : t0 F ∈ Qns F := by
  have hdet : (!![om, 0; 0, -om] : Matrix (Fin 2) (Fin 2) (QE F)).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have := om_mul_self (F := F)
    linear_combination (-1 : QE F) * this
  let M : SL(2, QE F) := ⟨!![om, 0; 0, -om], hdet⟩
  exact ⟨M, Subtype.ext Phi_t0⟩

theorem U1_mem_Qns : U1 F ∈ Qns F := by
  have hdet : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (QE F)).det = 1 := by
    simp [Matrix.det_fin_two_of]
  let M : SL(2, QE F) := ⟨!![1, 1; 0, 1], hdet⟩
  exact ⟨M, Subtype.ext Phi_U1⟩

theorem Qns_norm_of_comm {g : SL(4, F)} (hg : g * u0 F = u0 F * g) {p : SL(4, F)}
    (hp : p ∈ Qns F) : g * p * g⁻¹ ∈ Qns F := by
  obtain ⟨M, rfl⟩ := mem_Qns.mp hp
  have hg' : g⁻¹ * u0 F = u0 F * g⁻¹ := by
    have := (Commute.inv_left (show Commute g (u0 F) from hg)).eq
    exact this
  obtain ⟨N, hN⟩ := exists_Phi_of_comm (g : Matrix (Fin 4) (Fin 4) F) (by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hg])
  obtain ⟨N₂, hN₂⟩ := exists_Phi_of_comm ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) (by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hg'])
  have hNN : N * N₂ = 1 := by
    apply Phi_injective
    rw [map_mul, hN, hN₂, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, map_one]
    rfl
  have hdet : (N * (M : Matrix (Fin 2) (Fin 2) (QE F)) * N₂).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, M.2, mul_one, ← Matrix.det_mul, hNN, Matrix.det_one]
  let M' : SL(2, QE F) := ⟨N * (M : Matrix (Fin 2) (Fin 2) (QE F)) * N₂, hdet⟩
  refine ⟨M', Subtype.ext ?_⟩
  have h1 : ((PhiSL M' : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      Phi (N * (M : Matrix (Fin 2) (Fin 2) (QE F)) * N₂) := rfl
  rw [h1, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_PhiSL M,
    map_mul, map_mul, hN, hN₂]

@[expose] def c0 (F : Type) [Field F] : SL(4, F) :=
  ⟨!![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1],
    by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]⟩

theorem coe_c0 : ((c0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1] := rfl

theorem c0_mul_self : c0 F * c0 F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_c0, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem c0_inv : (c0 F)⁻¹ = c0 F := inv_eq_of_mul_eq_one_right c0_mul_self

theorem c0_conj_u0 : c0 F * u0 F * (c0 F)⁻¹ = zneg F * u0 F := by
  rw [c0_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_c0, coe_u0, coe_zneg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem c0_conj_Phi (N : Matrix (Fin 2) (Fin 2) (QE F)) :
    ((c0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * Phi N *
        ((c0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = Phi (N.map star) := by
  rw [coe_c0, Phi_apply, Phi_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem det_map_star (N : Matrix (Fin 2) (Fin 2) (QE F)) : (N.map star).det = star N.det := by
  have h := RingHom.map_det (starRingEnd (QE F)) N
  have hf : ((starRingEnd (QE F)) : QE F → QE F) = star := funext fun x => starRingEnd_apply x
  rw [RingHom.mapMatrix_apply, hf] at h
  exact h.symm

theorem Qns_conj_c0 {p : SL(4, F)} (hp : p ∈ Qns F) : c0 F * p * (c0 F)⁻¹ ∈ Qns F := by
  obtain ⟨M, rfl⟩ := mem_Qns.mp hp
  have hdet : ((M : Matrix (Fin 2) (Fin 2) (QE F)).map star).det = 1 := by
    rw [det_map_star, M.2, star_one]
  let M' : SL(2, QE F) := ⟨(M : Matrix (Fin 2) (Fin 2) (QE F)).map star, hdet⟩
  refine ⟨M', Subtype.ext ?_⟩
  have h1 : ((PhiSL M' : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      Phi ((M : Matrix (Fin 2) (Fin 2) (QE F)).map star) := rfl
  rw [c0_inv, h1, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_PhiSL M, c0_conj_Phi]

theorem zneg_mul_self : zneg F * zneg F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_zneg, Matrix.SpecialLinearGroup.coe_one]
  simp

theorem conj_u0_cases {g : SL(4, F)}
    (hg : g * u0 F * g⁻¹ * (u0 F)⁻¹ ∈ Subgroup.center SL(4, F)) :
    g * u0 F * g⁻¹ = u0 F ∨ g * u0 F * g⁻¹ = zneg F * u0 F := by
  obtain ⟨r, -, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have hzc : g * zneg F * g⁻¹ = zneg F := by
    rw [Subgroup.mem_center_iff.mp zneg_mem_center g]
    group
  have hyy : (g * u0 F * g⁻¹) * (g * u0 F * g⁻¹) = zneg F := by
    calc (g * u0 F * g⁻¹) * (g * u0 F * g⁻¹) = g * (u0 F * u0 F) * g⁻¹ := by group
      _ = zneg F := by rw [u0_mul_self, hzc]
  have hy : ((g * u0 F * g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      r • ((u0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by
    have h1 : ((g * u0 F * g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
        ((g * u0 F * g⁻¹ * (u0 F)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
          ((u0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
    rw [h1, ← hrA, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul]
  have huu : ((u0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
      ((u0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = -1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, u0_mul_self, coe_zneg]
  have hr2 : r * r = 1 := by
    have h1 : ((g * u0 F * g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
        ((g * u0 F * g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
        (r * r) • (-1 : Matrix (Fin 4) (Fin 4) F) := by
      rw [hy, Matrix.smul_mul, Matrix.mul_smul, huu, smul_smul]
    rw [← Matrix.SpecialLinearGroup.coe_mul, hyy, coe_zneg] at h1
    have := congrFun (congrFun h1 0) 0
    simp at this
    linear_combination -this
  rcases mul_self_eq_one_iff.mp hr2 with hr1 | hr1
  · left
    apply Subtype.ext
    rw [hy, hr1, one_smul]
  · right
    apply Subtype.ext
    rw [hy, hr1, neg_one_smul, Matrix.SpecialLinearGroup.coe_mul, coe_zneg, neg_one_mul]

instance [Finite F] : Finite (QE F) :=
  Finite.of_equiv (F × F) (QuadraticAlgebra.equivProd (-1 : F) 0).symm

theorem four_le_card_QE [Finite F] (h4 : 4 ≤ Nat.card F) : 4 ≤ Nat.card (QE F) :=
  h4.trans (Nat.card_le_card_of_injective _
    (QuadraticAlgebra.C_injective (R := F) (a := (-1 : F)) (b := 0)))

theorem PhiSL_injective : Function.Injective (PhiSL : SL(2, QE F) →* SL(4, F)) := by
  intro M N h
  apply Subtype.ext
  apply Phi_injective
  exact congrArg (fun x : SL(4, F) => (x : Matrix (Fin 4) (Fin 4) F)) h

theorem slayer_u0_ns [Fact (¬ IsSquare (-1 : F))] [Finite F] (h4 : 4 ≤ Nat.card F) :
    SLayer (u0 F) (Qns F) := by
  have hq : CFSG.IsQuasisimple SL(2, QE F) := isQuasisimple_sl2 (four_le_card_QE h4)
  have hperfSL : Group.IsPerfect SL(2, QE F) := hq.1
  have hperf : Group.IsPerfect (Qns F) := Group.IsPerfect.range (PhiSL : SL(2, QE F) →* SL(4, F))
  refine ⟨fun p hp => Qns_comm hp, ?_, (Subgroup.commutator_eq_self (H := Qns F)).symm.le, ?_⟩
  · intro g hg p hp
    rcases conj_u0_cases hg with h | h
    · exact Qns_norm_of_comm (mul_inv_eq_iff_eq_mul.mp h) hp
    · have hĝ : c0 F * g * u0 F = u0 F * (c0 F * g) := by
        refine mul_inv_eq_iff_eq_mul.mp ?_
        calc c0 F * g * u0 F * (c0 F * g)⁻¹ = c0 F * (g * u0 F * g⁻¹) * (c0 F)⁻¹ := by group
          _ = c0 F * (zneg F * u0 F) * (c0 F)⁻¹ := by rw [h]
          _ = zneg F * (c0 F * u0 F * (c0 F)⁻¹) := by
            have hz := Subgroup.mem_center_iff.mp zneg_mem_center (c0 F)
            calc c0 F * (zneg F * u0 F) * (c0 F)⁻¹ = (c0 F * zneg F) * u0 F * (c0 F)⁻¹ := by group
              _ = (zneg F * c0 F) * u0 F * (c0 F)⁻¹ := by rw [hz]
              _ = zneg F * (c0 F * u0 F * (c0 F)⁻¹) := by group
          _ = u0 F := by rw [c0_conj_u0, ← mul_assoc, zneg_mul_self, one_mul]
      have hq1 := Qns_conj_c0 (Qns_norm_of_comm hĝ hp)
      have e : c0 F * (c0 F * g * p * (c0 F * g)⁻¹) * (c0 F)⁻¹ = g * p * g⁻¹ := by
        rw [_root_.mul_inv_rev, c0_inv]
        calc c0 F * (c0 F * g * p * (g⁻¹ * c0 F)) * c0 F =
            (c0 F * c0 F) * g * p * g⁻¹ * (c0 F * c0 F) := by simp only [mul_assoc]
          _ = g * p * g⁻¹ := by rw [c0_mul_self, one_mul, mul_one]
      rwa [e] at hq1
  · refine ⟨{Qns F}, ?_, ?_⟩
    · intro H hH
      rw [Set.mem_singleton_iff] at hH
      subst hH
      refine ⟨le_rfl, isQuasisimple_of_equiv (MonoidHom.ofInjective PhiSL_injective) hq, ?_⟩
      intro p hp h hh
      exact (Qns F).mul_mem ((Qns F).mul_mem hp hh) ((Qns F).inv_mem hp)
    · exact le_iSup₂_of_le (Qns F) rfl le_rfl

theorem exists_layer_u0_of_nonsplit [Finite F] (h4 : 4 ≤ Nat.card F)
    (hns : ¬ ∃ i : F, i * i = -1) :
    ∃ Q : Subgroup SL(4, F), SLayer (u0 F) Q ∧ t0 F ∈ Q ∧ U1 F ∈ Q := by
  have : Fact (¬ IsSquare (-1 : F)) := ⟨fun ⟨r, hr⟩ => hns ⟨r, hr.symm⟩⟩
  exact ⟨Qns F, slayer_u0_ns h4, t0_mem_Qns, U1_mem_Qns⟩

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
