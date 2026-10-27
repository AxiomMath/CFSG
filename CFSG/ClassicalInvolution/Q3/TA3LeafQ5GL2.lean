module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution Matrix
open scoped MatrixGroups commutatorElement

namespace Q5GL2

variable {F : Type} [Field F] {H : Subgroup (GL (Fin 2) F)} {X : Type} [Group X]

@[expose] def slPart (H : Subgroup (GL (Fin 2) F)) : Subgroup H :=
  (GeneralLinearGroup.det.comp H.subtype).ker

theorem mem_slPart {A : H} : A ∈ slPart H ↔ GeneralLinearGroup.det (A : GL (Fin 2) F) = 1 :=
  MonoidHom.mem_ker

@[expose] def CubeKer (π : H →* X) : Prop :=
  ∀ A : H, π A = 1 → ∃ ω : Fˣ, ω ^ 3 = 1 ∧ (A : GL (Fin 2) F) = GeneralLinearGroup.scalar (Fin 2) ω

@[expose] def SLCentScalar (H : Subgroup (GL (Fin 2) F)) : Prop :=
  ∀ A : GL (Fin 2) F, (∀ B ∈ slPart H, A * (B : GL (Fin 2) F) = (B : GL (Fin 2) F) * A) →
    ∃ c : Fˣ, A = GeneralLinearGroup.scalar (Fin 2) c

theorem scalar_mul_comm (c : Fˣ) (B : GL (Fin 2) F) :
    GeneralLinearGroup.scalar (Fin 2) c * B = B * GeneralLinearGroup.scalar (Fin 2) c :=
  Units.ext (by
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)

theorem scalar_injective {a b : Fˣ}
    (h : GeneralLinearGroup.scalar (Fin 2) a = GeneralLinearGroup.scalar (Fin 2) b) : a = b := by
  have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
  exact Units.ext this

theorem eq_one_of_sq_of_cube {ω : Fˣ} (h2 : ω ^ 2 = 1) (h3 : ω ^ 3 = 1) : ω = 1 := by
  calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, one_mul]

theorem commutator_range_le (π : H →* X) : ⁅π.range, π.range⁆ ≤ (slPart H).map π := by
  rw [Subgroup.commutator_le]
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  rw [← map_commutatorElement]
  refine ⟨⁅A, B⁆, ?_, rfl⟩
  show ⁅A, B⁆ ∈ slPart H
  rw [slPart, MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

theorem injective_slPart {π : H →* X} (hk : CubeKer π) :
    Function.Injective (π.comp (slPart H).subtype) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  obtain ⟨ω, hω3, hω⟩ := hk A hA
  have hdet : GeneralLinearGroup.det ((A : H) : GL (Fin 2) F) = 1 := mem_slPart.mp A.2
  rw [hω, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hω1 := eq_one_of_sq_of_cube hdet hω3
  apply Subtype.ext
  apply Subtype.ext
  rw [hω, hω1, map_one]
  rfl

theorem exists_scalar_of_commute {π : H →* X} (hk : CubeKer π) (hc : SLCentScalar H) {A : H}
    (h : ∀ B ∈ slPart H, π A * π B = π B * π A) :
    ∃ c : Fˣ, (A : GL (Fin 2) F) = GeneralLinearGroup.scalar (Fin 2) c := by
  refine hc A fun B hB => ?_
  have h1 : π ⁅A, B⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (h B hB)
  obtain ⟨ω, hω3, hω⟩ := hk _ h1
  have hcoe : ((⁅A, B⁆ : H) : GL (Fin 2) F) = ⁅(A : GL (Fin 2) F), (B : GL (Fin 2) F)⁆ :=
    map_commutatorElement H.subtype A B
  have hdet : GeneralLinearGroup.det ((⁅A, B⁆ : H) : GL (Fin 2) F) = 1 := by
    rw [hcoe, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  rw [hω, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hω1 := eq_one_of_sq_of_cube hdet hω3
  rw [hω1, map_one, hcoe] at hω
  exact commutatorElement_eq_one_iff_mul_comm.mp hω

theorem eq_or_of_scalar_sq {π : H →* X} (hk : CubeKer π) {N1 A : H}
    (hN1 : (N1 : GL (Fin 2) F) = -1) {c : Fˣ}
    (hA : (A : GL (Fin 2) F) = GeneralLinearGroup.scalar (Fin 2) c) (h : π A * π A = 1) :
    π A = 1 ∨ π A = π N1 := by
  obtain ⟨ω, hω3, hω⟩ := hk (A * A) (by rw [map_mul, h])
  have hcc : c * c = ω := by
    apply scalar_injective
    rw [map_mul, ← hω, Subgroup.coe_mul, hA]
  have hc6 : (c ^ 3) * (c ^ 3) = 1 := by
    rw [← mul_pow, hcc, hω3]
  have hA3 : π A = π (A ^ 3) := by
    rw [map_pow, pow_succ, pow_two, h, one_mul]
  have hval : ((c ^ 3 : Fˣ) : F) * ((c ^ 3 : Fˣ) : F) = 1 := by
    rw [← Units.val_mul, hc6, Units.val_one]
  rcases mul_self_eq_one_iff.mp hval with h1 | h1
  · left
    have h1' : c ^ 3 = 1 := Units.ext (by rw [Units.val_one]; exact h1)
    have : A ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hA, ← map_pow, h1', map_one]
      rfl)
    rw [hA3, this, map_one]
  · right
    have : A ^ 3 = N1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hA, ← map_pow, hN1]
      refine Units.ext ?_
      rw [GeneralLinearGroup.coe_scalar, show (c ^ 3 : Fˣ).1 = -1 from h1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp)
    rw [hA3, this]

theorem mem_map_slPart_of_sq {π : H →* X} (hk : CubeKer π) {N1 A : H}
    (hN1 : (N1 : GL (Fin 2) F) = -1) (hA : π A * π A = π N1)
    (hns : ∀ c : Fˣ, (A : GL (Fin 2) F) ≠ GeneralLinearGroup.scalar (Fin 2) c) :
    π A ∈ (slPart H).map π := by
  obtain ⟨ω, hω3, hω⟩ := hk (A * A * N1⁻¹) (by rw [map_mul, map_mul, hA, map_inv, mul_inv_cancel])
  set W := A * A * N1⁻¹ with hW
  have hπW : π W = 1 := by rw [hW, map_mul, map_mul, hA, map_inv, mul_inv_cancel]
  set A' := W * A with hA'
  have hπA' : π A' = π A := by rw [hA', map_mul, hπW, one_mul]
  have hAA : (A : GL (Fin 2) F) * A = GeneralLinearGroup.scalar (Fin 2) ω * -1 := by
    have e : (A : GL (Fin 2) F) * A = (W : GL (Fin 2) F) * N1 := by
      rw [hW, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    rw [e, hω, hN1]
  have hA'eq : (A' : GL (Fin 2) F) = GeneralLinearGroup.scalar (Fin 2) ω * A := by
    rw [hA', Subgroup.coe_mul, hω]
  have hsq : ((A' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((A' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
    have e : (A' : GL (Fin 2) F) * A' = -1 := by
      rw [hA'eq]
      calc GeneralLinearGroup.scalar (Fin 2) ω * (A : GL (Fin 2) F) *
            (GeneralLinearGroup.scalar (Fin 2) ω * A) =
          GeneralLinearGroup.scalar (Fin 2) ω * ((A : GL (Fin 2) F) *
            GeneralLinearGroup.scalar (Fin 2) ω) * A := by simp only [mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin 2) ω * (GeneralLinearGroup.scalar (Fin 2) ω *
            (A : GL (Fin 2) F)) * A := by rw [← scalar_mul_comm ω (A : GL (Fin 2) F)]
        _ = GeneralLinearGroup.scalar (Fin 2) ω * GeneralLinearGroup.scalar (Fin 2) ω *
            ((A : GL (Fin 2) F) * A) := by simp only [mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin 2) (ω * ω * ω) * -1 := by
            rw [hAA, map_mul, map_mul]
            simp only [mul_assoc]
        _ = -1 := by rw [← pow_three', hω3, map_one, one_mul]
    rw [← Units.val_mul, e]
    simp
  set M := ((A' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hM
  have e00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = -1 := by
    have := congrFun (congrFun hsq 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e01 : M 0 0 * M 0 1 + M 0 1 * M 1 1 = 0 := by
    have := congrFun (congrFun hsq 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e10 : M 1 0 * M 0 0 + M 1 1 * M 1 0 = 0 := by
    have := congrFun (congrFun hsq 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 = -1 := by
    have := congrFun (congrFun hsq 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  by_cases htr : M 0 0 + M 1 1 = 0
  ·
    have hdet : GeneralLinearGroup.det (A' : GL (Fin 2) F) = 1 := by
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, ← hM, Matrix.det_fin_two, Units.val_one]
      have h11 : M 1 1 = -M 0 0 := by linear_combination htr
      rw [h11]
      linear_combination -e00
    rw [← hπA']
    exact ⟨A', mem_slPart.mpr hdet, rfl⟩
  ·
    exfalso
    have h01 : M 0 1 = 0 := by
      have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right htr
    have h10 : M 1 0 = 0 := by
      have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right htr
    have h0011 : M 0 0 = M 1 1 := by
      have : (M 0 0 - M 1 1) * (M 0 0 + M 1 1) = 0 := by
        linear_combination e00 - e11
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right htr)
    have h00 : M 0 0 ≠ 0 := by
      intro h0
      rw [h0, h01] at e00
      simp at e00
    set c : Fˣ := Units.mk0 (M 0 0) h00 with hc
    have hA'c : (A' : GL (Fin 2) F) = GeneralLinearGroup.scalar (Fin 2) c := by
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar, ← hM]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hc, h01, h10, h0011]
    apply hns (ω⁻¹ * c)
    rw [map_mul, map_inv, ← hA'c, hA'eq, inv_mul_cancel_left]

theorem blk_eq_scalar {A : GL (Fin 2) F} {c : Fˣ}
    (h : GH74.GLS.IVK.Proofs2.Lemma41aL3.blk A = GeneralLinearGroup.scalar (Fin 3) c) :
    c ^ 3 = 1 ∧ A = GeneralLinearGroup.scalar (Fin 2) c := by
  have hm := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [GH74.GLS.IVK.Proofs2.Lemma41aL3.coe_blk, GeneralLinearGroup.coe_scalar] at hm
  have e := fun i j => congrFun (congrFun hm i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  have e22 := e 2 2
  simp [GH74.GLS.IVK.Proofs2.Lemma41aL3.blkMat, Matrix.scalar_apply] at e00 e01 e10 e11 e22
  have hA : A = GeneralLinearGroup.scalar (Fin 2) c := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11, Matrix.scalar_apply]
  refine ⟨?_, hA⟩
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = (c : F) ^ 2 := by
    rw [Matrix.det_fin_two, e00, e01, e10, e11]
    ring
  rw [hdet] at e22
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  calc (c : F) ^ 3 = (c : F) * (c : F) ^ 2 := by ring
    _ = ((c : F) ^ 2)⁻¹ * (c : F) ^ 2 := by rw [e22]
    _ = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hc0)

end Q5GL2

end CFSG.ClassicalInvolution.Q3.TA3
