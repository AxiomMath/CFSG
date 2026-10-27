module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915K2b
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915K2d
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Matrix CFSG.LocalAnalysis.ComponentInitial Subgroup
open scoped commutatorElement

section Mats

variable {F : Type} [Field F]

@[expose] def blockM (A : GL (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![(A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
     (A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1, 0;
     0, 0, (((Matrix.GeneralLinearGroup.det A)⁻¹ : Fˣ) : F)]

theorem det_blockM (A : GL (Fin 2) F) : (blockM A).det = 1 := by
  have h1 : ((Matrix.GeneralLinearGroup.det A : Fˣ) : F) = (A : Matrix (Fin 2) (Fin 2) F).det :=
    Matrix.GeneralLinearGroup.val_det_apply A
  have h3 : (((Matrix.GeneralLinearGroup.det A)⁻¹ : Fˣ) : F) =
      ((A : Matrix (Fin 2) (Fin 2) F).det)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, h1]
  have hd : (A : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← h1]; exact Units.ne_zero _
  rw [blockM, Matrix.det_fin_three, h3, Matrix.det_fin_two] at *
  simp
  field_simp

theorem blockM_mul (A B : GL (Fin 2) F) : blockM (A * B) = blockM A * blockM B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockM, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, mul_comm]

@[expose] def betaSL : GL (Fin 2) F →* SpecialLinearGroup (Fin 3) F where
  toFun A := ⟨blockM A, det_blockM A⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockM]
  map_mul' A B := Subtype.ext (blockM_mul A B)

theorem coe_betaSL (A : GL (Fin 2) F) :
    ((betaSL A : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blockM A := rfl

@[expose] def cyc : SpecialLinearGroup (Fin 3) F :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

@[expose] def t3 : SpecialLinearGroup (Fin 3) F := betaSL (-1)

theorem det_neg_one_two' : ((-1 : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
  rw [Matrix.det_neg, Matrix.det_one]; simp

theorem coe_t3 : ((t3 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t3, coe_betaSL, blockM, det_neg_one_two']

@[expose] def t1 : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

@[expose] def t2 : SpecialLinearGroup (Fin 3) F :=
  ⟨!![-1, 0, 0; 0, 1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

theorem cyc_mul_t3 : (cyc : SpecialLinearGroup (Fin 3) F) * t3 = t1 * cyc := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_t3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc, t1, Matrix.mul_apply, Fin.sum_univ_three]

theorem cyc_mul_t1 : (cyc : SpecialLinearGroup (Fin 3) F) * t1 = t2 * cyc := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc, t1, t2, Matrix.mul_apply, Fin.sum_univ_three]

theorem t1_mul_t2 : (t1 : SpecialLinearGroup (Fin 3) F) * t2 = t3 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_t3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t1, t2, Matrix.mul_apply, Fin.sum_univ_three]

theorem t2_mul_t1 : (t2 : SpecialLinearGroup (Fin 3) F) * t1 = t3 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_t3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t1, t2, Matrix.mul_apply, Fin.sum_univ_three]

theorem t1_mul_t1 : (t1 : SpecialLinearGroup (Fin 3) F) * t1 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t1, Matrix.mul_apply, Fin.sum_univ_three]

theorem t2_mul_t2 : (t2 : SpecialLinearGroup (Fin 3) F) * t2 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t2, Matrix.mul_apply, Fin.sum_univ_three]

theorem not_mem_scalars_of_entries {A : SpecialLinearGroup (Fin 3) F} {i j : Fin 3}
    (hij : (A : Matrix (Fin 3) (Fin 3) F) i i ≠ (A : Matrix (Fin 3) (Fin 3) F) j j) :
    A ∉ LinearFlag.scalars 3 F := by
  rintro ⟨c, -, hc⟩
  apply hij
  have h1 := congrFun (congrFun hc i) i
  have h2' := congrFun (congrFun hc j) j
  rw [h1, h2']
  simp

theorem t1_not_mem_scalars (h2 : (2 : F) ≠ 0) :
    (t1 : SpecialLinearGroup (Fin 3) F) ∉ LinearFlag.scalars 3 F :=
  not_mem_scalars_of_entries (i := 0) (j := 1) (by
    simp only [t1]
    simp
    intro h
    apply h2
    linear_combination h)

theorem t2_not_mem_scalars (h2 : (2 : F) ≠ 0) :
    (t2 : SpecialLinearGroup (Fin 3) F) ∉ LinearFlag.scalars 3 F :=
  not_mem_scalars_of_entries (i := 0) (j := 1) (by
    simp only [t2]
    simp
    intro h
    apply h2
    linear_combination -h)

theorem t3_not_mem_scalars (h2 : (2 : F) ≠ 0) :
    (t3 : SpecialLinearGroup (Fin 3) F) ∉ LinearFlag.scalars 3 F :=
  not_mem_scalars_of_entries (i := 0) (j := 2) (by
    rw [coe_t3]
    simp
    intro h
    apply h2
    linear_combination -h)

theorem cyc_conj_t3 : (cyc : SpecialLinearGroup (Fin 3) F) * t3 * cyc⁻¹ = t1 := by
  rw [cyc_mul_t3]; group

theorem cyc_conj_t1 : (cyc : SpecialLinearGroup (Fin 3) F) * t1 * cyc⁻¹ = t2 := by
  rw [cyc_mul_t1]; group

theorem cyc_sq_conj_t3 :
    (cyc * cyc : SpecialLinearGroup (Fin 3) F) * t3 * (cyc * cyc)⁻¹ = t2 := by
  have : (cyc * cyc : SpecialLinearGroup (Fin 3) F) * t3 * (cyc * cyc)⁻¹ =
      cyc * (cyc * t3 * cyc⁻¹) * cyc⁻¹ := by group
  rw [this, cyc_conj_t3, cyc_conj_t1]

end Mats

section Assembly

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F]

theorem two_ne_zero_of_odd_card' (hF : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro h
    have he := FiniteField.even_card_of_char_two h
    have ho : Fintype.card F % 2 = 1 := by
      simpa only [← Nat.card_eq_fintype_card] using Nat.odd_iff.mp hF
    omega
  intro hzero
  exact hchar (CharP.ringChar_of_prime_eq_zero Nat.prime_two hzero)

theorem l3_mem_derived2 (hZ : Odd (Nat.card ↥(center X))) (hF : Odd (Nat.card F))
    (ι : (X ⧸ center X) ≃* LinearFlag.projectiveSL 3 F) {x : X} (hx : x * x = 1)
    (g : X ⧸ center X)
    (hg : g * ι.symm (LinearFlag.proj 3 F t3) * g⁻¹ = QuotientGroup.mk x) :
    x ∈ ⁅⁅centralizer ({x} : Set X), centralizer ({x} : Set X)⁆,
      ⁅centralizer ({x} : Set X), centralizer ({x} : Set X)⁆⁆ := by
  have h2 := two_ne_zero_of_odd_card' hF
  obtain ⟨σ, hσ, hD⟩ := exists_sigma_D2 F h2
  let Φ : ↥(D2 F) →* X ⧸ center X :=
    (MulAut.conj g).toMonoidHom.comp (ι.symm.toMonoidHom.comp
      ((LinearFlag.proj 3 F).comp (betaSL.comp (D2 F).subtype)))
  refine mem_derived2_centralizer_of_hom hZ Φ (c := ⟨-1, negOne_mem_D2 F⟩) hσ hD
    (negOne_mem_derived_D2 F hF) ?_ hx ?_
  · intro d
    apply Subtype.ext
    simp [mul_neg, neg_mul]
  · show g * ι.symm (LinearFlag.proj 3 F (betaSL (-1 : GL (Fin 2) F))) * g⁻¹ = _
    exact hg

theorem l3_facts (hZ : Odd (Nat.card ↥(center X))) (hF : Odd (Nat.card F))
    (ι : (X ⧸ center X) ≃* LinearFlag.projectiveSL 3 F) :
    ∃ x₁ x₂ : X, x₁ * x₁ = 1 ∧ x₂ * x₂ = 1 ∧ x₁ * x₂ = x₂ * x₁ ∧ x₁ ≠ x₂ ∧ x₁ ≠ 1 ∧ x₂ ≠ 1 ∧
      x₁ ∈ ⁅⁅centralizer ({x₁} : Set X), centralizer ({x₁} : Set X)⁆,
        ⁅centralizer ({x₁} : Set X), centralizer ({x₁} : Set X)⁆⁆ ∧
      x₂ ∈ ⁅⁅centralizer ({x₂} : Set X), centralizer ({x₂} : Set X)⁆,
        ⁅centralizer ({x₂} : Set X), centralizer ({x₂} : Set X)⁆⁆ ∧
      x₁ * x₂ ∈ ⁅⁅centralizer ({x₁ * x₂} : Set X), centralizer ({x₁ * x₂} : Set X)⁆,
        ⁅centralizer ({x₁ * x₂} : Set X), centralizer ({x₁ * x₂} : Set X)⁆⁆ := by
  have h2 := two_ne_zero_of_odd_card' hF
  have hy : ∀ t : SpecialLinearGroup (Fin 3) F, t * t = 1 →
      (ι.symm ((LinearFlag.proj 3 F) t)) * (ι.symm ((LinearFlag.proj 3 F) t)) = 1 := fun t ht => by
    rw [← map_mul, ← map_mul, ht, map_one, map_one]
  obtain ⟨x₁, hx₁, hx₁y⟩ := exists_involution_lift hZ (hy t1 t1_mul_t1)
  obtain ⟨x₂, hx₂, hx₂y⟩ := exists_involution_lift hZ (hy t2 t2_mul_t2)
  have hy12 : (QuotientGroup.mk x₁ : X ⧸ center X) * QuotientGroup.mk x₂ = ι.symm ((LinearFlag.proj 3 F) t3) := by
    rw [hx₁y, hx₂y, ← map_mul, ← map_mul, t1_mul_t2]
  have hy21 : (QuotientGroup.mk x₂ : X ⧸ center X) * QuotientGroup.mk x₁ = ι.symm ((LinearFlag.proj 3 F) t3) := by
    rw [hx₁y, hx₂y, ← map_mul, ← map_mul, t2_mul_t1]
  have hcomm : x₁ * x₂ = x₂ * x₁ := by
    have hconj : (x₁ * x₂ * x₁⁻¹) * (x₁ * x₂ * x₁⁻¹) = 1 := by
      calc (x₁ * x₂ * x₁⁻¹) * (x₁ * x₂ * x₁⁻¹) = x₁ * (x₂ * x₂) * x₁⁻¹ := by group
        _ = 1 := by rw [hx₂]; group
    have hmk : (QuotientGroup.mk (x₁ * x₂ * x₁⁻¹) : X ⧸ center X) = QuotientGroup.mk x₂ := by
      have h1 : (QuotientGroup.mk x₁ : X ⧸ center X) * QuotientGroup.mk x₂ =
          QuotientGroup.mk x₂ * QuotientGroup.mk x₁ := hy12.trans hy21.symm
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1]
      group
    have := involution_lift_unique hZ hconj hx₂ hmk
    calc x₁ * x₂ = (x₁ * x₂ * x₁⁻¹) * x₁ := by group
      _ = x₂ * x₁ := by rw [this]
  have hne : x₁ ≠ x₂ := by
    intro h
    have hh : ι.symm ((LinearFlag.proj 3 F) t1) = ι.symm ((LinearFlag.proj 3 F) t2) := by rw [← hx₁y, ← hx₂y, h]
    have := ι.symm.injective hh
    have h3 := LinearFlag.proj_eq_proj_iff.mp this
    rw [inv_eq_of_mul_eq_one_right t1_mul_t1, t1_mul_t2] at h3
    exact t3_not_mem_scalars h2 h3
  have hne1 : x₁ ≠ 1 := by
    intro h
    have hh : ι.symm ((LinearFlag.proj 3 F) t1) = 1 := by rw [← hx₁y, h]; rfl
    have := ι.symm.injective (hh.trans (map_one ι.symm).symm)
    exact t1_not_mem_scalars h2 (LinearFlag.proj_eq_one_iff.mp this)
  have hne2 : x₂ ≠ 1 := by
    intro h
    have hh : ι.symm ((LinearFlag.proj 3 F) t2) = 1 := by rw [← hx₂y, h]; rfl
    have := ι.symm.injective (hh.trans (map_one ι.symm).symm)
    exact t2_not_mem_scalars h2 (LinearFlag.proj_eq_one_iff.mp this)
  have hx12 : (x₁ * x₂) * (x₁ * x₂) = 1 := by
    calc (x₁ * x₂) * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
      _ = x₁ * (x₁ * x₂) * x₂ := by rw [← hcomm]
      _ = (x₁ * x₁) * (x₂ * x₂) := by group
      _ = 1 := by rw [hx₁, hx₂, one_mul]
  have hconj : ∀ a b : SpecialLinearGroup (Fin 3) F,
      ι.symm ((LinearFlag.proj 3 F) a) * ι.symm ((LinearFlag.proj 3 F) b) *
        (ι.symm ((LinearFlag.proj 3 F) a))⁻¹ = ι.symm ((LinearFlag.proj 3 F) (a * b * a⁻¹)) :=
    fun a b => by simp [map_mul, map_inv]
  refine ⟨x₁, x₂, hx₁, hx₂, hcomm, hne, hne1, hne2, ?_, ?_, ?_⟩
  · refine l3_mem_derived2 hZ hF ι hx₁ (ι.symm ((LinearFlag.proj 3 F) cyc)) ?_
    rw [hx₁y, hconj, cyc_conj_t3]
  · refine l3_mem_derived2 hZ hF ι hx₂ (ι.symm ((LinearFlag.proj 3 F) (cyc * cyc))) ?_
    rw [hx₂y, hconj, cyc_sq_conj_t3]
  · refine l3_mem_derived2 hZ hF ι hx12 1 ?_
    rw [one_mul, inv_one, mul_one, QuotientGroup.mk_mul, hy12]

end Assembly

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
