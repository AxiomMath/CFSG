module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Basic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {K : Type} [Field K]

section Field4

variable (h : UnitaryFieldData 2 1 K)

include h

theorem u62lb_card_units : Nat.card Kˣ = 3 := by
  haveI := h.finite
  rw [Nat.card_units, h.card]
  norm_num

theorem u62lb_units_pow_three (a : Kˣ) : a ^ 3 = 1 := by
  haveI := h.finite
  rw [← u62lb_card_units h]
  exact pow_card_eq_one'

theorem u62lb_two_eq_zero : (2 : K) = 0 := by
  haveI := h.charP
  exact CharP.cast_eq_zero K 2

theorem u62lb_bar (c : K) : h.bar c = c ^ 2 := by
  rw [UnitaryFieldData.bar_apply]
  norm_num

theorem u62lb_norm_unit (c : Kˣ) : h.norm (c : K) = 1 := by
  rw [UnitaryFieldData.norm, u62lb_bar, ← pow_succ']
  have := congrArg (fun u : Kˣ => (u : K)) (u62lb_units_pow_three h c)
  simpa using this

omit h

end Field4

@[expose] noncomputable def dmat : (Fin 6 → Kˣ) →* GL (Fin 6) K where
  toFun μ :=
    { val := Matrix.diagonal fun i => (μ i : K)
      inv := Matrix.diagonal fun i => ((μ i)⁻¹ : Kˣ)
      val_inv := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        simp
      inv_val := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        simp }
  map_one' := by
    ext1
    simp
  map_mul' μ ν := by
    ext1
    simp [Matrix.diagonal_mul_diagonal]

theorem coe_dmat (μ : Fin 6 → Kˣ) :
    ((dmat μ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal fun i => (μ i : K) :=
  rfl

theorem dmat_comm (μ ν : Fin 6 → Kˣ) : (dmat μ : GL (Fin 6) K) * dmat ν = dmat ν * dmat μ := by
  rw [← map_mul, ← map_mul, mul_comm]

section Unitary

variable (h : UnitaryFieldData 2 1 K)

theorem dmat_mem_primeFormUnitary (μ : Fin 6 → Kˣ) :
    (dmat μ : GL (Fin 6) K) ∈ primeFormUnitary h (idGram K 6) := by
  rw [mem_primeFormUnitary, coe_dmat, diagonal_map (map_zero h.bar), diagonal_transpose]
  change diagonal _ * ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * diagonal _ =
    ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  rw [Units.val_one, Matrix.mul_one, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  have := u62lb_norm_unit h (μ i)
  rw [UnitaryFieldData.norm, mul_comm] at this
  exact this

theorem dmat_mem_gramSU (μ : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1) :
    (dmat μ : GL (Fin 6) K) ∈ gramSU h (idGram K 6) := by
  refine ⟨dmat_mem_primeFormUnitary h μ, ?_⟩
  rw [coe_dmat, det_diagonal, ← Units.coe_prod, hμ, Units.val_one]

@[expose] noncomputable def dmatU (μ : Fin 6 → Kˣ) : primeFormUnitary h (idGram K 6) :=
  ⟨dmat μ, dmat_mem_primeFormUnitary h μ⟩

@[expose] noncomputable def dmatS (μ : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1) :
    gramSU h (idGram K 6) :=
  ⟨dmat μ, dmat_mem_gramSU h μ hμ⟩

@[expose] noncomputable def diagP (μ : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1) :
    primeFormP h (idGram K 6) :=
  (dmatS h μ hμ : primeFormP h (idGram K 6))

theorem mem_normOneScalars_iff (g : gramSU h (idGram K 6)) :
    g ∈ normOneScalars h (gramSU h (idGram K 6)) 6 ↔
      ∃ c : Kˣ, (g : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
  constructor
  · rintro ⟨c, -, -, hc⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, u62lb_norm_unit h c, ?_, hc⟩
    calc c ^ 6 = (c ^ 3) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [u62lb_units_pow_three h, one_pow]

theorem diagP_mem_fixSub (δ μ : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1) :
    diagP h μ hμ ∈ fixSub (primeFormConjHom h (idGram K 6) (dmatU h δ)) := by
  rw [mem_fixSub]
  change primeFormConjHom h (idGram K 6) (dmatU h δ) (dmatS h μ hμ : primeFormP h (idGram K 6)) =
    (dmatS h μ hμ : primeFormP h (idGram K 6))
  rw [primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  change (dmat δ : GL (Fin 6) K) * dmat μ * (dmat δ)⁻¹ = dmat μ
  rw [dmat_comm δ μ, mul_inv_cancel_right]

theorem prod_mul_eq_one {μ ν : Fin 6 → Kˣ} (hμ : ∏ i, μ i = 1) (hν : ∏ i, ν i = 1) :
    ∏ i, (μ * ν) i = 1 := by
  simp only [Pi.mul_apply]
  rw [Finset.prod_mul_distrib, hμ, hν, one_mul]

theorem prod_inv_eq_one {μ : Fin 6 → Kˣ} (hμ : ∏ i, μ i = 1) : ∏ i, (μ⁻¹) i = 1 := by
  simp only [Pi.inv_apply]
  rw [Finset.prod_inv_distrib, hμ, inv_one]

theorem prod_one_eq_one : ∏ i, (1 : Fin 6 → Kˣ) i = 1 := by
  simp

theorem diagP_mul (μ ν : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1) (hν : ∏ i, ν i = 1) :
    diagP h μ hμ * diagP h ν hν = diagP h (μ * ν) (prod_mul_eq_one hμ hν) := by
  unfold diagP
  rw [← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (map_mul dmat μ ν).symm

theorem diagP_one : diagP h (1 : Fin 6 → Kˣ) prod_one_eq_one = 1 := by
  unfold diagP
  rw [← QuotientGroup.mk_one]
  congr 1

theorem diagP_inv (μ : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1) :
    (diagP h μ hμ)⁻¹ = diagP h μ⁻¹ (prod_inv_eq_one hμ) := by
  unfold diagP
  rw [← QuotientGroup.mk_inv]
  congr 1

theorem diagP_eq_one_iff (μ : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1) :
    diagP h μ hμ = 1 ↔ ∃ c : Kˣ, ∀ i, μ i = c := by
  unfold diagP
  rw [QuotientGroup.eq_one_iff, mem_normOneScalars_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun i => ?_⟩
    have := congrArg (fun M : GL (Fin 6) K => (M : Matrix (Fin 6) (Fin 6) K) i i) hc
    simp only [dmatS, coe_dmat, diagonal_apply_eq, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] at this
    exact Units.ext this
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply Units.ext
    change ((dmat μ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = _
    rw [coe_dmat, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    congr 1
    funext i
    rw [hc i]

end Unitary

end CFSG.HardMathSupport.Dickson.Bal207

end
