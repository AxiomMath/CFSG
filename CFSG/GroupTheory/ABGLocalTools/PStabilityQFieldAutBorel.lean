module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityQBorel
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

open Subgroup Matrix

namespace CFSG.ABGLocalTools

open SL2Facts

variable {F : Type*} [Field F]

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) F

theorem mulVec_single_zero (P : SL2) :
    (P : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = ![P 0 0, P 1 0] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem inv_mulVec_first_column (P : SL2) :
    ((P⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) F) *ᵥ ![P 0 0, P 1 0] = ![1, 0] := by
  rw [← mulVec_single_zero, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem mem_map_conj_borelSL2_iff (P : SL2) (b : SL2) :
    b ∈ (borelSL2 F).map (MulAut.conj P).toMonoidHom ↔
      ∃ c : F, (b : Matrix (Fin 2) (Fin 2) F) *ᵥ ![P 0 0, P 1 0] = c • ![P 0 0, P 1 0] := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    have hA10 : A 1 0 = 0 := hA
    refine ⟨A 0 0, ?_⟩
    change ((P * A * P⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) F) *ᵥ _ = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, inv_mulVec_first_column, ← Matrix.mulVec_mulVec]
    have hAe : (A : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = A 0 0 • ![1, 0] := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hA10]
    rw [hAe, Matrix.mulVec_smul, mulVec_single_zero]
  · rintro ⟨c, hc⟩
    obtain ⟨h10, -⟩ := inv_mul_mul_apply_of_eigenvector hc
    refine ⟨P⁻¹ * b * P, h10, ?_⟩
    change P * (P⁻¹ * b * P) * P⁻¹ = b
    group

theorem uT_map (σ : F ≃+* F) (t : F) :
    ((uT t : SL2) : Matrix (Fin 2) (Fin 2) F).map σ =
      ((uT (σ t) : SL2) : Matrix (Fin 2) (Fin 2) F) := by
  rw [coe_uT, coe_uT]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable [Finite F]

theorem exists_borel_of_semilinear_eigenvector (hodd : Odd (Nat.card F)) {p : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) (hpq : ¬ p ∣ Nat.card F)
    (α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) (σ : F ≃+* F) (hσ : σ ≠ 1)
    (G : GL (Fin 2) F)
    (hαG : ∀ b : Matrix.SpecialLinearGroup (Fin 2) F, ∃ u : F, u ≠ 0 ∧
      ((α b : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        u • ((G : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F).map σ *
          ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)))
    {v : Fin 2 → F} (hv : v ≠ 0) {μ : F}
    (hGv : (G : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => σ (v i)) = μ • v) :
    ∃ B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F), B.map α.toMonoidHom = B ∧
      TwoSubgroupsCyclic B ∧ CFSG.pCore p B = ⊥ ∧ ∃ b ∈ B, α b ≠ b := by
  classical
  set Gm : Matrix (Fin 2) (Fin 2) F := (G : Matrix (Fin 2) (Fin 2) F) with hGm
  set Gi : Matrix (Fin 2) (Fin 2) F := ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    with hGi
  have hGGi : Gm * Gi = 1 := by rw [hGm, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * Gm = 1 := by rw [hGm, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let σv : Fin 2 → F := fun i => σ (v i)
  have hGv' : Gm *ᵥ σv = μ • v := hGv
  have hμ : μ ≠ 0 := by
    rintro rfl
    apply hv
    have h0 : σv = 0 := by
      have : Gi *ᵥ (Gm *ᵥ σv) = σv := by
        rw [Matrix.mulVec_mulVec, hGiG, Matrix.one_mulVec]
      rw [← this, hGv, zero_smul, Matrix.mulVec_zero]
    ext i
    have := congrFun h0 i
    simpa [σv] using this
  have hGiv : Gi *ᵥ v = μ⁻¹ • σv := by
    have : Gi *ᵥ (Gm *ᵥ σv) = σv := by rw [Matrix.mulVec_mulVec, hGiG, Matrix.one_mulVec]
    rw [hGv, Matrix.mulVec_smul] at this
    rw [← this, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hmap_mul : ∀ M N : Matrix (Fin 2) (Fin 2) F, (M * N).map σ = M.map σ * N.map σ :=
    fun M N => Matrix.map_mul (f := (σ : F →+* F))
  have hσmv : ∀ (M : Matrix (Fin 2) (Fin 2) F) (w : Fin 2 → F),
      M.map σ *ᵥ (fun i => σ (w i)) = fun i => σ ((M *ᵥ w) i) := by
    intro M w
    ext i
    exact ((σ : F →+* F).map_mulVec M w i).symm
  obtain ⟨P, hP0, hP1⟩ := exists_sl2_first_column hv
  have hvP : v = ![P 0 0, P 1 0] := by
    ext i; fin_cases i <;> simp [hP0, hP1]
  set B := (borelSL2 F).map (MulAut.conj P).toMonoidHom with hB
  have hmem : ∀ b : SL2, b ∈ B ↔ ∃ c : F, (b : Matrix (Fin 2) (Fin 2) F) *ᵥ v = c • v := by
    intro b
    rw [hvP]
    exact mem_map_conj_borelSL2_iff P b
  have hle : B.map α.toMonoidHom ≤ B := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc⟩ := (hmem b).mp hb
    obtain ⟨u, -, hu⟩ := hαG b
    rw [hmem]
    refine ⟨u * σ c, ?_⟩
    change ((α b : SL2) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = _
    rw [hu, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGiv,
      Matrix.mulVec_smul, hσmv, hc]
    have : (fun i => σ ((c • v) i)) = σ c • σv := by
      ext i; simp [σv]
    rw [this]
    simp only [Matrix.mulVec_smul, smul_smul]
    rw [hGv', smul_smul]
    congr 1
    field_simp
  have hBα : B.map α.toMonoidHom = B := by
    apply Subgroup.eq_of_le_of_card_ge hle
    exact (Subgroup.card_map_of_injective (K := B) (f := α.toMonoidHom) α.injective).symm.le
  refine ⟨B, hBα, (twoSubgroupsCyclic_borelSL2 hodd).map_mulAut _,
    pCore_map_mulAut_eq_bot (pCore_borelSL2_eq_bot hp hpq) _, ?_⟩
  by_contra hfix
  push Not at hfix
  apply hσ
  set Pm : Matrix (Fin 2) (Fin 2) F := (P : Matrix (Fin 2) (Fin 2) F) with hPm
  set Pi : Matrix (Fin 2) (Fin 2) F := ((P⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) F) with hPi
  set Q : Matrix (Fin 2) (Fin 2) F := Pi * Gm * Pm.map σ with hQ
  have hPiP : Pi * Pm = 1 := by
    rw [hPi, hPm, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hPPi : Pm * Pi = 1 := by
    rw [hPi, hPm, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hσPPi : Pi.map σ * Pm.map σ = 1 := by
    rw [← hmap_mul, hPiP, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hQe : Q *ᵥ ![1, 0] = μ • ![1, 0] := by
    have h1 : Pm.map σ *ᵥ ![1, 0] = σv := by
      have := hσmv Pm ![1, 0]
      have h2 : (fun i => σ (![(1 : F), 0] i)) = ![1, 0] := by
        ext i; fin_cases i <;> simp
      rw [h2] at this
      rw [this, hPm, mulVec_single_zero, ← hvP]
    rw [hQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, hGv, Matrix.mulVec_smul, hvP,
      hPi, inv_mulVec_first_column]
  have hQ10 : Q 1 0 = 0 := by
    have := congrFun hQe 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hQ00 : Q 0 0 = μ := by
    have := congrFun hQe 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hrel : ∀ t : F, (uT t : Matrix (Fin 2) (Fin 2) F) * Q =
      Q * (uT (σ t) : Matrix (Fin 2) (Fin 2) F) := by
    intro t
    have hbt : MulAut.conj P (uT t) ∈ B := ⟨uT t, uT_mem_borelSL2 t, rfl⟩
    have hαb := hfix _ hbt
    obtain ⟨u, hu0, hu⟩ := hαG (MulAut.conj P (uT t))
    rw [hαb] at hu
    have hconj : ((MulAut.conj P (uT t) : SL2) : Matrix (Fin 2) (Fin 2) F) =
        Pm * (uT t : Matrix (Fin 2) (Fin 2) F) * Pi := by
      rw [MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    have hσu := uT_map σ t
    rw [hconj, hmap_mul, hmap_mul] at hu
    change Pm * (uT t : Matrix (Fin 2) (Fin 2) F) * Pi =
      u • (Gm * (Pm.map σ * (uT t : Matrix (Fin 2) (Fin 2) F).map σ * Pi.map σ) * Gi) at hu
    rw [hσu] at hu
    have key : (uT t : Matrix (Fin 2) (Fin 2) F) * Q =
        u • (Q * (uT (σ t) : Matrix (Fin 2) (Fin 2) F)) := by
      have := congrArg (fun M => Pi * M * (Gm * Pm.map σ)) hu
      calc (uT t : Matrix (Fin 2) (Fin 2) F) * Q
          = Pi * (Pm * (uT t : Matrix (Fin 2) (Fin 2) F) * Pi) * (Gm * Pm.map σ) := by
            rw [hQ]
            simp only [← Matrix.mul_assoc]
            rw [hPiP, Matrix.one_mul]
        _ = Pi * (u • (Gm * (Pm.map σ * (uT (σ t) : Matrix (Fin 2) (Fin 2) F) * Pi.map σ) * Gi)) *
            (Gm * Pm.map σ) := this
        _ = u • (Q * (uT (σ t) : Matrix (Fin 2) (Fin 2) F)) := by
            rw [Matrix.mul_smul, Matrix.smul_mul, hQ]
            congr 1
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Gi Gm, hGiG, Matrix.one_mul, hσPPi, Matrix.mul_one]
    have h00 := congrFun (congrFun key 0) 0
    simp [coe_uT, Matrix.mul_apply, Fin.sum_univ_two, hQ10, hQ00] at h00
    have hu1 : u = 1 := by
      have : (u - 1) * μ = 0 := by linear_combination -h00
      rcases mul_eq_zero.mp this with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hμ
    rw [key, hu1, one_smul]
  have h01 : ∀ t : F, t * Q 1 1 = μ * σ t := by
    intro t
    have := congrFun (congrFun (hrel t) 0) 1
    simp [coe_uT, Matrix.mul_apply, Fin.sum_univ_two, hQ00] at this
    linear_combination this
  have hQ11 : Q 1 1 = μ := by
    have := h01 1
    simpa using this
  ext t
  have := h01 t
  rw [hQ11] at this
  show σ t = t
  have : μ * (σ t - t) = 0 := by linear_combination this.symm
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hμ
  · exact (sub_eq_zero.mp h)

end CFSG.ABGLocalTools
