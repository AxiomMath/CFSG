module

public import CFSG.GH74.Generic.S1.RUniAct

public section

namespace CFSG.GH74.Generic.S1.Uni

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F]

theorem uni_center_pow_four (h : UnitaryFieldData p f F)
    {z : ↥(StatedSU 4 (p ^ f) F)} (hz : ∀ k : ↥(StatedSU 4 (p ^ f) F), z * k = k * z) :
    z ^ 4 = 1 := by
  classical
  have hfin : Finite F := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hF : Nat.card F = (p ^ f) ^ 2 := h.card_eq_sq
  obtain ⟨hqs, hcenter⟩ :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := F) (p := p) (f := f)
      (n := 4) hF (by norm_num) (fun h => by simp at h)
  have hZ : unitaryScalars h 4 = Subgroup.center ↥(StatedSU 4 (p ^ f) F) :=
    (unitaryScalars_eq h (by norm_num)).trans hcenter.symm
  have hzc : z ∈ Subgroup.center ↥(StatedSU 4 (p ^ f) F) :=
    Subgroup.mem_center_iff.2 fun k => (hz k).symm
  rw [← hZ] at hzc
  obtain ⟨c, -, hc4, hzc'⟩ := mem_unitaryScalars.1 hzc
  apply Subtype.ext
  rw [Subgroup.coe_pow, hzc', ← map_pow, hc4, map_one]
  rfl


theorem rdet_scalar_conj (u : Fˣ) (g k : GL (Fin 4) F) :
    (Matrix.GeneralLinearGroup.scalar (Fin 4) u * g) * k *
      (Matrix.GeneralLinearGroup.scalar (Fin 4) u * g)⁻¹ = g * k * g⁻¹ := by
  have hcc : ∀ x : GL (Fin 4) F, Matrix.GeneralLinearGroup.scalar (Fin 4) u * x =
      x * Matrix.GeneralLinearGroup.scalar (Fin 4) u := fun x => by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.diagonal_mul, Matrix.mul_diagonal,
      mul_comm]
  calc (Matrix.GeneralLinearGroup.scalar (Fin 4) u * g) * k *
        (Matrix.GeneralLinearGroup.scalar (Fin 4) u * g)⁻¹
      = Matrix.GeneralLinearGroup.scalar (Fin 4) u * (g * k * g⁻¹) *
        (Matrix.GeneralLinearGroup.scalar (Fin 4) u)⁻¹ := by
        simp only [_root_.mul_inv_rev, mul_assoc]
    _ = g * k * g⁻¹ := by
      rw [hcc (g * k * g⁻¹), mul_assoc, mul_inv_cancel, mul_one]

theorem uni_det_inner (h : UnitaryFieldData p f F) (hq4 : p ^ f % 4 = 1) {N : GL (Fin 4) F}
    (hN : ((N : Matrix (Fin 4) (Fin 4) F).map h.bar)ᵀ * (N : Matrix (Fin 4) (Fin 4) F) = 1)
    (hd : (N : Matrix (Fin 4) (Fin 4) F).det ^ ((p ^ f + 1) / 2) = 1) :
    ∃ s : ↥(StatedSU 4 (p ^ f) F), ∀ k : ↥(StatedSU 4 (p ^ f) F),
      N * (k : GL (Fin 4) F) * N⁻¹ =
        (s : GL (Fin 4) F) * (k : GL (Fin 4) F) * (s : GL (Fin 4) F)⁻¹ := by
  classical
  have hfin : Finite F := h.finite
  have hq1 : 1 < p ^ f := by
    have h1 := h.prime.one_lt
    have h2 := h.one_le
    calc 1 < p := h1
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) h2
  set q := p ^ f with hq
  set m := (q + 1) / 2 with hm
  have hqm : q + 1 = 2 * m := by omega
  have hmodd : m % 2 = 1 := by omega
  have hm2 : 1 < m := by omega
  set δ : F := (N : Matrix (Fin 4) (Fin 4) F).det with hδ
  have hδ0 : δ ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 N.isUnit).ne_zero
  have hbar : h.bar δ * δ = 1 := by
    have h1 := congrArg Matrix.det hN
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    have h2 : ((N : Matrix (Fin 4) (Fin 4) F).map h.bar).det = h.bar δ := by
      rw [hδ, RingHom.map_det, RingHom.mapMatrix_apply]
    rw [h2] at h1
    exact h1
  have hδq : δ ^ (q + 1) = 1 := by
    rw [pow_succ, ← UnitaryFieldData.bar_apply]
    exact hbar
  have hcop : Nat.Coprime 4 m := by
    have : Nat.Coprime 2 m := Nat.coprime_two_left.2 (Nat.odd_iff.2 hmodd)
    simpa using this.pow_left 2
  obtain ⟨k0, -, hk0⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hm2
  set ν : F := δ ^ k0 with hν
  have hν0 : ν ≠ 0 := pow_ne_zero _ hδ0
  have hν4 : ν ^ 4 = δ := by
    have h1 : 4 * k0 = 1 + m * (4 * k0 / m) := by
      have := Nat.div_add_mod (4 * k0) m
      rw [hk0] at this
      omega
    rw [hν, ← pow_mul, mul_comm k0 4, h1, pow_add, pow_mul, hd, one_pow, mul_one, pow_one]
  have hνq : ν ^ (q + 1) = 1 := by
    have : ν ^ m = 1 := by rw [hν, ← pow_mul, mul_comm, pow_mul, hd, one_pow]
    rw [hqm, pow_mul', this, one_pow]
  have hν0' : ν⁻¹ ≠ 0 := inv_ne_zero hν0
  let c : GL (Fin 4) F := Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 ν hν0)
  let sGL : GL (Fin 4) F :=
    Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 ν⁻¹ hν0') * N
  have hsval : (sGL : Matrix (Fin 4) (Fin 4) F) = ν⁻¹ • (N : Matrix (Fin 4) (Fin 4) F) := by
    simp only [sGL, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    rw [Matrix.smul_eq_diagonal_mul]
    rfl
  have hsmem : sGL ∈ StatedSU 4 (p ^ f) F := by
    rw [rmem_statedSU h, hsval]
    refine ⟨?_, ?_⟩
    · rw [Matrix.det_smul, Fintype.card_fin, ← hδ, inv_pow, hν4]
      exact inv_mul_cancel₀ hδ0
    · have h1 : ((ν⁻¹ • (N : Matrix (Fin 4) (Fin 4) F)).map h.bar) =
          (h.bar ν⁻¹) • (N : Matrix (Fin 4) (Fin 4) F).map h.bar := by
        ext i j
        simp
      rw [h1, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hN]
      have h2 : h.bar ν⁻¹ * ν⁻¹ = 1 := by
        rw [map_inv₀, UnitaryFieldData.bar_apply, ← mul_inv, ← pow_succ, hνq, inv_one]
      rw [h2, one_smul]
  refine ⟨⟨sGL, hsmem⟩, fun k => ?_⟩
  have hN' : N = c * sGL := by
    have hu : Units.mk0 ν hν0 * Units.mk0 ν⁻¹ hν0' = 1 := by
      apply Units.ext
      simp [hν0]
    simp only [sGL, c]
    rw [← mul_assoc, ← map_mul, hu, map_one, one_mul]
  calc N * (k : GL (Fin 4) F) * N⁻¹ = (c * sGL) * (k : GL (Fin 4) F) * (c * sGL)⁻¹ := by
        rw [← hN']
    _ = sGL * (k : GL (Fin 4) F) * sGL⁻¹ := rdet_scalar_conj _ sGL k

end CFSG.GH74.Generic.S1.Uni
