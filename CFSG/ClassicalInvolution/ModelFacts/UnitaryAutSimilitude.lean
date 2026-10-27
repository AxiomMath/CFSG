module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarCommutantSpace
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismRealization

public section

namespace CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan

variable {p f : ℕ} {K : Type} [Field K]

theorem glAut_mem_unitarySU (h : UnitaryFieldData p f K) (φ : K ≃+* K) {d : ℕ}
    {y : GL (Fin d) K} (hy : y ∈ unitarySU p f K d) : glAut φ y ∈ unitarySU p f K d := by
  rw [mem_unitarySU_iff h] at hy ⊢
  obtain ⟨hdet, hu⟩ := hy
  refine ⟨?_, ?_⟩
  · rw [coe_glAut, show (y : Matrix (Fin d) (Fin d) K).map φ =
      (φ : K →+* K).mapMatrix (y : Matrix (Fin d) (Fin d) K) from rfl, ← RingHom.map_det, hdet,
      map_one]
  · rw [coe_glAut, map_bar_map_comm, ← transpose_map, ← map_mul_ringEquiv, hu,
      map_one_ringEquiv]

theorem conj_mem_unitarySU_of (h : UnitaryFieldData p f K) {d : ℕ} (g : GL (Fin d) K)
    (φ : K ≃+* K)
    (hg : ∀ x : unitarySU p f K d, g * glAut φ (x : GL (Fin d) K) * g⁻¹ ∈ unitarySU p f K d)
    {y : GL (Fin d) K} (hy : y ∈ unitarySU p f K d) : g * y * g⁻¹ ∈ unitarySU p f K d := by
  have h1 := hg ⟨glAut φ.symm y, glAut_mem_unitarySU h φ.symm hy⟩
  have h2 : glAut φ (glAut φ.symm y) = y := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    simp [coe_glAut]
  simpa [h2] using h1

theorem conjTranspose_mul_commute_aux (h : UnitaryFieldData p f K) {d : ℕ}
    (G Gi Y : Matrix (Fin d) (Fin d) K) (hGiG : Gi * G = 1)
    (hY : (Y.map h.bar)ᵀ * Y = 1)
    (hmain : ((G * Y * Gi).map h.bar)ᵀ * (G * Y * Gi) = 1) :
    (G.map h.bar)ᵀ * G * Y = Y * ((G.map h.bar)ᵀ * G) := by
  have hstar : (G.map h.bar)ᵀ * (Gi.map h.bar)ᵀ = 1 := by
    rw [← transpose_mul, ← Matrix.map_mul, hGiG, Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
      transpose_one]
  have hYY : Y * (Y.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hY
  have h3 := conjTranspose_mul_mul h (1 : Matrix (Fin d) (Fin d) K) (G * Y) Gi
  have h4 := conjTranspose_mul_mul h (1 : Matrix (Fin d) (Fin d) K) G Y
  simp only [Matrix.mul_one] at h3 h4
  rw [h4] at h3
  rw [h3] at hmain
  have key : (Y.map h.bar)ᵀ * ((G.map h.bar)ᵀ * G) * Y = (G.map h.bar)ᵀ * G := by
    calc (Y.map h.bar)ᵀ * ((G.map h.bar)ᵀ * G) * Y
        = ((G.map h.bar)ᵀ * (Gi.map h.bar)ᵀ) *
            ((Y.map h.bar)ᵀ * ((G.map h.bar)ᵀ * G) * Y) * (Gi * G) := by
          rw [hstar, hGiG, Matrix.one_mul, Matrix.mul_one]
      _ = (G.map h.bar)ᵀ * ((Gi.map h.bar)ᵀ * ((Y.map h.bar)ᵀ * ((G.map h.bar)ᵀ * G) * Y) * Gi) *
            G := by simp only [Matrix.mul_assoc]
      _ = (G.map h.bar)ᵀ * G := by rw [hmain, Matrix.mul_one]
  calc (G.map h.bar)ᵀ * G * Y
      = (Y * (Y.map h.bar)ᵀ) * ((G.map h.bar)ᵀ * G) * Y := by rw [hYY, Matrix.one_mul]
    _ = Y * ((Y.map h.bar)ᵀ * ((G.map h.bar)ᵀ * G) * Y) := by simp only [Matrix.mul_assoc]
    _ = Y * ((G.map h.bar)ᵀ * G) := by rw [key]

theorem conjTranspose_mul_commute (h : UnitaryFieldData p f K) {d : ℕ} (g : GL (Fin d) K)
    {y : GL (Fin d) K} (hy : y ∈ unitarySU p f K d) (hgy : g * y * g⁻¹ ∈ unitarySU p f K d) :
    ((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (g : Matrix (Fin d) (Fin d) K) *
        (y : Matrix (Fin d) (Fin d) K) =
      (y : Matrix (Fin d) (Fin d) K) *
        (((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (g : Matrix (Fin d) (Fin d) K)) := by
  rw [mem_unitarySU_iff h] at hy hgy
  refine conjTranspose_mul_commute_aux h (g : Matrix (Fin d) (Fin d) K)
    ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (y : Matrix (Fin d) (Fin d) K)
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hy.2 ?_
  have := hgy.2
  rwa [Units.val_mul, Units.val_mul] at this

theorem eq_smul_one_of_commute (h : UnitaryFieldData p f K) (hp : p ≠ 2) {d : ℕ} (hd : 3 ≤ d)
    (B : Matrix (Fin d) (Fin d) K)
    (hB : ∀ y : GL (Fin d) K, y ∈ unitarySU p f K d →
      B * (y : Matrix (Fin d) (Fin d) K) = (y : Matrix (Fin d) (Fin d) K) * B) :
    ∃ a : K, B = a • 1 := by
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h3 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    have h4 := Nat.le_of_dvd two_pos ((CharP.cast_eq_zero_iff K p 2).mp h3)
    have := h.prime.two_le
    omega
  obtain ⟨c, hcN, hck⟩ := exists_norm_one_not_fixed h hp
  have hcomm : ∀ M : GL (Fin d) K, M ∈ gramSU h (1 : Matrix (Fin d) (Fin d) K) → ∀ u,
      ((Matrix.mulVecLin B).restrictScalars h.fixedField)
        ((M : Matrix (Fin d) (Fin d) K) *ᵥ u) =
      (M : Matrix (Fin d) (Fin d) K) *ᵥ
        ((Matrix.mulVecLin B).restrictScalars h.fixedField) u := by
    intro M hM u
    have hM' : M ∈ unitarySU p f K d := by rw [unitarySU_eq_gramSU h]; exact hM
    change B *ᵥ ((M : Matrix (Fin d) (Fin d) K) *ᵥ u) = (M : Matrix (Fin d) (Fin d) K) *ᵥ (B *ᵥ u)
    rw [mulVec_mulVec, mulVec_mulVec, hB M hM']
  obtain ⟨a, ha⟩ := coordinate_commutant_scalar h h2 hd hcN hck
    ((Matrix.mulVecLin B).restrictScalars h.fixedField)
    (fun i l hil u => by
      obtain ⟨M, hM, hMmem⟩ := unitSignDiag_mem h hil
      have := hcomm M hMmem u
      rwa [hM] at this)
    (fun i j hij u => by
      obtain ⟨M, hM, hMmem⟩ := unitLambdaDiag_mem h hcN hij
      have := hcomm M hMmem u
      rwa [hM] at this)
    (fun i j hij u => by
      obtain ⟨M, hM, hMmem⟩ := unitSignedSwapMatrix_mem h hij
      have := hcomm M hMmem u
      rwa [hM] at this)
  refine ⟨a, Matrix.ext fun i j => ?_⟩
  have h5 := congrFun (ha (Pi.single j 1)) i
  change (B *ᵥ Pi.single j 1) i = (a • (Pi.single j 1 : Fin d → K)) i at h5
  simpa [mulVec_single_one, Pi.single_apply, Matrix.smul_apply, Matrix.one_apply, eq_comm] using h5

theorem exists_similitude_of_conj_mem (h : UnitaryFieldData p f K) (hp : p ≠ 2) {d : ℕ}
    (hd : 3 ≤ d) (g : GL (Fin d) K) (φ : K ≃+* K)
    (hg : ∀ x : unitarySU p f K d, g * glAut φ (x : GL (Fin d) K) * g⁻¹ ∈ unitarySU p f K d) :
    ∃ c : K, c ≠ 0 ∧ h.bar c = c ∧
      ((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (g : Matrix (Fin d) (Fin d) K) = c • 1 := by
  obtain ⟨c, hc⟩ := eq_smul_one_of_commute h hp hd
    (((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (g : Matrix (Fin d) (Fin d) K))
    fun y hy => conjTranspose_mul_commute h g hy (conj_mem_unitarySU_of h g φ hg hy)
  have hGGi : (g : Matrix (Fin d) (Fin d) K) * ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hne : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  refine ⟨c, ?_, ?_, hc⟩
  · rintro rfl
    have hz : ((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ = 0 := by
      have := congrArg (· * ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) hc
      simpa [Matrix.mul_assoc, hGGi] using this
    have hstar : ((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
        (((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ = 1 := by
      rw [← transpose_mul, ← Matrix.map_mul, hGiG,
        Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one]
    rw [hz, Matrix.zero_mul] at hstar
    exact zero_ne_one hstar
  ·
    have h0 := congrFun (congrFun hc ⟨0, by omega⟩) ⟨0, by omega⟩
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one] at h0
    rw [← h0, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, UnitaryFieldData.bar_bar, mul_comm]

theorem exists_similitude_of_matrix_form {K : Type} [Field K] [Finite K] [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {d : ℕ}
    (hd : 3 ≤ d) {g : GL (Fin d) K} {φ : K ≃+* K} (α : Su K p f d →* Su K p f d)
    (hα : ∀ x, ((α x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (g : Matrix (Fin d) (Fin d) K) *
        φ.mapMatrix ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          ((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    ∃ c : K, c ≠ 0 ∧ unitaryInvolution K p f c = c ∧
      ((g : Matrix (Fin d) (Fin d) K).map (unitaryInvolution K p f))ᵀ *
        (g : Matrix (Fin d) (Fin d) K) = c • 1 := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hbar : ∀ c, h.bar c = unitaryInvolution K p f c := fun c => by
    rw [unitaryInvolution_apply, UnitaryFieldData.bar_apply]
  obtain ⟨c, hc0, hcb, hc⟩ := exists_similitude_of_conj_mem h hp2 hd g φ fun x => by
    have hx : (x : GL (Fin d) K) ∈ SUid (unitaryInvolution K p f) d := by
      rw [SUid_eq_statedSU hK d]
      exact x.2
    have h1 : g * glAut φ (x : GL (Fin d) K) * g⁻¹ = (α ⟨x, hx⟩ : GL (Fin d) K) :=
      Units.ext (by rw [hα, Units.val_mul, Units.val_mul, coe_glAut, RingEquiv.mapMatrix_apply])
    have h2 : ((α ⟨x, hx⟩ : Su K p f d) : GL (Fin d) K) ∈
        CFSG.Assembly.LowTwoRank.StatedSU d (p ^ f) K := by
      rw [← SUid_eq_statedSU hK d]
      exact (α ⟨x, hx⟩).2
    rw [h1]
    exact h2
  have hmap : (g : Matrix (Fin d) (Fin d) K).map (unitaryInvolution K p f) =
      (g : Matrix (Fin d) (Fin d) K).map h.bar := by
    ext i j
    simp only [Matrix.map_apply, hbar]
  exact ⟨c, hc0, (hbar c).symm.trans hcb, by rw [hmap]; exact hc⟩

end CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
