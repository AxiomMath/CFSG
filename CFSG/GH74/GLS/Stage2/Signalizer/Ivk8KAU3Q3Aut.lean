module

public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.GH74.KGroups.L3EpsUniAut

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps.Uni CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open CFSG.GH74.Generic.S45.Uni (det_unitary_norm mkSU coe_mkSU)
open scoped MatrixGroups

section Q3Aut

variable {p f : ℕ} {F : Type} [Field F]

theorem exists_conj_of_unitary_q3 (h : UnitaryFieldData p f F) (hq3 : p ^ f = 3)
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    {σ : MulAut K} {A : GL (Fin 3) F}
    (hAu : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1)
    (hrel : ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
      (g' : GL (Fin 3) F) = A * g * A⁻¹ ∧ θ g' = σ (θ g)) :
    ∃ y : K, MulAut.conj y = σ := by
  set Am : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) with hAm
  have hd0 : Am.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A)).ne_zero
  have hNd := det_unitary_norm h hAu
  have hbar : ∀ c : F, h.bar c = c ^ 3 := fun c => by rw [UnitaryFieldData.bar_apply, hq3]
  set ν : F := Am.det with hν
  have hν0 : ν ≠ 0 := hd0
  have hν3 : ν ^ 3 * Am.det = 1 := by
    have := hNd
    rw [hbar] at this
    exact this
  have hNν : h.bar ν * ν = 1 := hNd
  have hxu : (((ν • Am).map h.bar)ᵀ) * (ν • Am) = 1 := by
    have hm : (ν • Am).map h.bar = h.bar ν • Am.map h.bar := by
      ext i j
      simp
    rw [hm, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAu, hNν, one_smul]
  have hxd : (ν • Am).det = 1 := by
    rw [det_smul, Fintype.card_fin, hν3]
  let x : ↥(unitarySU p f F 3) := mkSU h (ν • Am) hxu hxd
  have hxGL : (x : GL (Fin 3) F) = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ν hν0) * A := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_mkSU, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
    rfl
  refine ⟨θ x, ?_⟩
  ext k
  obtain ⟨g, rfl⟩ := hθ.surj k
  obtain ⟨g', hg'GL, hg'θ⟩ := hrel g
  have hgg : g' = x * g * x⁻¹ := by
    apply Subtype.ext
    rw [hg'GL]
    show A * g * A⁻¹ = (x : GL (Fin 3) F) * g * (x : GL (Fin 3) F)⁻¹
    rw [hxGL, conj_scalar_mul]
  rw [← hg'θ, hgg, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem ringEquiv_comm_bar (h : UnitaryFieldData p f F) (φ : F ≃+* F) (c : F) :
    φ (h.bar c) = h.bar (φ c) := by
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, map_pow]

theorem map_unitary_of_ringEquiv (h : UnitaryFieldData p f F) (φ : F ≃+* F)
    {A : Matrix (Fin 3) (Fin 3) F} (hAu : (A.map h.bar)ᵀ * A = 1) :
    ((A.map φ).map h.bar)ᵀ * A.map φ = 1 := by
  have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M.map φ) hAu
  simp only [Matrix.map_mul, Matrix.transpose_map] at h1
  have h2 : (A.map h.bar).map φ = (A.map φ).map h.bar := by
    ext i j
    simp [ringEquiv_comm_bar h φ]
  rw [h2] at h1
  simpa [Matrix.transpose_map] using h1

theorem unitary_mul_q3 (h : UnitaryFieldData p f F) {A B : Matrix (Fin 3) (Fin 3) F}
    (hA : (A.map h.bar)ᵀ * A = 1) (hB : (B.map h.bar)ᵀ * B = 1) :
    ((A * B).map h.bar)ᵀ * (A * B) = 1 := by
  rw [Matrix.map_mul, transpose_mul]
  calc (B.map h.bar)ᵀ * (A.map h.bar)ᵀ * (A * B)
      = (B.map h.bar)ᵀ * ((A.map h.bar)ᵀ * A) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA, Matrix.mul_one, hB]

theorem ringEquiv_mul_self_q3 (hq3 : p ^ f = 3) (hF : Nat.card F = (p ^ f) ^ 2) [Finite F]
    (φ : F ≃+* F) : φ * φ = 1 := by
  have hc := (card_ringAut_and_isCyclic (p := 3) (n := 2) Nat.prime_three F
    (by rw [hF, hq3])).1
  have : Fintype (RingAut F) := Fintype.ofFinite _
  have h1 : (φ : RingAut F) ^ Nat.card (RingAut F) = 1 := pow_card_eq_one'
  rw [hc, sq] at h1
  exact h1

theorem aut_sq_inner_q3 [Finite F] (h : UnitaryFieldData p f F) (hp : p ≠ 2) (hq3 : p ^ f = 3)
    (hF : Nat.card F = (p ^ f) ^ 2) {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K}
    (hθ : IsCover h θ) (σ : MulAut K) : ∃ y : K, MulAut.conj y = σ * σ := by
  have hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3) := by
    rw [hθ.ker]
    exact unitaryScalars_le_center h 3
  obtain ⟨A, φ, hA, hAu, hlift, -⟩ :=
    CFSG.GH74.Generic.S45.exists_lift_unitarySU' h hp (le_refl 3) θ hθ.surj hker σ
  have hΦmat : ∀ g : ↥(unitarySU p f F 3),
      ((unitaryConjHom A φ hA g : ↥(unitarySU p f F 3)) : GL (Fin 3) F) =
        A * glAut φ (g : GL (Fin 3) F) * A⁻¹ := fun g => rfl
  have hφφ : φ * φ = 1 := ringEquiv_mul_self_q3 hq3 hF φ
  have hgg : ∀ x : GL (Fin 3) F, glAut φ (glAut φ x) = x := by
    intro x
    have : (glAut (ι := Fin 3) φ * glAut (ι := Fin 3) φ : MulAut (GL (Fin 3) F)) = 1 := by
      rw [← map_mul, hφφ, map_one]
    exact congrArg (fun e : MulAut (GL (Fin 3) F) => e x) this
  have hΦ2 : ∀ g : ↥(unitarySU p f F 3),
      ((unitaryConjHom A φ hA (unitaryConjHom A φ hA g) : ↥(unitarySU p f F 3)) : GL (Fin 3) F) =
        (A * glAut φ A) * (g : GL (Fin 3) F) * (A * glAut φ A)⁻¹ := by
    intro g
    rw [hΦmat (unitaryConjHom A φ hA g), hΦmat g, map_mul, map_mul, map_inv, hgg]
    group
  have hDu : (((A * glAut φ A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
      ((A * glAut φ A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [Units.val_mul, coe_glAut]
    exact unitary_mul_q3 h hAu (map_unitary_of_ringEquiv h φ hAu)
  refine exists_conj_of_unitary_q3 h hq3 hθ hDu fun g => ?_
  refine ⟨unitaryConjHom A φ hA (unitaryConjHom A φ hA g), hΦ2 g, ?_⟩
  rw [hlift, hlift]
  rfl

end Q3Aut

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
