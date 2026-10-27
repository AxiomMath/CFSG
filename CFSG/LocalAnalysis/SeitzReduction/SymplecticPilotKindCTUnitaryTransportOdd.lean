module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryTransport

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup
  mem_matrixIsometryGroup)
open CFSG.LieType.Universal.Unitary.SUExtras (mat mat_injective)
open scoped MatrixGroups

section Conj

variable {K : Type*} [Field K] {n : ℕ}

theorem conjMat_isometry (b : K →+* K) {R Rinv C g : Matrix (Fin n) (Fin n) K}
    (hR : R * Rinv = 1) (hbR : R.map b = R) (hbRi : Rinv.map b = Rinv)
    (hg : (g.map b)ᵀ * C * g = C) :
    ((Rinv * g * R).map b)ᵀ * (Rᵀ * C * R) * (Rinv * g * R) = Rᵀ * C * R := by
  have e1 : Rinvᵀ * Rᵀ = 1 := by rw [← transpose_mul, hR, transpose_one]
  calc ((Rinv * g * R).map b)ᵀ * (Rᵀ * C * R) * (Rinv * g * R)
      = Rᵀ * ((g.map b)ᵀ * ((Rinvᵀ * Rᵀ) * C * (R * Rinv)) * g) * R := by
        rw [Matrix.map_mul, Matrix.map_mul, hbR, hbRi]
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = Rᵀ * C * R := by rw [e1, hR, Matrix.one_mul, Matrix.mul_one, hg, Matrix.mul_assoc]

theorem antidiag_transpose' : (antidiag n : Matrix (Fin n) (Fin n) K)ᵀ = antidiag n := by
  ext i j
  simp only [transpose_apply, antidiag, of_apply]
  by_cases h : i = Fin.rev j
  · rw [ite_eq_left h, ite_eq_left (by rw [h, Fin.rev_rev])]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [h', Fin.rev_rev]))]

theorem antidiag_mul_self : (antidiag n : Matrix (Fin n) (Fin n) K) * antidiag n = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp only [antidiag, of_apply, ite_true, one_mul, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp
    · rw [ite_eq_right (fun h' => h (by rw [h', Fin.rev_rev])), ite_eq_right h]
  · intro c _ hc
    simp only [antidiag, of_apply]
    rw [ite_eq_right hc, zero_mul]
  · simp

end Conj

section Congr

variable {k : Type} [Field k] [Finite k] [CharP k 2] {n : ℕ}

theorem exists_mul_antidiag_mul_transpose_eq_one {i₀ : Fin n} (hi₀ : Fin.rev i₀ = i₀) :
    ∃ P : GL (Fin n) k, (P : Matrix (Fin n) (Fin n) k) * antidiag n *
      (P : Matrix (Fin n) (Fin n) k)ᵀ = 1 := by
  refine CFSG.SeitzReduction.SymplecticLagrangian.exists_mul_mul_transpose_eq_one
    antidiag_transpose' ⟨⟨_, _, antidiag_mul_self, antidiag_mul_self⟩, rfl⟩ fun hall => ?_
  have h1 := hall (Pi.single i₀ 1)
  rw [Matrix.mulVec_single_one, single_dotProduct, one_mul] at h1
  have h2 : (antidiag n : Matrix (Fin n) (Fin n) k) i₀ i₀ = 1 := by
    rw [antidiag, of_apply, ite_eq_left hi₀.symm]
  rw [col_apply, h2] at h1
  exact one_ne_zero h1

variable (P : GL (Fin n) k)

@[expose] def oddQ : Matrix (Fin n) (Fin n) k := (P : Matrix (Fin n) (Fin n) k)ᵀ

@[expose] noncomputable def oddQi : Matrix (Fin n) (Fin n) k :=
  ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)ᵀ

omit [Finite k] [CharP k 2] in
theorem oddQ_mul_oddQi : oddQ P * oddQi P = 1 := by
  rw [oddQ, oddQi, ← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one]

omit [Finite k] [CharP k 2] in
theorem oddQi_mul_oddQ : oddQi P * oddQ P = 1 := by
  rw [oddQ, oddQi, ← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]

end Congr

section Beta

variable {k : Type} [Field k] [Finite k] [CharP k 2] {m : ℕ} (P : GL (Fin (2 * m + 1)) k)
  (hP : ((P : GL (Fin (2 * m + 1)) k) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) k) *
    antidiag (2 * m + 1) *
      ((P : GL (Fin (2 * m + 1)) k) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) k)ᵀ = 1)

noncomputable abbrev ctuEmbedK : StatedSp m k →* SU (RingEquiv.refl k) (2 * m + 1) :=
  ctuEmbed 1 le_rfl (RingEquiv.refl k) (RingHom.id k) (fun _ => rfl)

omit [Finite k] in
include hP in
theorem oddBeta_mem (z : StatedSp m k) :
    (oddQi P * mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK z) * oddQ P)ᵀ * 1 *
      (oddQi P * mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK z) * oddQ P) = 1 := by
  have hQ : (oddQ P)ᵀ * antidiag (2 * m + 1) * oddQ P = 1 := by
    rw [oddQ, transpose_transpose]
    exact hP
  have hb : ∀ M : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) k, M.map (RingHom.id k) = M :=
    fun M => by
      ext
      rfl
  have h := conjMat_isometry (RingHom.id k) (oddQ_mul_oddQi P) (hb _) (hb _)
    (g := mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK z)) (C := antidiag (2 * m + 1))
    (ctuEmbedK z).2.2
  rw [hQ, hb] at h
  exact h

@[expose] noncomputable def oddBetaHom :
    StatedSp m k →* matrixIsometryGroup (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) k) where
  toFun z := ⟨⟨oddQi P * mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK z) * oddQ P,
      oddQi P * mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK z⁻¹) * oddQ P,
      by
        calc _ = oddQi P * (mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK z) *
              (oddQ P * oddQi P) * mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK z⁻¹)) *
                oddQ P := by simp only [Matrix.mul_assoc]
          _ = 1 := by
            rw [oddQ_mul_oddQi, Matrix.mul_one, ← map_mul, ← map_mul, mul_inv_cancel, map_one,
              map_one, Matrix.mul_one, oddQi_mul_oddQ],
      by
        calc _ = oddQi P * (mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK z⁻¹) *
              (oddQ P * oddQi P) * mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK z)) *
                oddQ P := by simp only [Matrix.mul_assoc]
          _ = 1 := by
            rw [oddQ_mul_oddQi, Matrix.mul_one, ← map_mul, ← map_mul, inv_mul_cancel, map_one,
              map_one, Matrix.mul_one, oddQi_mul_oddQ]⟩,
    oddBeta_mem P hP z⟩
  map_one' := Subtype.ext (Units.ext (by
    change oddQi P * mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK 1) * oddQ P = 1
    rw [map_one, map_one, Matrix.mul_one, oddQi_mul_oddQ]))
  map_mul' z z' := Subtype.ext (Units.ext (by
    change oddQi P * mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK (z * z')) * oddQ P =
      (oddQi P * mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK z) * oddQ P) *
        (oddQi P * mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK z') * oddQ P)
    rw [map_mul, map_mul]
    calc _ = oddQi P * (mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK z) *
          (oddQ P * oddQi P) * mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK z')) * oddQ P := by
          rw [oddQ_mul_oddQi, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]))

omit [Finite k] in
theorem coe_oddBetaHom (z : StatedSp m k) :
    (((oddBetaHom P hP z : matrixIsometryGroup (1 : Matrix (Fin (2 * m + 1))
      (Fin (2 * m + 1)) k)) : GL (Fin (2 * m + 1)) k) :
        Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) k) =
      oddQi P * mat (RingEquiv.refl k) (2 * m + 1) (ctuEmbedK z) * oddQ P := rfl

theorem oddBetaHom_bijective : Function.Bijective (oddBetaHom P hP) := by
  have hinj : Function.Injective (oddBetaHom P hP) := by
    intro z z' hzz
    have h1 := congrArg (fun g : matrixIsometryGroup (1 : Matrix (Fin (2 * m + 1))
      (Fin (2 * m + 1)) k) => oddQ P * ((g : GL (Fin (2 * m + 1)) k) :
        Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) k) * oddQi P) hzz
    simp only [coe_oddBetaHom] at h1
    have e : ∀ M : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) k,
        oddQ P * (oddQi P * M * oddQ P) * oddQi P = M := by
      intro M
      calc _ = (oddQ P * oddQi P) * M * (oddQ P * oddQi P) := by simp only [Matrix.mul_assoc]
        _ = M := by rw [oddQ_mul_oddQi, Matrix.one_mul, Matrix.mul_one]
    rw [e, e] at h1
    exact ctuEmbed_injective (mat_injective h1)
  obtain ⟨β⟩ := nonempty_statedSp_mulEquiv_isometryOne k m
  exact ⟨hinj, (hinj.bijective_of_nat_card_le (Nat.card_congr β.toEquiv).ge).2⟩

@[expose] noncomputable def oddBeta :
    StatedSp m k ≃* matrixIsometryGroup (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) k) :=
  MulEquiv.ofBijective (oddBetaHom P hP) (oddBetaHom_bijective P hP)

end Beta

section OddGram

variable {f m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {K' : Type} [Field K']
  (h : UnitaryFieldData 2 f K') {C₀ : GL (Fin (2 * m + 1)) K'}
  (hC₀ : ((C₀ : GL (Fin (2 * m + 1)) K') : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') = 1)
  (θ : F ≃+* K') (P : GL (Fin (2 * m + 1)) h.fixedField)
  (hP : ((P : GL (Fin (2 * m + 1)) h.fixedField) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField) * antidiag (2 * m + 1) *
      ((P : GL (Fin (2 * m + 1)) h.fixedField) :
        Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField)ᵀ = 1)

@[expose] noncomputable def oddR : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K' :=
  (oddQ P).map h.fixedField.subtype

@[expose] noncomputable def oddRi : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K' :=
  (oddQi P).map h.fixedField.subtype

theorem oddR_mul_oddRi : oddR h P * oddRi h P = 1 := by
  rw [oddR, oddRi, ← Matrix.map_mul, oddQ_mul_oddQi, Matrix.map_one _ (map_zero _) (map_one _)]

theorem oddRi_mul_oddR : oddRi h P * oddR h P = 1 := by
  rw [oddR, oddRi, ← Matrix.map_mul, oddQi_mul_oddQ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_bar_subtype (M : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField) :
    (M.map h.fixedField.subtype).map h.bar = M.map h.fixedField.subtype := by
  ext i j
  simp only [map_apply]
  exact (h.mem_fixedField.1 (M i j).2)

theorem antidiag_map_subtype :
    (antidiag (2 * m + 1) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField).map
      h.fixedField.subtype = antidiag (2 * m + 1) := by
  ext i j
  simp only [map_apply, antidiag, of_apply]
  split_ifs <;> simp

include hP in
theorem oddR_transpose_antidiag :
    (oddR h P)ᵀ * antidiag (2 * m + 1) * oddR h P = 1 := by
  rw [oddR, ← antidiag_map_subtype h, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, oddQ,
    transpose_transpose, hP, Matrix.map_one _ (map_zero _) (map_one _)]

include hP in
theorem oddRi_transpose_mul_oddRi : (oddRi h P)ᵀ * 1 * oddRi h P = antidiag (2 * m + 1) := by
  have h1 := oddR_transpose_antidiag h P hP
  calc (oddRi h P)ᵀ * 1 * oddRi h P
      = (oddRi h P)ᵀ * ((oddR h P)ᵀ * antidiag (2 * m + 1) * oddR h P) * oddRi h P := by rw [h1]
    _ = (oddR h P * oddRi h P)ᵀ * antidiag (2 * m + 1) * (oddR h P * oddRi h P) := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = antidiag (2 * m + 1) := by
      rw [oddR_mul_oddRi, transpose_one, Matrix.one_mul, Matrix.mul_one]

omit [Finite F] [CharP F 2] in
theorem transportMat_refl_antidiag :
    transportMat (θ : F →+* K') (Equiv.refl (Fin (2 * m + 1)))
      (antidiag (2 * m + 1) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) F) =
        antidiag (2 * m + 1) := by
  ext i j
  simp only [transportMat, map_apply, submatrix_apply, Equiv.refl_apply, antidiag, of_apply]
  split_ifs <;> simp

@[expose] noncomputable def oddTransportMat (A : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) F) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K' :=
  oddRi h P * transportMat (θ : F →+* K') (Equiv.refl _) A * oddR h P

omit [Finite F] [CharP F 2] in
theorem oddTransportMat_mul (A B : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) F) :
    oddTransportMat h θ P (A * B) = oddTransportMat h θ P A * oddTransportMat h θ P B := by
  rw [oddTransportMat, oddTransportMat, oddTransportMat, transportMat_mul]
  calc _ = oddRi h P * transportMat (θ : F →+* K') (Equiv.refl _) A * (oddR h P * oddRi h P) *
        transportMat (θ : F →+* K') (Equiv.refl _) B * oddR h P := by
        rw [oddR_mul_oddRi, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

omit [Finite F] [CharP F 2] in
theorem oddTransportMat_one : oddTransportMat h θ P 1 = 1 := by
  rw [oddTransportMat, transportMat_one, Matrix.mul_one, oddRi_mul_oddR]

include hC₀ hP in
theorem oddTransportMat_mem_gramSU (y : SU (unitaryInvolution F 2 f) (2 * m + 1)) :
    ((oddTransportMat h θ P (mat (unitaryInvolution F 2 f) (2 * m + 1) y)).map h.bar)ᵀ *
        (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') *
          oddTransportMat h θ P (mat (unitaryInvolution F 2 f) (2 * m + 1) y) =
        (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') ∧
      (oddTransportMat h θ P (mat (unitaryInvolution F 2 f) (2 * m + 1) y)).det = 1 := by
  refine ⟨?_, ?_⟩
  · rw [hC₀, ← oddR_transpose_antidiag h P hP]
    have h1 := transportMat_isometry (θ : F →+* K') (Equiv.refl (Fin (2 * m + 1)))
      (ringEquiv_unitaryInvolution h θ) y.2.2
    rw [transportMat_refl_antidiag] at h1
    exact conjMat_isometry h.bar (oddR_mul_oddRi h P) (map_bar_subtype h _) (map_bar_subtype h _) h1
  · rw [oddTransportMat, det_mul, det_mul, det_transportMat,
      show (mat (unitaryInvolution F 2 f) (2 * m + 1) y).det = 1 from y.2.1, map_one, mul_one,
      ← det_mul, oddRi_mul_oddR, det_one]

@[expose] noncomputable def ctuOddGramHom :
    SU (unitaryInvolution F 2 f) (2 * m + 1) →*
      gramSU h (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') where
  toFun y := ⟨⟨oddTransportMat h θ P (mat (unitaryInvolution F 2 f) (2 * m + 1) y),
      oddTransportMat h θ P (mat (unitaryInvolution F 2 f) (2 * m + 1) y⁻¹),
      by rw [← oddTransportMat_mul, ← map_mul, mul_inv_cancel, map_one, oddTransportMat_one],
      by rw [← oddTransportMat_mul, ← map_mul, inv_mul_cancel, map_one, oddTransportMat_one]⟩,
    oddTransportMat_mem_gramSU h hC₀ θ P hP y⟩
  map_one' := Subtype.ext (Units.ext (by
    change oddTransportMat h θ P (mat (unitaryInvolution F 2 f) (2 * m + 1) 1) = 1
    rw [map_one, oddTransportMat_one]))
  map_mul' y z := Subtype.ext (Units.ext (by
    change oddTransportMat h θ P (mat (unitaryInvolution F 2 f) (2 * m + 1) (y * z)) = _
    rw [map_mul, oddTransportMat_mul]
    rfl))

theorem coe_ctuOddGramHom (y : SU (unitaryInvolution F 2 f) (2 * m + 1)) :
    (((ctuOddGramHom h hC₀ θ P hP y : gramSU h
      (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K')) : GL (Fin (2 * m + 1)) K') :
        Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') =
      oddTransportMat h θ P (mat (unitaryInvolution F 2 f) (2 * m + 1) y) := rfl

omit [Finite F] [CharP F 2] in
theorem transportMat_symm_refl_antidiag :
    transportMat (θ.symm : K' →+* F) (Equiv.refl (Fin (2 * m + 1))).symm
      (antidiag (2 * m + 1) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') =
        antidiag (2 * m + 1) := by
  ext i j
  simp only [transportMat, map_apply, submatrix_apply, Equiv.refl_symm, Equiv.refl_apply, antidiag,
    of_apply]
  split_ifs <;> simp

theorem ctuOddGramHom_bijective : Function.Bijective (ctuOddGramHom h hC₀ θ P hP) := by
  have hback : ∀ A : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) F,
      transportMat (θ.symm : K' →+* F) (Equiv.refl (Fin (2 * m + 1))).symm
        (oddR h P * oddTransportMat h θ P A * oddRi h P) = A := by
    intro A
    have e : oddR h P * oddTransportMat h θ P A * oddRi h P =
        transportMat (θ : F →+* K') (Equiv.refl _) A := by
      rw [oddTransportMat]
      calc _ = (oddR h P * oddRi h P) * transportMat (θ : F →+* K') (Equiv.refl _) A *
            (oddR h P * oddRi h P) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [oddR_mul_oddRi, Matrix.one_mul, Matrix.mul_one]
    rw [e, transportMat_symm_transportMat]
  constructor
  · intro y z hyz
    have h1 := congrArg (fun g : gramSU h (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') =>
      transportMat (θ.symm : K' →+* F) (Equiv.refl (Fin (2 * m + 1))).symm
        (oddR h P * ((g : GL (Fin (2 * m + 1)) K') : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K')
          * oddRi h P)) hyz
    simp only [coe_ctuOddGramHom, hback] at h1
    exact mat_injective h1
  · intro g
    set X := oddR h P * ((g : GL (Fin (2 * m + 1)) K') :
      Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') * oddRi h P with hX
    set Xi := oddR h P * (((g⁻¹ : gramSU h (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K')) :
      GL (Fin (2 * m + 1)) K') : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') * oddRi h P
      with hXi
    have hXXi : X * Xi = 1 := by
      calc X * Xi = oddR h P * (((g * g⁻¹ : gramSU h (C₀ : Matrix (Fin (2 * m + 1))
            (Fin (2 * m + 1)) K')) : GL (Fin (2 * m + 1)) K') :
              Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') * oddRi h P := by
            rw [hX, hXi, Subgroup.coe_mul, Units.val_mul]
            calc _ = oddR h P * ((g : GL (Fin (2 * m + 1)) K') :
                  Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') * (oddRi h P * oddR h P) *
                (((g⁻¹ : gramSU h (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K')) :
                  GL (Fin (2 * m + 1)) K') :
                    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') * oddRi h P := by
                  simp only [Matrix.mul_assoc]
              _ = _ := by rw [oddRi_mul_oddR, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [mul_inv_cancel, Subgroup.coe_one, Units.val_one, Matrix.mul_one,
            oddR_mul_oddRi]
    have hXiX : Xi * X = 1 := by
      calc Xi * X = oddR h P * (((g⁻¹ * g : gramSU h (C₀ : Matrix (Fin (2 * m + 1))
            (Fin (2 * m + 1)) K')) : GL (Fin (2 * m + 1)) K') :
              Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') * oddRi h P := by
            rw [hX, hXi, Subgroup.coe_mul, Units.val_mul]
            calc _ = oddR h P * (((g⁻¹ : gramSU h (C₀ : Matrix (Fin (2 * m + 1))
                  (Fin (2 * m + 1)) K')) : GL (Fin (2 * m + 1)) K') :
                    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') * (oddRi h P * oddR h P) *
                ((g : GL (Fin (2 * m + 1)) K') :
                  Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') * oddRi h P := by
                  simp only [Matrix.mul_assoc]
              _ = _ := by rw [oddRi_mul_oddR, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [inv_mul_cancel, Subgroup.coe_one, Units.val_one, Matrix.mul_one,
            oddR_mul_oddRi]
    have hgiso : (((g : GL (Fin (2 * m + 1)) K') :
        Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K').map h.bar)ᵀ * 1 *
          ((g : GL (Fin (2 * m + 1)) K') : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') = 1 := by
      have := g.2.1
      simp only [hC₀] at this
      exact this
    have hXiso : (X.map h.bar)ᵀ * antidiag (2 * m + 1) * X = antidiag (2 * m + 1) := by
      rw [← oddRi_transpose_mul_oddRi h P hP]
      exact conjMat_isometry h.bar (oddRi_mul_oddR h P) (map_bar_subtype h _)
        (map_bar_subtype h _) hgiso
    have hdetX : X.det = 1 := by
      rw [hX, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, oddRi_mul_oddR, det_one, one_mul]
      exact g.2.2
    refine ⟨⟨⟨transportMat (θ.symm : K' →+* F) (Equiv.refl (Fin (2 * m + 1))).symm X,
      transportMat (θ.symm : K' →+* F) (Equiv.refl (Fin (2 * m + 1))).symm Xi,
      by rw [← transportMat_mul, hXXi, transportMat_one],
      by rw [← transportMat_mul, hXiX, transportMat_one]⟩,
      by
        change (transportMat (θ.symm : K' →+* F) (Equiv.refl (Fin (2 * m + 1))).symm X).det = 1
        rw [det_transportMat, hdetX, map_one],
      by
        have h1 := transportMat_isometry (θ.symm : K' →+* F) (Equiv.refl (Fin (2 * m + 1))).symm
          (ringEquiv_symm_bar h θ) hXiso
        rw [transportMat_symm_refl_antidiag] at h1
        exact h1⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_ctuOddGramHom]
    change oddRi h P * transportMat (θ : F →+* K') (Equiv.refl _)
      (transportMat (θ.symm : K' →+* F) (Equiv.refl (Fin (2 * m + 1))).symm X) * oddR h P = _
    rw [transportMat_transportMat_symm, hX]
    calc _ = (oddRi h P * oddR h P) * ((g : GL (Fin (2 * m + 1)) K') :
          Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') * (oddRi h P * oddR h P) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [oddRi_mul_oddR, Matrix.one_mul, Matrix.mul_one]

@[expose] noncomputable def ctuOddGramEquiv :
    SU (unitaryInvolution F 2 f) (2 * m + 1) ≃*
      gramSU h (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') :=
  MulEquiv.ofBijective (ctuOddGramHom h hC₀ θ P hP) (ctuOddGramHom_bijective h hC₀ θ P hP)

theorem ctuOddGramEquiv_ctuEmbed [CharP h.fixedField 2] [Finite h.fixedField] {K₀ : Type}
    [Field K₀] [CharP K₀ 2]
    {ι : K₀ →+* F} (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c) (ι' : K₀ ≃+* h.fixedField)
    (hθι : ∀ c, θ (ι c) = (ι' c : K')) (x : StatedSp m K₀) :
    ctuOddGramEquiv h hC₀ θ P hP (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι x) =
      isoOneToSU h hC₀ (oddBeta P hP (F4Pilot.statedSpMap (ι' : K₀ →+* h.fixedField) m x)) := by
  apply Subtype.ext
  apply Units.ext
  change oddTransportMat h θ P (mat (unitaryInvolution F 2 f) (2 * m + 1)
    (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι x)) = _
  rw [coe_isoOneToSU]
  change _ = (oddQi P * mat (RingEquiv.refl h.fixedField) (2 * m + 1)
    (ctuEmbedK (F4Pilot.statedSpMap (ι' : K₀ →+* h.fixedField) m x)) * oddQ P).map
      h.fixedField.subtype
  rw [Matrix.map_mul, Matrix.map_mul, oddTransportMat]
  change oddRi h P * _ * oddR h P = oddRi h P * _ * oddR h P
  congr 2
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord m 1).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord m 1).surjective b
  simp only [transportMat, map_apply, submatrix_apply, Equiv.refl_apply]
  change θ (ctuEmbedMat 1 ι _ (ctuCoord m 1 w) (ctuCoord m 1 w')) =
    h.fixedField.subtype (ctuEmbedMat 1 (RingHom.id h.fixedField) _ (ctuCoord m 1 w)
      (ctuCoord m 1 w'))
  rw [ctuEmbedMat_apply, ctuEmbedMat_apply]
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁, fromBlocks_apply₁₁, map_apply, map_apply, hθι]
    rfl
  · simp
  · simp
  · rw [fromBlocks_apply₂₂, fromBlocks_apply₂₂, one_apply, one_apply]
    split_ifs <;> simp

end OddGram

section OddParam

variable {G : Type} [Group G] {L : Subgroup G} {K₀ : Type} [Field K₀] [CharP K₀ 2] {m f : ℕ}
  {F : Type} [Field F] [Finite F] [CharP F 2] {ι : K₀ →+* F}
  {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp (m + 1) K₀} {t : G}
  {k : Fin (m + 1)} {K' : Type} [Field K'] {h : UnitaryFieldData 2 f K'} [CharP h.fixedField 2]
  [Finite h.fixedField] {C₀ : GL (Fin (2 * m + 1)) K'} {hC : IsPrimeFormGram C₀}
  {hC₀ : ((C₀ : GL (Fin (2 * m + 1)) K') : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') = 1}
  {ι' : K₀ ≃+* h.fixedField}

@[expose] noncomputable def ctuParamOfUnitaryOdd (θ : F ≃+* K')
    (hθι : ∀ c, θ (ι c) = (ι' c : K')) (P : GL (Fin (2 * m + 1)) h.fixedField)
    (hP : ((P : GL (Fin (2 * m + 1)) h.fixedField) :
      Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField) * antidiag (2 * m + 1) *
        ((P : GL (Fin (2 * m + 1)) h.fixedField) :
          Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField)ᵀ = 1)
    (Pa : UnitaryOddNeighbourParam h e t k hC hC₀ (oddBeta P hP) ι') :
    CtuParam 1 le_rfl (unitaryInvolution F 2 f) ι hι e k where
  Φ := Pa.Φ.comp (((ctuBlockEquiv (unitaryInvolution F 2 f) le_rfl k).trans
    (ctuOddGramEquiv h hC₀ θ P hP)).toMonoidHom)
  ker_le := by
    intro x hx
    exact mem_center_of_mulEquiv_mem_center _ (Pa.ker_le hx)
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, Pa.range_eq]
  N1 y hy := by
    rw [spBlock_compl_singleton] at hy
    obtain ⟨x, hx⟩ := (complSpEquiv k).surjective ⟨y, hy⟩
    have hyx : y = ((complSpEquiv k x : complSp K₀ k) : StatedSp (m + 1) K₀) := by rw [hx]
    subst hyx
    change Pa.Φ (ctuOddGramEquiv h hC₀ θ P hP (ctuBlockEquiv (unitaryInvolution F 2 f) le_rfl k
      ⟨_, _⟩)) = _
    rw [ctuBlockEquiv_ctuEmbed, ctuOddGramEquiv_ctuEmbed h hC₀ θ P hP hι ι' hθι, Pa.N1 x]

end OddParam

theorem spUnitaryOddCtuParamInput_holds : SpUnitaryOddCtuParamInput := by
  intro G _ _ L hset m f K _ _ _ hm hKc hf e t ht hKt hP
  obtain ⟨K₀', _, h₀, _, C₀, hC, hC₀, hβ₀⟩ := hP 0
  have : Finite K₀' := h₀.finite
  have : CharP K₀' 2 := h₀.charP
  have : Finite h₀.fixedField :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h₀
  obtain ⟨P₀, hP₀⟩ := exists_mul_antidiag_mul_transpose_eq_one (k := h₀.fixedField)
    (n := 2 * m + 1) (i₀ := ⟨m, by omega⟩) (Fin.ext (by simp only [Fin.val_rev]; omega))
  obtain ⟨ι₀, -⟩ := hβ₀ (oddBeta P₀ hP₀)
  have hF : Nat.card K₀' = (2 ^ f) ^ 2 := by rw [h₀.card, ← pow_mul, mul_comm]
  set ι : K →+* K₀' := h₀.fixedField.subtype.comp (ι₀ : K →+* h₀.fixedField) with hιdef
  have hι : ∀ c, unitaryInvolution K₀' 2 f (ι c) = ι c := fun c => by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h₀.bar_apply]
    exact (h₀.mem_fixedField.1 (ι₀ c).2)
  refine ⟨K₀', inferInstance, inferInstance, inferInstance, hF, ι, hι, fun k => ?_⟩
  obtain ⟨K', _, h, _, C, hCk, hCk₀, hβ⟩ := hP k
  have : Finite K' := h.finite
  have : Finite h.fixedField :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  obtain ⟨P, hPk⟩ := exists_mul_antidiag_mul_transpose_eq_one (k := h.fixedField)
    (n := 2 * m + 1) (i₀ := ⟨m, by omega⟩) (Fin.ext (by simp only [Fin.val_rev]; omega))
  obtain ⟨ι', ⟨Pa⟩⟩ := hβ (oddBeta P hPk)
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_comp_eq ι
    (h.fixedField.subtype.comp (ι' : K →+* h.fixedField))
    (by rw [hF, h.card, ← pow_mul, mul_comm])
  exact ⟨ctuParamOfUnitaryOdd θ hθ P hPk Pa⟩

theorem spUnitaryOddParamCTInput_of_align (hA : CtuAlignInput 1 le_rfl)
    (h4 : SpUnitaryOddParamCTFourInput) : SpUnitaryOddParamCTInput :=
  spUnitaryOddParamCTInput_of_inputs spUnitaryOddCtuParamInput_holds hA h4

end CFSG.SeitzReduction.SymplecticPilot
