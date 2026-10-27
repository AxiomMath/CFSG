module

public import CFSG.GH74.Generic.S45.LUniLift
public import Certificates.Data.CatFactsL4U4P1U43Defs

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.U43

open CFSG.LieType.Multipliers.U43 Matrix CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Sporadic.SmallOddCore

@[expose] def IsUnitaryF (A : GL (Fin 4) F9) : Prop :=
  ((A : Matrix (Fin 4) (Fin 4) F9).map barF)ᵀ * (A : Matrix (Fin 4) (Fin 4) F9) = 1

@[expose] def iF : F9 := ⟨0, 1⟩

theorem unitaryFieldData : UnitaryFieldData 3 1 F9 :=
  ⟨Nat.prime_three, le_rfl, by rw [Nat.card_eq_fintype_card, F9.card_eq]; norm_num⟩

theorem bar_eq_barF (c : F9) : unitaryFieldData.bar c = barF c := by
  rw [UnitaryFieldData.bar_apply, barF_eq_pow, pow_one]

theorem det_cases {A : GL (Fin 4) F9} (hA : IsUnitaryF A) :
    (A : Matrix (Fin 4) (Fin 4) F9).det = 1 ∨ (A : Matrix (Fin 4) (Fin 4) F9).det = iF ∨
      (A : Matrix (Fin 4) (Fin 4) F9).det = -1 ∨ (A : Matrix (Fin 4) (Fin 4) F9).det = -iF := by
  have h1 := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  have h2 : ((A : Matrix (Fin 4) (Fin 4) F9).map barF).det =
      barF (A : Matrix (Fin 4) (Fin 4) F9).det :=
    (RingHom.map_det (barEquiv : F9 →+* F9) _).symm
  rw [h2] at h1
  have key : ∀ x : F9, barF x * x = 1 → x = 1 ∨ x = iF ∨ x = -1 ∨ x = -iF := by decide
  exact key _ h1

theorem inv_eq_of_unitary {D : GL (Fin 4) F9} (hD : IsUnitaryF D) :
    ((D⁻¹ : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
      ((D : Matrix (Fin 4) (Fin 4) F9).map barF)ᵀ := by
  have h1 : ((D⁻¹ : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
      (((D : Matrix (Fin 4) (Fin 4) F9).map barF)ᵀ * D) * (D⁻¹ : GL (Fin 4) F9) := by
    rw [show ((D : Matrix (Fin 4) (Fin 4) F9).map barF)ᵀ * D = 1 from hD, Matrix.one_mul]
  rw [h1, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem isUnitaryF_mul_inv {A D : GL (Fin 4) F9} (hA : IsUnitaryF A) (hD : IsUnitaryF D) :
    IsUnitaryF (A * D⁻¹) := by
  have hbb : ∀ M : Matrix (Fin 4) (Fin 4) F9, (M.map barF).map barF = M := fun M =>
    Matrix.ext fun i j => barF_barF _
  have hDD : (D : Matrix (Fin 4) (Fin 4) F9) * ((D : Matrix (Fin 4) (Fin 4) F9).map barF)ᵀ = 1 :=
    mul_eq_one_comm.mp hD
  have hmul : ∀ M N : Matrix (Fin 4) (Fin 4) F9, (M * N).map barF = M.map barF * N.map barF :=
    fun M N => Matrix.map_mul (f := (barEquiv : F9 →+* F9))
  unfold IsUnitaryF
  rw [Units.val_mul, inv_eq_of_unitary hD, hmul, Matrix.transpose_mul, Matrix.transpose_map,
    Matrix.transpose_transpose, hbb, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (A : Matrix (Fin 4) (Fin 4) F9),
    show ((A : Matrix (Fin 4) (Fin 4) F9).map barF)ᵀ * A = 1 from hA, Matrix.one_mul, hDD]

theorem perm820_mem_range {B : GL (Fin 4) F9} (hB : IsUnitaryF B)
    (hd : (B : Matrix (Fin 4) (Fin 4) F9).det = 1) : perm820 B ∈ psi.range := by
  have hpow : (B : Matrix (Fin 4) (Fin 4) F9).map (· ^ 3) =
      (B : Matrix (Fin 4) (Fin 4) F9).map barF :=
    Matrix.ext fun i j => (barF_eq_pow _).symm
  have hmem : B ∈ StatedSU 4 3 F9 := Subgroup.subset_closure ⟨hd, by rw [hpow]; exact hB⟩
  exact ⟨QuotientGroup.mk ⟨B, hmem⟩, psi_mk _⟩

theorem mem_coset {A D : GL (Fin 4) F9} (hA : IsUnitaryF A) (hD : IsUnitaryF D)
    (hdet : (A : Matrix (Fin 4) (Fin 4) F9).det = (D : Matrix (Fin 4) (Fin 4) F9).det)
    (ε : ℕ) : perm820 A * frob820 ^ ε * (perm820 D * frob820 ^ ε)⁻¹ ∈ psi.range := by
  have h1 : perm820 A * frob820 ^ ε * (perm820 D * frob820 ^ ε)⁻¹ = perm820 (A * D⁻¹) := by
    rw [map_mul, map_inv]
    group
  rw [h1]
  refine perm820_mem_range (isUnitaryF_mul_inv hA hD) ?_
  have hD0 : (D : Matrix (Fin 4) (Fin 4) F9).det ≠ 0 :=
    (D.isUnit.map Matrix.detMonoidHom).ne_zero
  have hDi : (D : Matrix (Fin 4) (Fin 4) F9).det *
      ((D⁻¹ : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [Units.val_mul, Matrix.det_mul, hdet, hDi]

theorem ringEquiv_F9 (φ : F9 ≃+* F9) : φ = RingEquiv.refl F9 ∨ ∀ c, φ c = barF c := by
  have hdec : ∀ c : F9, c = ((c.re.val : ℕ) : F9) + ((c.im.val : ℕ) : F9) * iF := by decide
  have hbar : ∀ c : F9, barF c = ((c.re.val : ℕ) : F9) + ((c.im.val : ℕ) : F9) * -iF := by decide
  have hsq : ∀ x : F9, x * x = -1 → x = iF ∨ x = -iF := by decide
  have hi : φ iF * φ iF = -1 := by
    rw [← map_mul, show iF * iF = -1 by decide, map_neg, map_one]
  have hφ : ∀ c : F9, φ c = ((c.re.val : ℕ) : F9) + ((c.im.val : ℕ) : F9) * φ iF := by
    intro c
    conv_lhs => rw [hdec c]
    rw [map_add, map_mul, map_natCast, map_natCast]
  rcases hsq _ hi with h | h
  · left
    refine RingEquiv.ext fun c => ?_
    rw [hφ c, h, ← hdec c]
    rfl
  · right
    intro c
    rw [hφ c, h, ← hbar c]

@[expose] noncomputable def theta : unitarySU 3 1 F9 4 →* X₀ :=
  QuotientGroup.mk' ((StatedScalars (Fin 4) F9).subgroupOf (StatedSU 4 3 F9))

theorem psi_theta (g : unitarySU 3 1 F9 4) : psi (theta g) = perm820 (g : GL (Fin 4) F9) :=
  psi_mk g

theorem theta_surjective : Function.Surjective theta := QuotientGroup.mk'_surjective _

theorem ker_theta_le : theta.ker ≤ Subgroup.center (unitarySU 3 1 F9 4) := by
  intro z hz
  rw [theta, QuotientGroup.ker_mk'] at hz
  have hz' : (z : GL (Fin 4) F9) ∈ StatedScalars (Fin 4) F9 := hz
  obtain ⟨c, hc⟩ := hz'
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
  have hcen : GeneralLinearGroup.scalar (Fin 4) c ∈ Subgroup.center (GL (Fin 4) F9) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact Subgroup.mem_center_iff.mp hcen _

theorem glAut_refl_apply (g : GL (Fin 4) F9) : glAut (RingEquiv.refl F9) g = g := by
  apply Units.ext
  rw [coe_glAut]
  exact Matrix.ext fun i j => rfl

theorem exists_aut_form (α : MulAut X₀) :
    ∃ (A : GL (Fin 4) F9) (ε : ℕ), ε ≤ 1 ∧ IsUnitaryF A ∧ ∀ x : X₀,
      perm820 A * frob820 ^ ε * psi x * (perm820 A * frob820 ^ ε)⁻¹ = psi (α x) := by
  obtain ⟨A, φ, hA, hAu, hlift, -⟩ := CFSG.GH74.Generic.S45.exists_lift_unitarySU'
    unitaryFieldData (by norm_num) (d := 4) (by norm_num) theta theta_surjective ker_theta_le α
  have hU : IsUnitaryF A := by
    have hm : (A : Matrix (Fin 4) (Fin 4) F9).map unitaryFieldData.bar =
        (A : Matrix (Fin 4) (Fin 4) F9).map barF :=
      Matrix.ext fun i j => bar_eq_barF _
    unfold IsUnitaryF
    rw [← hm]
    exact hAu
  have hpsi : ∀ g : unitarySU 3 1 F9 4, psi (α (theta g)) =
      perm820 A * perm820 (glAut φ (g : GL (Fin 4) F9)) * (perm820 A)⁻¹ := by
    intro g
    rw [← hlift g, psi_theta, coe_unitaryConjHom, map_mul, map_mul, map_inv]
  rcases ringEquiv_F9 φ with rfl | hφ
  · refine ⟨A, 0, by norm_num, hU, fun x => ?_⟩
    obtain ⟨g, rfl⟩ := theta_surjective x
    rw [hpsi g, glAut_refl_apply, psi_theta, pow_zero, mul_one]
  · refine ⟨A, 1, le_rfl, hU, fun x => ?_⟩
    obtain ⟨g, rfl⟩ := theta_surjective x
    have hconj := frob820_conj (g : GL (Fin 4) F9) (glAut φ (g : GL (Fin 4) F9)) (by
      rw [coe_glAut]
      exact Matrix.ext fun i j => hφ _)
    rw [hpsi g, ← hconj, psi_theta, pow_one]
    group

theorem matDm1_sq : matN9 codeDm1 * matN9 codeDm1 = 1 := by decide +kernel

@[expose] def dM1 : GL (Fin 4) F9 := ⟨matN9 codeDm1, matN9 codeDm1, matDm1_sq, matDm1_sq⟩

theorem factorization_two : (2 * 3265920).factorization 2 = 8 := by
  have h : 2 * 3265920 = 2 ^ 8 * 25515 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

end CFSG.ComponentClassification.HarrisLit.P1.U43
