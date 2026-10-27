module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFL4
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFBase
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFEven
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFSpLevi
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.ClassicalInvolution.Q3.Q3MFO4Top

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.L4

open Matrix CFSG CFSG.Blueprint CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalInvolution.Asc77.CX.MF2L (spForm)
open scoped MatrixGroups

section Outer

variable {F : Type} [Field F] [Finite F]

variable (F) in
@[expose] def PSLSymStatement : Prop :=
  ∀ A : GL (Fin 4) F, (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A →
    oddCoreIn (fixedSubgroup (conjAut 4 F A * dualAut 4 F)) = ⊥

omit [Finite F] in
theorem spForm_mul_self : spForm (1 : F) 1 * spForm 1 1 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spForm, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] noncomputable def spFormGL (F : Type) [Field F] : GL (Fin 4) F :=
  ⟨spForm 1 1, -spForm 1 1, by rw [Matrix.mul_neg, spForm_mul_self, neg_neg],
    by rw [Matrix.neg_mul, spForm_mul_self, neg_neg]⟩

omit [Finite F] in
theorem coe_spFormGL : (spFormGL F : Matrix (Fin 4) (Fin 4) F) = spForm 1 1 := rfl

omit [Finite F] in
theorem exists_conj_spFormGL (h2 : (2 : F) ≠ 0) {A : GL (Fin 4) F}
    (hAt : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A) :
    ∃ Q : GL (Fin 4) F, conjAut 4 F A * dualAut 4 F =
      conjAut 4 F Q * (conjAut 4 F (spFormGL F) * dualAut 4 F) * (conjAut 4 F Q)⁻¹ := by
  obtain ⟨P, hP⟩ := exists_spForm_basis h2 hAt (A.isUnit.map Matrix.detMonoidHom).ne_zero
  have hdetP : P.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hP
    rw [det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul] at h1
    have h3 : (spForm (1 : F) 1).det ≠ 0 := (spFormGL F).isUnit.map Matrix.detMonoidHom |>.ne_zero
    exact h3 h1.symm
  set PGL : GL (Fin 4) F := Matrix.GeneralLinearGroup.mkOfDetNeZero P hdetP with hPGL
  have hPc : (PGL : Matrix (Fin 4) (Fin 4) F) = P := rfl
  set Q : GL (Fin 4) F := Matrix.GeneralLinearGroup.inverseTranspose PGL with hQ
  refine ⟨Q, ?_⟩
  have e1 : conjAut 4 F Q * (conjAut 4 F (spFormGL F) * dualAut 4 F) * (conjAut 4 F Q)⁻¹ =
      conjAut 4 F (Q * spFormGL F * Matrix.GeneralLinearGroup.inverseTranspose Q⁻¹) *
        dualAut 4 F := by
    rw [← map_inv, mul_assoc, mul_assoc, dualAut_mul_conjAut, ← mul_assoc, ← mul_assoc, ← map_mul,
      ← map_mul]
  rw [e1]
  have hAeq : A = Q * spFormGL F * Matrix.GeneralLinearGroup.inverseTranspose Q⁻¹ := by
    apply Units.ext
    have hPinv' : P * ((PGL⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← hPc, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hQc : (Q : Matrix (Fin 4) (Fin 4) F) =
        ((PGL⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ :=
      Matrix.GeneralLinearGroup.coe_inverseTranspose PGL
    have hQi : ((Matrix.GeneralLinearGroup.inverseTranspose Q⁻¹ : GL (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F) = ((PGL⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
      rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, inv_inv, hQc, transpose_transpose]
    rw [Units.val_mul, Units.val_mul, hQi, hQc, coe_spFormGL, ← hP]
    calc (A : Matrix (Fin 4) (Fin 4) F)
        = ((P * ((PGL⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))ᵀ) * A *
            (P * ((PGL⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
          rw [hPinv', transpose_one, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
  rw [← hAeq]

theorem oddCoreIn_fixed_of_outer_psl4 (hF : Nat.card F = 3) (hB : PSLSymStatement F)
    (hSp : CFSG.Open.IsQuasisimple (StatedSp 2 F))
    (ρ : MulAut (projectiveSL 4 F)) (hρ2 : ρ * ρ = 1)
    (hout : ρ ∉ innSubgroup (projectiveSL 4 F)) : oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  have h2 : (2 : F) ≠ 0 := Q3MFOD.two_ne_zero_of_card_three hF
  have hSpZ := SpL.isPGroup_center_statedSp (n := 2) hF
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hρ⟩ := hgen ρ
  have hσ := Q3MFO4.ringEquiv_eq_refl hF σ
  subst hσ
  have hσ1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
  interval_cases ε
  ·
    have hρ' : ρ = conjAut 4 F A := by rw [hρ, hσ1, pow_zero, mul_one, mul_one]
    subst hρ'
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num : 3 ≤ 4) (A * A) 1
      (by rw [map_mul, hρ2, map_one, mul_one])
    have hcm : ((A * A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (c : F) • (1 : Matrix (Fin 4) (Fin 4) F) := by
      rw [← hc, smul_one_eq_diagonal]
      rfl
    rcases Q3MFOD.cases_of_card_three hF (c : F) with h0 | h1 | h1
    · exact absurd h0 c.ne_zero
    ·
      have hAA : A * A = 1 := by
        apply Units.ext
        rw [hcm, h1, one_smul, Units.val_one]
      by_cases hD : conjSLAut A = 1
      · exfalso
        apply hout
        have hone : conjAut 4 F A = 1 := by
          ext x
          obtain ⟨g, rfl⟩ := proj_surjective 4 F x
          rw [conjAut_proj, MulAut.one_apply]
          congr 1
          apply Subtype.ext
          have h := congrArg (fun φ : MulAut SL(4, F) => (φ g : Matrix (Fin 4) (Fin 4) F)) hD
          simp only [conjSLAut_coe, MulAut.one_apply] at h
          rw [coe_slConjugation]
          exact h
        rw [hone]
        exact one_mem _
      · have h := oddCoreIn_fixed_conjInvol_eq_bot hF A hAA hD
        have h' := oddCoreIn_fixed_congr_eq_bot' (Q3MFO4.projEquiv (F := F)).symm _ h
        rwa [Q3MFO4.congr_conjAut] at h'
    ·
      exfalso
      apply hout
      have hAA : (A : Matrix (Fin 4) (Fin 4) F) * A = -1 := by
        rw [← Units.val_mul, hcm, h1, neg_one_smul]
      have hdet := det_eq_one_of_mul_self_eq_neg_one hF hAA
      set s : SL(4, F) := ⟨A, hdet⟩ with hs
      refine ⟨proj 4 F s, MulEquiv.ext fun x => ?_⟩
      obtain ⟨g, rfl⟩ := proj_surjective 4 F x
      rw [MulAut.conj_apply, conjAut_proj, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv]
      have hinv : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          adjugate (A : Matrix (Fin 4) (Fin 4) F) := by
        rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
      rw [hinv]
  ·
    have hρ' : ρ = conjAut 4 F A * dualAut 4 F := by rw [hρ, hσ1, pow_one, mul_one]
    subst hρ'
    have hsq : (conjAut 4 F A * fieldAut 4 F (RingEquiv.refl F) * dualAut 4 F) ^ 2 = 1 := by
      rw [hσ1, mul_one, sq]
      exact hρ2
    rw [sq_conjAut_fieldAut_dualAut] at hsq
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num : 3 ≤ 4) _ _ hsq
    have hmap : ∀ X : GL (Fin 4) F, ((GeneralLinearGroup.map
        ((RingEquiv.refl F : F ≃+* F) : F →+* F) X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          (X : Matrix (Fin 4) (Fin 4) F) := fun X => by
      ext i j
      rfl
    have hcm : (c : F) • (1 : Matrix (Fin 4) (Fin 4) F) =
        (A : Matrix (Fin 4) (Fin 4) F) *
          ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
      have h := congrArg (fun X : GL (Fin 4) F => (X : Matrix (Fin 4) (Fin 4) F)) hc
      rw [Units.val_mul, hmap, Matrix.GeneralLinearGroup.coe_inverseTranspose] at h
      rw [← h, smul_one_eq_diagonal]
      rfl
    have hNA : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
        (A : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one]
    have hA : (A : Matrix (Fin 4) (Fin 4) F) = (c : F) • (A : Matrix (Fin 4) (Fin 4) F)ᵀ := by
      calc (A : Matrix (Fin 4) (Fin 4) F)
          = (A : Matrix (Fin 4) (Fin 4) F) * (((A⁻¹ : GL (Fin 4) F) :
              Matrix (Fin 4) (Fin 4) F)ᵀ * (A : Matrix (Fin 4) (Fin 4) F)ᵀ) := by
            rw [hNA, Matrix.mul_one]
        _ = ((c : F) • (1 : Matrix (Fin 4) (Fin 4) F)) * (A : Matrix (Fin 4) (Fin 4) F)ᵀ := by
            rw [← Matrix.mul_assoc, ← hcm]
        _ = (c : F) • (A : Matrix (Fin 4) (Fin 4) F)ᵀ := by
            rw [Matrix.smul_mul, Matrix.one_mul]
    rcases Q3MFOD.cases_of_card_three hF (c : F) with h0 | h1 | h1
    · exact absurd h0 c.ne_zero
    ·
      refine hB A ?_
      have := congrArg transpose hA
      rw [h1, one_smul, transpose_transpose] at this
      exact this
    ·
      have hAt : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A := by
        have := congrArg transpose hA
        rw [h1, transpose_smul, transpose_transpose, neg_one_smul] at this
        exact this
      obtain ⟨Q, hQ⟩ := exists_conj_spFormGL h2 hAt
      rw [hQ]
      exact oddCoreIn_fixed_conj_eq_bot _ _ (Q3MFO4.oddCoreIn_fixed_graph hF one_ne_zero
        one_ne_zero (spFormGL F) coe_spFormGL hSp hSpZ)

end Outer

section Model


theorem outerFixedOddFree_psl4_of (hB : PSLSymStatement (GaloisField 3 1)) :
    OuterFixedOddFree .PSL 4 := by
  intro S _ _ _ hS σ hσ hout
  have hFT : IsFundTag StatedLieTag.PSL := trivial
  have hadm : StatedLieAdmissible .PSL 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover _ 4 3 1 Nat.prime_three (by norm_num) hFT hadm S hS
  obtain ⟨hSq, -, -, -, -⟩ := Q3NM.centralQuotientData Nat.prime_three hFT hadm S ψ hψ hker
  have hZ := center_eq_bot_of_isQuasisimple hSq
  have : Group.IsPerfect (modelUniv .PSL 4 3 1 Nat.prime_three).K :=
    ⟨((ModelFacts.modelClauseZero .PSL 4 3 1 Nat.prime_three hFT hadm).1).1⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : Nat.card (GaloisField 3 1) = 3 := by simpa using GaloisField.card 3 1 one_ne_zero
  have hadmSp : StatedLieAdmissible .PSp 2 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  have hSp : CFSG.Open.IsQuasisimple (StatedSp 2 (GaloisField 3 1)) :=
    (ModelFacts.modelClauseZero .PSp 2 3 1 Nat.prime_three trivial hadmSp).1
  let e : S ≃* projectiveSL 4 (GaloisField 3 1) :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (Q3NM.centralQuotientIso ψ hψ hker).symm).trans (Q3MFO4.projEquiv (F := GaloisField 3 1)).symm
  have hρ2 : MulAut.congr e σ * MulAut.congr e σ = 1 := by rw [← map_mul, hσ, map_one]
  have hρout : MulAut.congr e σ ∉ innSubgroup (projectiveSL 4 (GaloisField 3 1)) := by
    rintro ⟨y, hy⟩
    apply hout
    refine ⟨e.symm y, MulEquiv.ext fun x => ?_⟩
    have h1 := congrArg (fun φ => φ (e x)) hy
    simp only [MulAut.conj_apply, MulAut.congr_apply] at h1
    rw [MulAut.conj_apply]
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]
    simp
  have h1 := Q3NM.oddCoreIn_fixed_congr_eq_bot' e.symm (MulAut.congr e σ)
    (oddCoreIn_fixed_of_outer_psl4 hF hB hSp _ hρ2 hρout)
  have h2 : MulAut.congr e.symm (MulAut.congr e σ) = σ := by
    ext x
    simp [MulAut.congr_apply]
  rwa [h2] at h1

end Model

end CFSG.ClassicalInvolution.Q3.TL4.L4
