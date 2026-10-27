module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU3OutData
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3OrthF
public import CFSG.GH74.KGroups.L3EpsUniGraph

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank
  CFSG.GH74.KGroups.L3Eps.Uni
  CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonal
open scoped MatrixGroups commutatorElement

section Real

theorem adMat_neg_one {k : Type} [Field k] : adMat (-1 : SL(2, k)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adMat, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]

theorem sl2_perfect_of_five_le {k : Type} [Field k] [Finite k] (_hodd : Odd (Nat.card k))
    (h5 : 5 ≤ Nat.card k) : Group.IsPerfect SL(2, k) := by
  have hq := CatalogueBGeneralLinear.specialLinear_quasisimple 2 k le_rfl
    (Or.inr (by omega)) (Or.inr (by omega))
  exact hq.1

theorem outerData_of_typeII {ℓ f : ℕ} {F : Type} [Field F] [Finite F] (h : UnitaryFieldData ℓ f F)
    (hp : ℓ ≠ 2) (h3 : 3 ≤ ℓ ^ f) {K : Type} [Group K] {θ : ↥(unitarySU ℓ f F 3) →* K}
    (hθ : IsCover h θ) {σ : MulAut K} {φ : F ≃+* F} {A : GL (Fin 3) F} (hφ : ∀ c, φ c = h.bar c)
    (hAu : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1)
    (hAA : (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F).map h.bar = 1)
    (hrel : ∀ g : ↥(unitarySU ℓ f F 3), ∃ g' : ↥(unitarySU ℓ f F 3),
      (g' : GL (Fin 3) F) = A * glAut φ (g : GL (Fin 3) F) * A⁻¹ ∧ θ g' = σ (θ g)) :
    Nonempty (KAOuterData h θ σ) := by
  classical
  have hq : Odd (ℓ ^ f) := (h.prime.odd_of_ne_two hp).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_pow h hq
  obtain ⟨D⟩ := exists_realData h h2 hAu hAA
  have hkc : Nat.card ↥h.fixedField = ℓ ^ f := h.card_fixedField
  have hodd : Odd (Nat.card ↥h.fixedField) := hkc ▸ hq
  have h2k : (2 : ↥h.fixedField) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨ι, P, P', hPP', hP'P, hiso, hι, -⟩ := ad_param hodd D.G D.hGs
  have hmem : ∀ S, Matrix.SpecialLinearGroup.toGL (ι S) ∈ D.Iso1 := by
    intro S
    refine ⟨hiso S, ?_⟩
    show Matrix.SpecialLinearGroup.toGL (ι S) ∈
      (Matrix.GeneralLinearGroup.det : GL (Fin 3) ↥h.fixedField →* h.fixedFieldˣ).ker
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp
  let j : SL(2, ↥h.fixedField) →* ↥D.Iso1 :=
    ((Matrix.SpecialLinearGroup.toGL).comp ι).codRestrict D.Iso1 hmem
  let Ψ : SL(2, ↥h.fixedField) →* ↥(unitarySU ℓ f F 3) := D.Phi.comp j
  have hΨm : ∀ S, (((Ψ S : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      baseConj h.fixedField.subtype D.Pu (ι S : Matrix (Fin 3) (Fin 3) ↥h.fixedField) := by
    intro S
    show (((D.Pu * inclK h (Matrix.SpecialLinearGroup.toGL (ι S)) * D.Pu⁻¹ : GL (Fin 3) F)) :
      Matrix (Fin 3) (Fin 3) F) = _
    rw [Units.val_mul, Units.val_mul, coe_inclK]
    rfl
  refine ⟨⟨Ψ, ?_, ?_, ?_, ?_, ?_, hkc, ?_, ?_⟩⟩
  ·
    intro S
    obtain ⟨g', hg'GL, hg'θ⟩ := hrel (D.Phi (j S))
    have hgg : g' = D.Phi (j S) := Subtype.ext (by rw [hg'GL]; exact D.Phi_fixed hφ (j S))
    rw [hgg] at hg'θ
    exact hg'θ.symm
  ·
    intro W hW
    exact irreducible_of_param_F h.fixedField.subtype h2 hPP' hP'P hι D.Pu W
      (fun S v hv => by rw [← hΨm S]; exact hW S v hv)
  ·
    intro T hT
    exact commutant_of_param_F h.fixedField.subtype h2 hPP' hP'P hι D.Pu T
      (fun S => by rw [← hΨm S]; exact hT S)
  ·
    intro τ' hτ
    refine eq_one_or_bar_of_fixes h τ' (fun c hc => ?_)
    have hcm : c ∈ h.fixedField := (h.mem_fixedField).2 hc
    exact fixes_of_traces h.fixedField.subtype h2k hPP' hP'P hι D.Pu τ'
      (fun S => by rw [← hΨm S]; exact hτ S) ⟨c, hcm⟩
  ·
    by_cases h5 : 5 ≤ ℓ ^ f
    · apply centOK_of_perfect
      have hperf : Group.IsPerfect SL(2, ↥h.fixedField) :=
        sl2_perfect_of_five_le hodd (by rw [hkc]; exact h5)
      exact Group.IsPerfect.ofSurjective (f := Ψ.rangeRestrict) Ψ.rangeRestrict_surjective
    · have hq3 : ℓ ^ f = 3 := by
        obtain ⟨m, hm⟩ := hq
        omega
      apply centOK_of_no_cube_roots h
      intro c hc3
      have hcard : Nat.card F = 9 := by rw [h.card, pow_mul', hq3]; norm_num
      have : Fintype F := Fintype.ofFinite F
      have hc8 : c ^ 8 = 1 := by
        have h1 : c ^ Fintype.card Fˣ = 1 := pow_card_eq_one
        rwa [Fintype.card_units, ← Nat.card_eq_fintype_card, hcard] at h1
      have := pow_gcd_eq_one.2 ⟨hc3, hc8⟩
      simpa using this
  ·
    intro S hS
    have hθinj := D.injective_theta_Phi hθ
    have h1 : j S = 1 := by
      apply hθinj
      rw [map_one]
      exact hS
    have h2' : ι S = 1 := by
      have h3' : Matrix.SpecialLinearGroup.toGL (ι S) = 1 := congrArg Subtype.val h1
      exact Matrix.SpecialLinearGroup.toGL_injective (by rw [map_one]; exact h3')
    exact ker_of_param h2k hPP' hP'P hι S h2'
  ·
    have h1 : ι (-1) = 1 := by
      apply Subtype.ext
      rw [hι, adMat_neg_one, Matrix.mul_one, hP'P]
      rfl
    have h2' : j (-1) = 1 := by
      apply Subtype.ext
      show Matrix.SpecialLinearGroup.toGL (ι (-1)) = 1
      rw [h1, map_one]
    show D.Phi (j (-1)) = 1
    rw [h2', map_one]

end Real

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
