module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TCClass

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.P211

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup CFSG.ComponentClassification.CatFactsSp4

variable {K : Type} [Field K]

theorem derivedSeries_two_le_PSp [Finite K] (hodd : ringChar K ≠ 2) :
    derivedSeries (MulAut (StatedProj (StatedSp 2 K))) 2 ≤
      (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range := by
  have hE : spSemilinearAutGroup 2 K = ⊤ := by
    rw [eq_top_iff]
    intro α _
    obtain ⟨A, σ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hodd le_rfl α
    exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
      (fieldAut_mem_spSemilinearAutGroup σ)
  have h := (standard_outer_quotient (K := K) (r := 2) (by norm_num)).2.2.2.2.2
  rw [hE] at h
  simpa only [derivedSeries_succ, derivedSeries_zero] using h

theorem card_PSL2_dvd [Finite K] :
    Nat.card (ProjectiveSpecialLinearGroup (Fin 2) K) ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [← card_SL2]
  exact Subgroup.card_quotient_dvd_card _

theorem card_dvd_of_pComponent {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    (hs : IsSimpleGroup (StatedProj (StatedSp 2 K)))
    (α : MulAut (StatedProj (StatedSp 2 K))) (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {J : Subgroup (StatedProj (StatedSp 2 K))} (hJX : J ≤ fixOf α)
    (hJ : CFSG.IsPComponent 2 (J.subgroupOf (fixOf α))) :
    Nat.card J ∣ p ^ f * ((p ^ f) ^ 2 - 1) ∨
      Nat.card J ∣ (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) ∨
      ∃ k : ℕ, k ^ 2 = p ^ f ∧ Nat.card J ∣ k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  have hchar : ringChar K ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, -, hfield⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar le_rfl).2.2 α hα2 hα1
  by_cases hσ : σ = 1
  · subst hσ
    have hα' : α = conjAut 2 K A := by rw [hα, map_one, mul_one]
    set Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hAm
    have hAA : Am * Am = (d : K) • 1 := by
      have h1 := congrArg (fun M : GL (Fin 2 ⊕ Fin 2) K =>
        (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hd
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
      have h1' : ((CatalogueBHigherLinearField.glFieldEquiv (Fin 2 ⊕ Fin 2) (1 : K ≃+* K)
          (A : GL (Fin 2 ⊕ Fin 2) K) : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = Am := by
        ext i j
        rfl
      rw [h1'] at h1
      rw [h1, Matrix.smul_one_eq_diagonal]
      rfl
    set μ := multiplierUnit A with hμdef
    have hμ : Amᵀ * formJ 2 K * Am = (μ : K) • formJ 2 K := multiplierUnit_spec A
    have hdμ : (d : K) = μ ∨ (d : K) = -μ := by
      have e1 : (Am * Am)ᵀ * formJ 2 K * (Am * Am) = ((μ : K) * μ) • formJ 2 K := by
        rw [transpose_mul, show Amᵀ * Amᵀ * formJ 2 K * (Am * Am) =
          Amᵀ * (Amᵀ * formJ 2 K * Am) * Am by simp only [Matrix.mul_assoc], hμ,
          Matrix.mul_smul, Matrix.smul_mul, hμ, smul_smul]
      rw [hAA, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_smul, Matrix.mul_one, smul_smul] at e1
      exact mul_self_eq_mul_self_iff.mp (smul_formJ_injective 2 e1)
    by_cases hsq : ∃ l : K, l ^ 2 = (μ : K)
    ·
      obtain ⟨l, hl⟩ := hsq
      have hl0 : l ≠ 0 := by
        rintro rfl
        rw [zero_pow two_ne_zero] at hl
        exact μ.ne_zero hl.symm
      have hA'sp : (l⁻¹ • Am)ᵀ * formJ 2 K * (l⁻¹ • Am) = formJ 2 K := by
        rw [transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hμ, smul_smul,
          smul_smul, ← hl]
        rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
      set A' : StatedSp 2 K := toSp (l⁻¹ • Am) hA'sp with hA'def
      have hAz : (A : GL (Fin 2 ⊕ Fin 2) K) =
          GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 l hl0) *
            (A' : GL (Fin 2 ⊕ Fin 2) K) := by
        apply Units.ext
        rw [Units.val_mul, GeneralLinearGroup.coe_scalar, hA'def, coe_toSp, Units.val_mk0,
          Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
          Matrix.one_mul, smul_smul, mul_inv_cancel₀ hl0, one_smul]
      have hαu : α = MulAut.conj (proj 2 K A') :=
        hα'.trans (conjAut_eq_conj_of_scalar_mul A _ A' hAz)
      set u := proj 2 K A' with hudef
      have hu1 : u ≠ 1 := fun h => hα1 (by rw [hαu, h, map_one])
      have hu2 : u * u = 1 := by
        have hc : MulAut.conj (u * u) = 1 := by rw [map_mul, ← hαu, hα2]
        apply eq_one_of_mem_center_P h2 h4 hs
        rw [mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 K)) => φ g) hc
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * (u * u) = u * u * g * (u * u)⁻¹ * (u * u) := by rw [this]
          _ = u * u * g := by group
      have hu : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
      obtain ⟨φ, hφ⟩ := exists_model_conj hodd hu
      have hcomm : ∀ x, φ (α x) = MulAut.conj (φ u) (φ x) := fun x => by
        rw [hαu]
        exact conj_comm φ u x
      obtain ⟨hJ0X, hJ0⟩ := isPComponent_map_fixOf hcomm hJX hJ
      rw [fixOf_conj] at hJ0X hJ0
      have hcardJ : Nat.card (J.map φ.toMonoidHom) = Nat.card J :=
        (Nat.card_congr (J.equivMapOfInjective _ φ.injective).toEquiv).symm
      left
      rcases hφ with h | h
      · rw [h] at hJ0X hJ0
        obtain ⟨hE, -⟩ := pComponent_centralizer_u1 hodd hJ0X hJ0
        rw [← hK]
        rcases hE with hE | hE
        · rw [← hcardJ, hE, ← Nat.card_congr (E1Equiv h2).toEquiv, card_SL2]
        · rw [← hcardJ, hE, ← Nat.card_congr (E2Equiv h2).toEquiv, card_SL2]
      · rw [h] at hJ0X hJ0
        obtain ⟨hL, -⟩ := pComponent_centralizer_u2 hodd hJ0X hJ0
        rw [← hK, ← hcardJ, hL, ← Nat.card_congr (LEquiv K).toEquiv]
        exact card_PSL2_dvd
    · push Not at hsq
      rcases hdμ with hdm | hdm
      ·
        have hdsq : ∀ l : K, l ^ 2 ≠ (d : K) := by rw [hdm]; exact hsq
        have hμd : Amᵀ * formJ 2 K * Am = (d : K) • formJ 2 K := by rw [hdm]; exact hμ
        obtain ⟨hQ, hcard⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A d.ne_zero hdsq hAA hμd
        have hθα : ∀ g, α (proj 2 K g) = proj 2 K (conjSp 2 K A g) := fun g => by
          rw [hα', conjAut_proj]
        have hJeq := eq_map_fixOf_of_isPComponent (conjSp 2 K A) hθα hQ hJX hJ
        have h2c := card_map_fixOf_mul_two h2 (conjSp 2 K A) fun z hz => conjSp_scalar A hz
        rw [← hJeq, hcard] at h2c
        exact Or.inr (Or.inl (Dvd.intro _ h2c))
      ·
        have ha : (d : K) ≠ 0 := d.ne_zero
        have hA : Amᵀ * formJ 2 K * Am = (-(d : K)) • formJ 2 K := by
          rw [hμ, hdm, neg_neg]
        obtain ⟨g, hg⟩ := exists_frame_typeI h2 ha hA hAA
        have hGL : (A : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) =
            (g : GL (Fin 2 ⊕ Fin 2) K) * ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
          apply Units.ext
          rw [Units.val_mul, Units.val_mul, coe_aIgsp]
          exact hg
        have hcomm : ∀ x, (MulAut.conj (proj 2 K g))⁻¹ (α x) =
            alphaI ha ((MulAut.conj (proj 2 K g))⁻¹ x) := fun x => by
          rw [hα']
          exact conj_inv_conjAut A (aIgsp ha) g hGL x
        obtain ⟨hJ0X, hJ0⟩ := isPComponent_map_fixOf hcomm hJX hJ
        have hJI := pComponent_fix_alphaI ha h2 h4 hJ0X hJ0
        have hcardJ : Nat.card (J.map ((MulAut.conj (proj 2 K g))⁻¹ :
            StatedProj (StatedSp 2 K) ≃* StatedProj (StatedSp 2 K)).toMonoidHom) = Nat.card J :=
          (Nat.card_congr (J.equivMapOfInjective _ (MulEquiv.injective _)).toEquiv).symm
        left
        rw [← hK, ← hcardJ, hJI, ← Nat.card_congr (JIEquiv ha).toEquiv]
        exact card_PSL2_dvd
  ·
    have hθα : ∀ g, α (proj 2 K g) = proj 2 K ((conjSp 2 K A * fieldSp 2 K σ) g) := fun g => by
      rw [hα]
      rfl
    obtain ⟨hQ, hcard⟩ := fixOf_conjSp_fieldSp hodd A σ hσ2 hσ d hd
    have hJeq := eq_map_fixOf_of_isPComponent _ hθα hQ hJX hJ
    have h2c := card_map_fixOf_mul_two h2 (conjSp 2 K A * fieldSp 2 K σ)
      fun z hz => conjSp_fieldSp_scalar A σ hz
    rw [← hJeq, hcard] at h2c
    obtain ⟨hKk, -⟩ := hfield hσ
    have hk : Nat.card {c : K // σ c = c} =
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        (CatalogueBLinearTwoDescent.mem_fixedSubfield K σ c).symm)
    rw [hk, hK] at hKk
    exact Or.inr (Or.inr ⟨_, hKk.symm, Dvd.intro _ h2c⟩)

end CFSG.ComponentClassification.GSThmB.P211
