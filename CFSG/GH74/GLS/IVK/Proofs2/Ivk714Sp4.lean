module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Tr
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Sp4Aux
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TCClass

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4
open scoped MatrixGroups

theorem sp4_eight_dvd {n : ℕ} (hn : Odd n) : 8 ∣ n ^ 2 - 1 := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨c, hc⟩ := Nat.even_mul_succ_self m
  have e : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by
    have : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    omega
  rw [e, hc]
  exact ⟨c, by ring⟩

theorem sp4_sixteen_dvd {n : ℕ} (hn : Odd n) : 16 ∣ n ^ 4 - 1 := by
  have h8 := sp4_eight_dvd hn
  have hsq : Odd (n ^ 2) := hn.pow
  obtain ⟨m, hm⟩ := hsq
  have h1 : 1 ≤ n ^ 2 := by omega
  have e : n ^ 4 - 1 = (n ^ 2 - 1) * (n ^ 2 + 1) := by
    have : n ^ 4 = n ^ 2 * n ^ 2 := by ring
    rw [this]
    zify [h1, show 1 ≤ n ^ 2 * n ^ 2 from Nat.one_le_iff_ne_zero.mpr (by positivity)]
    ring
  rw [e]
  have h2 : 2 ∣ n ^ 2 + 1 := ⟨m + 1, by omega⟩
  exact (Nat.mul_dvd_mul h8 h2 : 8 * 2 ∣ (n ^ 2 - 1) * (n ^ 2 + 1))

theorem sp4_dvd_field_card {k : ℕ} (hk : Odd k) :
    128 ∣ k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) :=
  Dvd.dvd.mul_left (Nat.mul_dvd_mul (sp4_eight_dvd hk) (sp4_sixteen_dvd hk) :
    8 * 16 ∣ (k ^ 2 - 1) * (k ^ 4 - 1)) _

variable {F : Type} [Field F]

theorem ivk714_sp4_core [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card F = p ^ f) (h5 : 5 ≤ p ^ f)
    (hs : IsSimpleGroup (StatedProj (StatedSp 2 F)))
    (α : MulAut (StatedProj (StatedSp 2 F))) (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {J : Subgroup (StatedProj (StatedSp 2 F))} (hJX : J ≤ fixOf α)
    (hJ : CFSG.IsPComponent 2 (J.subgroupOf (fixOf α)))
    (τ : ↥J →* alternatingGroup (Fin 7)) (hτ : Function.Surjective τ)
    (o : ℕ) (ho : Odd o) (hJcard : Nat.card J = 2520 * o) : False := by
  have hodd : Odd (Nat.card F) := odd_card_of_card_eq hp hp2 hK
  have hqodd : Odd (p ^ f) := hK ▸ hodd
  have h2 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card F := by omega
  have h5F : 5 ≤ Nat.card F := by omega
  have hchar : ringChar F ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := F)
    rw [h] at this
    exact_mod_cast this
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, hlin, hfield⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar le_rfl).2.2 α hα2 hα1
  by_cases hσ : σ = 1
  · subst hσ
    have hα' : α = conjAut 2 F A := by rw [hα, map_one, mul_one]
    set Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hAm
    have hAA : Am * Am = (d : F) • 1 := by
      have h1 := congrArg (fun M : GL (Fin 2 ⊕ Fin 2) F =>
        (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hd
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
      have h1' : ((CatalogueBHigherLinearField.glFieldEquiv (Fin 2 ⊕ Fin 2) (1 : F ≃+* F)
          (A : GL (Fin 2 ⊕ Fin 2) F) : GL (Fin 2 ⊕ Fin 2) F) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = Am := by
        ext i j
        rfl
      rw [h1'] at h1
      rw [h1, Matrix.smul_one_eq_diagonal]
      rfl
    set μ := multiplierUnit A with hμdef
    have hμ : Amᵀ * formJ 2 F * Am = (μ : F) • formJ 2 F := multiplierUnit_spec A
    have hdμ : (d : F) = μ ∨ (d : F) = -μ := by
      have e1 : (Am * Am)ᵀ * formJ 2 F * (Am * Am) = ((μ : F) * μ) • formJ 2 F := by
        rw [transpose_mul, show Amᵀ * Amᵀ * formJ 2 F * (Am * Am) =
          Amᵀ * (Amᵀ * formJ 2 F * Am) * Am by simp only [Matrix.mul_assoc], hμ,
          Matrix.mul_smul, Matrix.smul_mul, hμ, smul_smul]
      rw [hAA, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_smul, Matrix.mul_one, smul_smul] at e1
      exact mul_self_eq_mul_self_iff.mp (smul_formJ_injective 2 e1)
    by_cases hsq : ∃ l : F, l ^ 2 = (μ : F)
    ·
      obtain ⟨l, hl⟩ := hsq
      have hl0 : l ≠ 0 := by
        rintro rfl
        rw [zero_pow two_ne_zero] at hl
        exact μ.ne_zero hl.symm
      have hA'sp : (l⁻¹ • Am)ᵀ * formJ 2 F * (l⁻¹ • Am) = formJ 2 F := by
        rw [transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hμ, smul_smul,
          smul_smul, ← hl]
        rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
      set A' : StatedSp 2 F := toSp (l⁻¹ • Am) hA'sp with hA'def
      have hAz : (A : GL (Fin 2 ⊕ Fin 2) F) =
          GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 l hl0) *
            (A' : GL (Fin 2 ⊕ Fin 2) F) := by
        apply Units.ext
        rw [Units.val_mul, GeneralLinearGroup.coe_scalar, hA'def, coe_toSp, Units.val_mk0,
          Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
          Matrix.one_mul, smul_smul, mul_inv_cancel₀ hl0, one_smul]
      have hαu : α = MulAut.conj (proj 2 F A') :=
        hα'.trans (conjAut_eq_conj_of_scalar_mul A _ A' hAz)
      set u := proj 2 F A' with hudef
      have hu1 : u ≠ 1 := fun h => hα1 (by rw [hαu, h, map_one])
      have hu2 : u * u = 1 := by
        have hc : MulAut.conj (u * u) = 1 := by rw [map_mul, ← hαu, hα2]
        apply eq_one_of_mem_center_P h2 h4 hs
        rw [mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 F)) => φ g) hc
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
      let ψ : ↥J ≃* ↥(J.map φ.toMonoidHom) := J.equivMapOfInjective _ φ.injective
      rcases hφ with h | h
      · rw [h] at hJ0X hJ0
        obtain ⟨hE, -⟩ := pComponent_centralizer_u1 hodd hJ0X hJ0
        rcases hE with hE | hE
        · exact false_of_surjective_sl2 hodd h5F τ hτ
            (((E1Equiv h2).trans ((MulEquiv.subgroupCongr hE.symm).trans ψ.symm)).toMonoidHom)
            (MulEquiv.surjective _)
        · exact false_of_surjective_sl2 hodd h5F τ hτ
            (((E2Equiv h2).trans ((MulEquiv.subgroupCongr hE.symm).trans ψ.symm)).toMonoidHom)
            (MulEquiv.surjective _)
      · rw [h] at hJ0X hJ0
        obtain ⟨hL, -⟩ := pComponent_centralizer_u2 hodd hJ0X hJ0
        let eL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* ↥J :=
          ((LEquiv F).trans ((MulEquiv.subgroupCongr hL.symm).trans ψ.symm))
        exact false_of_surjective_sl2 hodd h5F τ hτ
          (eL.toMonoidHom.comp (QuotientGroup.mk' (center SL(2, F))))
          (eL.surjective.comp (QuotientGroup.mk'_surjective _))
    · push Not at hsq
      rcases hdμ with hdm | hdm
      ·
        have hdsq : ∀ l : F, l ^ 2 ≠ (d : F) := by rw [hdm]; exact hsq
        have hμd : Amᵀ * formJ 2 F * Am = (d : F) • formJ 2 F := by rw [hdm]; exact hμ
        obtain ⟨hQ, -⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A d.ne_zero hdsq hAA hμd
        obtain ⟨E, _, _, hEcard, ⟨eSL⟩⟩ :=
          ivk714_fixOf_conjSp_nonsquare_sl2 hp hp2 hf hK A d.ne_zero hdsq hAA hμd
        have hθα : ∀ g, α (proj 2 F g) = proj 2 F (conjSp 2 F A g) := fun g => by
          rw [hα', conjAut_proj]
        have hJeq := eq_map_fixOf_of_isPComponent (conjSp 2 F A) hθα hQ hJX hJ
        have hEodd : Odd (Nat.card E) := by rw [hEcard]; exact hqodd.pow
        have hE5 : 5 ≤ Nat.card E := by rw [hEcard]; nlinarith
        exact false_of_surjective_sl2 hEodd hE5 τ hτ
          ((MulEquiv.subgroupCongr hJeq.symm).toMonoidHom.comp
            (((proj 2 F).subgroupMap (fixOf (conjSp 2 F A))).comp eSL.symm.toMonoidHom))
          ((MulEquiv.subgroupCongr hJeq.symm).surjective.comp
            (((proj 2 F).subgroupMap_surjective (fixOf (conjSp 2 F A))).comp eSL.symm.surjective))
      ·
        have ha : (d : F) ≠ 0 := d.ne_zero
        have hA : Amᵀ * formJ 2 F * Am = (-(d : F)) • formJ 2 F := by
          rw [hμ, hdm, neg_neg]
        obtain ⟨g, hg⟩ := exists_frame_typeI h2 ha hA hAA
        have hGL : (A : GL (Fin 2 ⊕ Fin 2) F) * (g : GL (Fin 2 ⊕ Fin 2) F) =
            (g : GL (Fin 2 ⊕ Fin 2) F) * ((aIgsp ha : gsp 2 F) : GL (Fin 2 ⊕ Fin 2) F) := by
          apply Units.ext
          rw [Units.val_mul, Units.val_mul, coe_aIgsp]
          exact hg
        have hcomm : ∀ x, (MulAut.conj (proj 2 F g))⁻¹ (α x) =
            alphaI ha ((MulAut.conj (proj 2 F g))⁻¹ x) := fun x => by
          rw [hα']
          exact conj_inv_conjAut A (aIgsp ha) g hGL x
        obtain ⟨hJ0X, hJ0⟩ := isPComponent_map_fixOf hcomm hJX hJ
        have hJI := pComponent_fix_alphaI ha h2 h4 hJ0X hJ0
        let ψ : ↥J ≃* ↥(J.map (MulAut.conj (proj 2 F g))⁻¹.toMonoidHom) :=
          J.equivMapOfInjective _ (MulAut.conj (proj 2 F g))⁻¹.injective
        let eL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* ↥J :=
          ((JIEquiv ha).trans ((MulEquiv.subgroupCongr hJI.symm).trans ψ.symm))
        exact false_of_surjective_sl2 hodd h5F τ hτ
          (eL.toMonoidHom.comp (QuotientGroup.mk' (center SL(2, F))))
          (eL.surjective.comp (QuotientGroup.mk'_surjective _))
  ·
    have hθα : ∀ g, α (proj 2 F g) = proj 2 F ((conjSp 2 F A * fieldSp 2 F σ) g) := fun g => by
      rw [hα]
      rfl
    obtain ⟨hQ, hcard⟩ := fixOf_conjSp_fieldSp hodd A σ hσ2 hσ d hd
    have hJeq := eq_map_fixOf_of_isPComponent _ hθα hQ hJX hJ
    have h2c := card_map_fixOf_mul_two h2 (conjSp 2 F A * fieldSp 2 F σ)
      fun z hz => conjSp_fieldSp_scalar A σ hz
    rw [← hJeq, hcard, hJcard] at h2c
    have hkodd := CatalogueBOrthogonalFieldFixed.subfield_card_odd hodd
      (CatalogueBLinearTwoDescent.fixedSubfield F σ)
    have h128 := sp4_dvd_field_card hkodd
    rw [← h2c] at h128
    obtain ⟨m, rfl⟩ := ho
    omega

theorem ivk714_sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk714Empty (fun X _ => Blueprint.LieModel X .PSp 2 p f) := by
  intro p f hp hp2 hf K _ _ hs hK z hz h
  obtain ⟨-, -, F, _, _, hF, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hK
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq3 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by omega) p)
  by_cases hq : p ^ f = 3
  ·
    have hcard := two_mul_card_of_lieModel_psp hp2 hK
    rw [hq] at hcard
    norm_num at hcard
    have hd := h.two_five_two_zero_dvd.trans (Subgroup.card_subgroup_dvd_card (fixedSubgroup K z))
    omega
  · have h5 : 5 ≤ p ^ f := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hz2 : z * z = 1 := by
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hz])
    have hz1 : z ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hz
      omega
    let α : MulAut (StatedProj (StatedSp 2 F)) := e₀.symm.trans (z.trans e₀)
    have hα : ∀ s, e₀ (z s) = α (e₀ s) := fun s => by simp [α]
    have hα2 : α * α = 1 := by
      ext x
      simp only [MulAut.mul_apply, MulAut.one_apply, α, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
      have := congrArg (fun φ : MulAut K => φ (e₀.symm x)) hz2
      simp only [MulAut.mul_apply, MulAut.one_apply] at this
      rw [this, MulEquiv.apply_symm_apply]
    have hα1 : α ≠ 1 := by
      intro h1
      apply hz1
      ext s
      have := hα s
      rw [h1, MulAut.one_apply] at this
      simpa using e₀.injective this
    have hsP : IsSimpleGroup (StatedProj (StatedSp 2 F)) := by
      have := hs
      exact e₀.symm.isSimpleGroup
    obtain ⟨J, hJX, hJ, ⟨τ, hτ⟩, o, ho, hJcard⟩ := h.exists_two_component e₀ hα
    exact ivk714_sp4_core hp hp2 hf hF h5 hsP α hα2 hα1 hJX hJ τ hτ o ho hJcard

end CFSG.GH74.GLS.IVK.Proofs2
