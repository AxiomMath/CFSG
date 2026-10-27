module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFFin

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Gauss

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped MatrixGroups

section Plane

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_ts_two {P P' : HypPair Q} (h : P.Orth P') :
    ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0 := by
  have hli : LinearIndependent K ![P.e, P'.e] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun z => polar Q z P.f) hst
    have h2 := congrArg (fun z => polar Q z P'.f) hst
    have hfe : polar Q P'.e P.f = 0 := by rw [polar_comm]; exact h.fe
    simp only [polar_add_left, polar_smul_left_eq, polar_zero_left, P.polar_ef, P'.polar_ef,
      h.ef, hfe, mul_one, mul_zero, add_zero, zero_add] at h1 h2
    exact ⟨h1, h2⟩
  refine ⟨Submodule.span K (Set.range ![P.e, P'.e]), ?_, ?_⟩
  · rw [finrank_span_eq_card hli]
    simp
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun K |>.mp hx
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, P.Q_e, P'.Q_e,
      polar_smul_left_eq, polar_smul_right_eq, h.ee]
    simp

end Plane

section Split

variable {F : Type} [Field F] [Finite F] [Fact (Nat.card F = 3)] {V : Type} [AddCommGroup V]
  [Module F V] [FiniteDimensional F V] [Module (GaussField F) V]
  [IsScalarTower F (GaussField F) V] {Q : QuadraticForm F V} {a : V ≃ₗ[F] V}

theorem oddCoreIn_fixed_conjES_of_split (hF : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank F V)
    (hE : elementaryGroup Q = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) (h4 : Module.finrank (GaussField F) V = 4)
    {P P' : HypPair (gaussQuad Q hω hg)} (hPP : P.Orth P') :
    oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q)
      (Q3MFOD.conjES Q hE (neg_ne_zero.mpr one_ne_zero) hg))) = ⊥ := by
  classical
  have := finiteDimensional_gauss F V
  have h2 : (2 : F) ≠ 0 := Q3MFOD.two_ne_zero_of_card_three hF
  have hμ : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hZ2 := isPGroup_center_elementaryGroup hF hQ hdim
  have hQq := nondegenerate_gaussQuad h2 hω hg hQ
  obtain ⟨S, hS2, hS0⟩ := exists_ts_two hPP
  obtain ⟨ψ, e, -, he, heS⟩ :=
    split_four_determinant_form_isometry (gaussQuad Q hω hg) hQq h4 S hS2 hS0
  set θ : DeterminantIsometries (GaussField F) →* (V ≃ₗ[GaussField F] V) :=
    (TauCeti.QuadraticMap.orthogonalGroup (gaussQuad Q hω hg)).subtype.comp
      e.symm.toMonoidHom with hθ
  have hθO : ∀ d, θ d ∈ TauCeti.QuadraticMap.orthogonalGroup (gaussQuad Q hω hg) :=
    fun d => (e.symm d).2
  have hθe : ∀ g : TauCeti.QuadraticMap.orthogonalGroup (gaussQuad Q hω hg),
      θ (e g) = g := fun g => by
    show ((e.symm (e g) : TauCeti.QuadraticMap.orthogonalGroup (gaussQuad Q hω hg)) :
      V ≃ₗ[GaussField F] V) = g
    rw [MulEquiv.symm_apply_apply]
  have hval : ∀ d (X : Matrix (Fin 2) (Fin 2) (GaussField F)),
      d.val X = ψ (θ d (ψ.symm X)) := fun d X => by
    have h1 := he (e.symm d) X
    rwa [MulEquiv.apply_symm_apply] at h1
  set φ : SL(2, GaussField F) × SL(2, GaussField F) →* (V ≃ₗ[F] V) :=
    (res F).comp (θ.comp specialRho) with hφ
  have hφapp : ∀ z, φ z = res F (θ (specialRho z)) := fun z => rfl
  have hφO : ∀ z, φ z ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun z => res_mem_orthogonalGroup h2 hω hg (hθO _)
  have : Group.IsPerfect SL(2, GaussField F) := ⟨(SpL.isQuasisimple_SL2_gauss).1⟩
  have hperf : ∀ φ₁ : SL(2, GaussField F) →* (V ≃ₗ[F] V),
      (∀ z, φ₁ z ∈ TauCeti.QuadraticMap.orthogonalGroup Q) →
        ∀ z, φ₁ z ∈ elementaryGroup Q := by
    intro φ₁ hφ₁ z
    have hp : ⁅φ₁.range, φ₁.range⁆ = φ₁.range :=
      Subgroup.isPerfect_iff.mp (Group.IsPerfect.range φ₁)
    have hle : φ₁.range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rintro _ ⟨y, rfl⟩
      exact hφ₁ y
    rw [hE]
    have h5 : φ₁.range ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
      calc φ₁.range = ⁅φ₁.range, φ₁.range⁆ := hp.symm
        _ ≤ _ := Subgroup.commutator_mono hle hle
    exact h5 ⟨z, rfl⟩
  have hφE : ∀ z, φ z ∈ elementaryGroup Q := by
    intro z
    have hz : z = (z.1, 1) * (1, z.2) := by ext <;> simp
    rw [hz, map_mul]
    exact mul_mem (hperf (φ.comp (MonoidHom.inl _ _)) (fun y => hφO _) z.1)
      (hperf (φ.comp (MonoidHom.inr _ _)) (fun y => hφO _) z.2)
  set β₀ : SL(2, GaussField F) × SL(2, GaussField F) →* ↥(elementaryGroup Q) :=
    φ.codRestrict _ hφE with hβ₀
  have hβ₀app : ∀ z, ((β₀ z : ↥(elementaryGroup Q)) : V ≃ₗ[F] V) = φ z := fun z => rfl
  set σ := Q3MFOD.conjES Q hE hμ hg with hσ
  set β : SL(2, GaussField F) × SL(2, GaussField F) →*
      ↥(elementaryGroup Q) ⧸ Subgroup.center ↥(elementaryGroup Q) :=
    (QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup Q))).comp β₀ with hβ
  have hβσ : ∀ z, σ (β₀ z) = β₀ z := by
    intro z
    have h := (Q3MFOD.mem_fixedSubgroup_conjES hE hμ hg (β₀ z)).mpr (by
      rw [hβ₀app, hφapp]
      exact res_mul_a hω _)
    exact h
  have hβC : β.range ≤ fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q) σ) := by
    rintro _ ⟨z, rfl⟩
    rw [Q3NM.mem_fixedSubgroup_iff]
    show autToCentralQuotient ↥(elementaryGroup Q) σ (QuotientGroup.mk (β₀ z)) =
      QuotientGroup.mk (β₀ z)
    rw [autToCentralQuotient_mk, hβσ]
  have hNR : oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q) σ)) ≤
      β.range := by
    intro n hn
    have hnC := oddCoreIn_le _ hn
    have hm : Odd (orderOf n) :=
      (odd_card_oddCoreIn _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hn)
    obtain ⟨ν, hνn, hνm, hσν⟩ := exists_fixed_oddLift hZ2 σ hnC hm (pow_orderOf_eq_one n)
    have hνc : (ν : V ≃ₗ[F] V) * a = a * ν :=
      (Q3MFOD.mem_fixedSubgroup_conjES hE hμ hg ν).mp hσν
    obtain ⟨g, hgO, hgν⟩ :=
      exists_gauss_of_commute hω hg (elementaryGroup_le_orthogonalGroup Q ν.2) hνc
    obtain ⟨z, hz⟩ := CFSG.LocalAnalysis.ComponentInitial.determinant_sq_mem_specialImage
      (e ⟨g, hgO⟩)
    have hθz : θ (specialRho z) = g * g := by
      rw [hz, map_pow, hθe, pow_two]
    have hβ₀z : β₀ z = ν * ν := by
      apply Subtype.ext
      rw [hβ₀app, hφapp, hθz, map_mul, hgν, Subgroup.coe_mul]
    have hodd : Odd (orderOf ν) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hνm)
    obtain ⟨z', hz'⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.ka_odd_mem_of_sq_mem
      (R := β₀.range) ⟨z, hβ₀z⟩ hodd
    refine ⟨z', ?_⟩
    rw [← hνn, MonoidHom.comp_apply, hz']
    rfl
  have hker : ∀ x ∈ β.ker, x.1 ∈ Subgroup.center SL(2, GaussField F) ∧
      x.2 ∈ Subgroup.center SL(2, GaussField F) := by
    intro x hx
    have hx' : β₀ x ∈ Subgroup.center ↥(elementaryGroup Q) :=
      (QuotientGroup.eq_one_iff (β₀ x)).mp hx
    obtain ⟨c, hc⟩ := mem_scalars.mp (mem_scalars_of_mem_center hF hQ hdim hx')
    have hθc : ∀ v, θ (specialRho x) v = c • v := fun v => by
      have h1 := hc v
      rw [hβ₀app, hφapp, res_apply] at h1
      exact h1
    have hc0 : c ≠ 0 := by
      rintro rfl
      have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      apply hv
      apply (θ (specialRho x)).injective
      rw [hθc, zero_smul, map_zero]
    have hd : ∀ X : Matrix (Fin 2) (Fin 2) (GaussField F),
        (specialRho x).val X = (algebraMap F (GaussField F) c) • X := by
      intro X
      rw [hval, hθc, ← algebraMap_smul (GaussField F) c (ψ.symm X), map_smul,
        LinearEquiv.apply_symm_apply]
    have hμ' : algebraMap F (GaussField F) c ≠ 0 :=
      (map_ne_zero (algebraMap F (GaussField F))).mpr hc0
    exact CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.kaGO3S_center_of_sandwich hμ' fun X => by
      rw [← specialRho_apply]
      exact hd X
  exact CFSG.ComponentClassification.CatFactsL4U4.eq_bot_of_odd_block
    ⟨3, 2, Nat.prime_three, by decide, by norm_num, by rw [card_gaussField_eq_nine hF]; norm_num⟩
    β hker _ hNR (fun g hg r hr => conj_mem_oddCoreIn (hβC hg) hr) (odd_card_oddCoreIn _)

end Split

section Eight

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem oddCoreIn_fixed_conjES_of_sq_neg_one_eight (hF : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate)
    (hE : elementaryGroup Q = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {a : V ≃ₗ[F] V} (ha : ∀ v, a (a v) = -v) (hg : ∀ v, Q (a v) = (-1 : F) * Q v)
    (h8 : Module.finrank F V = 8) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q)
      (Q3MFOD.conjES Q hE (neg_ne_zero.mpr one_ne_zero) hg))) = ⊥ := by
  have : Fact (Nat.card F = 3) := ⟨hF⟩
  let _ : Module (GaussField F) V := gaussModule a ha
  have : IsScalarTower F (GaussField F) V := ⟨fun c z v => by
    show (c • z).re • v + (c • z).im • a v = c • (z.re • v + z.im • a v)
    rw [QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_add, smul_eq_mul, smul_eq_mul,
      mul_smul, mul_smul]⟩
  have hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v := fun v => by
    show (QuadraticAlgebra.omega : GaussField F).re • v +
      (QuadraticAlgebra.omega : GaussField F).im • a v = a v
    rw [QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, zero_smul, one_smul, zero_add]
  have h2 : (2 : F) ≠ 0 := Q3MFOD.two_ne_zero_of_card_three hF
  have hfr := finrank_gauss (F := F) (V := V)
  have h4 : Module.finrank (GaussField F) V = 4 := by omega
  by_cases hW : ∃ P P' : HypPair (gaussQuad Q hω hg), P.Orth P'
  · obtain ⟨P, P', hPP⟩ := hW
    exact oddCoreIn_fixed_conjES_of_split hF hQ (by omega) hE hω hg h4 hPP
  · have hodd : Odd (Nat.card (GaussField F)) := by rw [card_gaussField_eq_nine hF]; decide
    have h9 : 5 ≤ Nat.card (GaussField F) := by rw [card_gaussField_eq_nine hF]; norm_num
    have := finiteDimensional_gauss F V
    have hQq := nondegenerate_gaussQuad h2 hω hg hQ
    have hq : CFSG.Open.IsQuasisimple ↥(elementaryGroup (gaussQuad Q hω hg)) :=
      isQuasisimple_elementaryGroup_small hodd h9 hQq (by omega)
        (Or.inr fun P P' hPP => hW ⟨P, P', hPP⟩)
    exact oddCoreIn_fixed_conjES_of_gauss hF hQ (by omega) hE hω hg (by omega) hq

end Eight

end CFSG.ClassicalInvolution.Q3.TL4.Gauss

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

theorem d4CplxR_proved : D4CplxR := by
  intro hE a hg ha
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : Nat.card (GaloisField 3 1) = 3 := ModelFacts.TG3.natCard_galoisField_three
  exact Gauss.oddCoreIn_fixed_conjES_of_sq_neg_one_eight hF3
    (nondegenerate_polarBilin_quadPlus 4 (GaloisField 3 1)) hE ha hg finrank_d4


theorem omegaAutOddFreeR_of_outCent (hO : D4OutCentR) : OmegaAutOddFreeR :=
  omegaAutOddFreeR_of_d4 ⟨d4CplxR_proved, hO⟩

end CFSG.ClassicalInvolution.Q3.TL4
