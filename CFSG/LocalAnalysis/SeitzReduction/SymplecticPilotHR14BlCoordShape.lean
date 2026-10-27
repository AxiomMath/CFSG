module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlCoordCoset

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)
open CFSG.RankThree.OrthogonalInvolutions (commSpace)
open CFSG.RankThree.PartOne.AUTSL (reflMat reflMat_mem_isometries reflMat_mul_self comm_reflMat_iff
  mul_reflMat_mem_iff finrank_commSpace_reflMat reflMat_congr)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

@[expose] def OmegaBSpParamInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2]
    (Q : QuadraticForm K (Fin (2 * (n + 1)) → K)), Q.polarBilin.Nondegenerate →
    (∃ T : Submodule K (Fin (2 * (n + 1)) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) →
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q →
    ∀ (s : matrixIsometries Q), s * s = 1 → ∀ j : ℕ, 1 ≤ j →
      finrank K (commSpace (matrixLinearIso s.val)) = 2 * j + 1 →
    ∀ (w : Fin (2 * (n + 1)) → K) (hw : Q w ≠ 0), Q w = 1 →
      (∀ g : GL (Fin (2 * (n + 1))) K, g ∈ matrixIsometries Q → g * s.val = s.val * g →
        (g : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K) *ᵥ w = w) →
      ∃ φ : StatedSp n K →* GL (Fin (2 * (n + 1))) K, Function.Injective φ ∧
        (∀ x, φ x ∈ matrixDerived Q ∧ φ x * reflMat Q w hw = reflMat Q w hw * φ x) ∧
        (∀ g ∈ matrixDerived Q, g * reflMat Q w hw = reflMat Q w hw * g → ∃ x, φ x = g) ∧
        φ (spARep n j) = s.val * reflMat Q w hw

@[expose] def OmegaBFixedVectorInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2]
    (Q : QuadraticForm K (Fin (2 * (n + 1)) → K)), Q.polarBilin.Nondegenerate →
    (∃ T : Submodule K (Fin (2 * (n + 1)) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) →
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q →
    ∀ (s : matrixIsometries Q), s * s = 1 → ∀ j : ℕ, 1 ≤ j →
      finrank K (commSpace (matrixLinearIso s.val)) = 2 * j + 1 →
    ∀ (w : Fin (2 * (n + 1)) → K), Q w = 1 →
      (∀ g : GL (Fin (2 * (n + 1))) K, g ∈ matrixIsometries Q → g * s.val = s.val * g →
        (g : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K) *ᵥ w = w) →
      ∀ v : Fin (2 * (n + 1)) → K,
        (s.val : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K) *ᵥ v = v →
        (∀ g ∈ matrixDerived Q, g * s.val = s.val * g →
          (g : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K) *ᵥ v = v) →
        v ∈ K ∙ w

section Helpers

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem bCoord_two_mul_finrank_le [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    {s : matrixIsometries Q} (hs : s * s = 1) :
    2 * finrank K (commSpace (matrixLinearIso s.val)) ≤ d := by
  have hS : matrixLinearIso s.val ∈ TauCeti.QuadraticMap.orthogonalGroup Q := s.2
  have hSS := bCoord_mul_self_linear hs
  have hle : commSpace (matrixLinearIso s.val) ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q) (commSpace (matrixLinearIso s.val)) := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [polarBilin_apply_apply]
    exact polar_of_mem_omegaInvSpace hS hSS hy hx
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ, Module.finrank_fin_fun] at h1
  have h2 := Submodule.finrank_le (commSpace (matrixLinearIso s.val))
  rw [Module.finrank_fin_fun] at h2
  omega

theorem bCoord_mem_fixedSubgroup_iff [CharP K 2] (hQ0 : ∃ v, Q v ≠ 0) {X : Type*} [Group X]
    (ε : X ≃* matrixProjectiveDerived Q) {α : MulAut X} {γ : matrixIsometries Q}
    (hα : MulAut.congr ε α = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q γ))
    (A : matrixDerived Q) :
    ε.symm (matrixProjectiveProjection Q A) ∈ fixedSubgroup α ↔ γ.val * A.val = A.val * γ.val := by
  change α (ε.symm (matrixProjectiveProjection Q A)) = ε.symm (matrixProjectiveProjection Q A) ↔ _
  rw [bCoord_apply_symm, hα]
  constructor
  · intro h
    exact bCoord_commute_of_kappa_fix hQ0 γ A (ε.symm.injective h)
  · intro h
    rw [bCoord_kappa_fix_of_commute γ A h]

end Helpers

theorem bCoord_statedSpCongr_spARep {K K' : Type} [Field K] [Field K'] (σ : K ≃+* K') (n j : ℕ) :
    F4Pilot.statedSpCongr σ n (spARep n j) = spARep n j := by
  apply mat_injective
  have h : mat n K' (F4Pilot.statedSpCongr σ n (spARep n j)) = (mat n K (spARep n j)).map σ := rfl
  rw [h]
  ext a b
  rw [Matrix.map_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [spARep, mat_upperUnipotentSp, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply,
      spARepMat, Matrix.of_apply] <;> (try split_ifs) <;> simp

theorem spOmegaBShapeInputCoord_of_model (hM1 : OmegaBSpParamInput)
    (hM2 : OmegaBFixedVectorInput) (κ : Sp2mKind) : SpOmegaBShapeInputCoord κ := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob htN K' _ _ Q hK' hQ hT hE hImg ε
    hθt j hj g hg hB
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hd : 1 ≤ 2 * (n + 1) := by omega
  obtain ⟨σ⟩ : Nonempty (K ≃+* K') := by
    have := Fintype.ofFinite K
    have := Fintype.ofFinite K'
    exact ⟨FiniteField.ringEquivOfCardEq (K := K) (K' := K') (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKc, hK'])⟩
  obtain ⟨s₀, hs₀, hr₀, hθ⟩ :=
    bCoord_exists_refl (by omega) hK4 e ht hKt hglob htN hQ hT hImg ε hθt
  obtain ⟨β, s₁, hs₁, hr₁, hβ⟩ := hB
  obtain ⟨s, hs, hrs, hθs⟩ := bCoord_exists_kappa_of_conj hImg hs₁ hβ
  have hrank : finrank K' (commSpace (matrixLinearIso s.val)) = 2 * j + 1 := by
    rw [hrs, ← lagRank_sub_one_eq_finrank_commSpace]
    exact hr₁
  have h2j : 2 * j ≤ n := by
    have h1 := bCoord_two_mul_finrank_le hQ hs
    rw [hrank] at h1
    omega
  obtain ⟨w, hw, -, hfixw⟩ := bCoord_canonical hQ hs ⟨j, hrank⟩
  have hw0 : Q w ≠ 0 := by rw [hw]; exact one_ne_zero
  have hQ0 : ∃ v, Q v ≠ 0 := ⟨w, hw0⟩
  obtain ⟨φ, hφinj, hφmem, hφsurj, hφa⟩ := hM1 n K' Q hQ hT hE s hs j hj hrank w hw0 hw hfixw
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = reflMat Q w hw0 := ⟨_, rfl⟩
  have hρO : ρ ∈ matrixIsometries Q := hρ ▸ reflMat_mem_isometries w hw0
  have hρρ : ρ * ρ = 1 := hρ ▸ reflMat_mul_self w hw0
  have hcomm : ∀ γ : GL (Fin (2 * (n + 1))) K', γ ∈ matrixIsometries Q →
      (γ * ρ = ρ * γ ↔
        (γ : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K') *ᵥ w = w) :=
    fun γ hγ => hρ ▸ comm_reflMat_iff hQ hγ hw hw0
  rw [← hρ] at hφmem hφsurj hφa
  set ρI : matrixIsometries Q := ⟨ρ, hρO⟩ with hρI
  set φ' : StatedSp n K →* GL (Fin (2 * (n + 1))) K' :=
    φ.comp (F4Pilot.statedSpCongr σ n).toMonoidHom with hφ'
  have hφ'mem : ∀ x, φ' x ∈ matrixDerived Q ∧ φ' x * ρ = ρ * φ' x := fun x => hφmem _
  have hφ'a : φ' (spARep n j) = s.val * ρ := by
    rw [hφ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, bCoord_statedSpCongr_spARep, hφa]
  set φc : StatedSp n K →* matrixDerived Q :=
    φ'.codRestrict (matrixDerived Q) (fun x => (hφ'mem x).1) with hφc
  have hφcval : ∀ x, ((φc x : matrixDerived Q) : GL (Fin (2 * (n + 1))) K') = φ' x :=
    fun x => rfl
  have hφcinj : Function.Injective φc := fun x y h =>
    (F4Pilot.statedSpCongr σ n).injective (hφinj (congrArg Subtype.val h))
  have hφcsurj : ∀ A : matrixDerived Q, A.val * ρ = ρ * A.val → ∃ x, φc x = A := by
    intro A hA
    obtain ⟨x, hx⟩ := hφsurj A.val A.2 hA
    refine ⟨(F4Pilot.statedSpCongr σ n).symm x, Subtype.ext ?_⟩
    rw [hφcval, hφ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      hx]
  set ψ : StatedSp n K →* spGlobal e :=
    ε.symm.toMonoidHom.comp ((matrixProjectiveProjection Q).comp φc) with hψ
  have hψinj : Function.Injective ψ :=
    ε.symm.injective.comp ((bCoord_proj_injective hQ0).comp hφcinj)
  have hψx : ∀ x, ε (ψ x) = matrixProjectiveProjection Q (φc x) := fun x => by
    simp [hψ]
  have hψx' : ∀ x, ψ x = ε.symm (matrixProjectiveProjection Q (φc x)) := fun x => by
    simp [hψ]
  set η : MulAut (spGlobal e) := (MulAut.congr ε).symm
    (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q ρI)) with hηdef
  have hηε : MulAut.congr ε η =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q ρI) := by
    rw [hηdef, MulEquiv.apply_symm_apply]
  have hα : (spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ =
      MulAut.conj (ψ (spARep n j)) * η := by
    apply (MulAut.congr ε).injective
    rw [hθs, map_mul, bCoord_congr_conj, hηε, hψx, bCoord_conj_proj_eq, ← map_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    change s.val = (φc (spARep n j) : GL (Fin (2 * (n + 1))) K') * ρ
    rw [hφcval, hφ'a, mul_assoc, hρρ, mul_one]
  have hη : fixedSubgroup η = ψ.range := by
    ext y
    obtain ⟨A, hA⟩ := matrixProjectiveProjection_surjective Q (ε y)
    have hy : y = ε.symm (matrixProjectiveProjection Q A) := by
      rw [hA, MulEquiv.symm_apply_apply]
    rw [hy, bCoord_mem_fixedSubgroup_iff hQ0 ε hηε A]
    constructor
    · intro h
      obtain ⟨x, hx⟩ := hφcsurj A h.symm
      exact ⟨x, by rw [hψx', hx]⟩
    · rintro ⟨x, hx⟩
      have h1 : matrixProjectiveProjection Q (φc x) = matrixProjectiveProjection Q A := by
        rw [← hψx, hx, MulEquiv.apply_symm_apply]
      rw [← bCoord_proj_injective hQ0 h1]
      exact (hφ'mem x).2.symm
  have hfix : fixedSubgroup ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) =
      (centralizer ({spARep n j} : Set (StatedSp n K))).map ψ := by
    ext y
    obtain ⟨A, hA⟩ := matrixProjectiveProjection_surjective Q (ε y)
    have hy : y = ε.symm (matrixProjectiveProjection Q A) := by
      rw [hA, MulEquiv.symm_apply_apply]
    rw [hy, bCoord_mem_fixedSubgroup_iff hQ0 ε hθs A]
    constructor
    · intro h
      have hAO : A.val ∈ matrixIsometries Q := matrixDerived_le_isometries Q A.2
      have hAρ := (hcomm A.val hAO).2 (hfixw A.val hAO h.symm)
      obtain ⟨x, hx⟩ := hφcsurj A hAρ
      refine ⟨x, mem_centralizer_singleton_iff.2 ?_, by rw [hψx', hx]⟩
      apply hφcinj
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hφcval (spARep n j), hφ'a, hx]
      have hAsρ : A.val * (s.val * ρ) = s.val * ρ * A.val := by
        calc A.val * (s.val * ρ) = A.val * s.val * ρ := (mul_assoc _ _ _).symm
          _ = s.val * A.val * ρ := by rw [h]
          _ = s.val * (A.val * ρ) := mul_assoc _ _ _
          _ = s.val * (ρ * A.val) := by rw [hAρ]
          _ = s.val * ρ * A.val := (mul_assoc _ _ _).symm
      exact hAsρ
    · rintro ⟨x, hx, hxy⟩
      have h1 : matrixProjectiveProjection Q (φc x) = matrixProjectiveProjection Q A := by
        rw [← hψx, hxy, MulEquiv.apply_symm_apply]
      rw [← bCoord_proj_injective hQ0 h1, hφcval]
      have hxa := mem_centralizer_singleton_iff.1 hx
      have h3 : Commute (φ' x) (s.val * ρ) := by
        have h4 := congrArg (fun z => ((φc z : matrixDerived Q) : GL (Fin (2 * (n + 1))) K')) hxa
        simp only [map_mul, Subgroup.coe_mul, hφcval, hφ'a] at h4
        exact h4
      have h5 : Commute (φ' x) ρ := (hφ'mem x).2
      have h6 := h3.mul_right h5
      rw [mul_assoc, hρρ, mul_one] at h6
      exact h6.eq.symm
  obtain ⟨v, hv, hs₀v⟩ := exists_eq_reflMat_of_rank_eq_one hQ s₀ hs₀
    (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hr₀)
  have hρI1 : finrank K' (commSpace (matrixLinearIso ρI.val)) = 1 := by
    change finrank K' (commSpace (matrixLinearIso ρ)) = 1
    rw [hρ]
    exact finrank_commSpace_reflMat hQ w hw0
  have hρIρI : ρI * ρI = 1 := Subtype.ext hρρ
  obtain ⟨γ, hγ⟩ := exists_conj_of_rank_eq_one hQ hT hρIρI hs₀
    (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hρI1)
    (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hr₀)
  obtain ⟨γ', hγ'Ω, hγ'⟩ : ∃ γ' : matrixIsometries Q, γ'.val ∈ matrixDerived Q ∧
      γ' * s₀ * γ'⁻¹ = ρI := by
    by_cases hγΩ : γ.val ∈ matrixDerived Q
    · exact ⟨γ, hγΩ, hγ⟩
    · refine ⟨γ * s₀, ?_, ?_⟩
      · change γ.val * s₀.val ∈ matrixDerived Q
        rw [hs₀v]
        exact (mul_reflMat_mem_iff hQ hT γ.2 v hv).2 hγΩ
      · rw [← hγ]
        group
  have hz : ∃ z : spGlobal e, η = MulAut.conj z * (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ *
      (MulAut.conj z)⁻¹ := by
    refine ⟨ε.symm (matrixProjectiveProjection Q ⟨γ'.val, hγ'Ω⟩), (MulAut.congr ε).injective ?_⟩
    rw [hηε, map_mul, map_mul, map_inv, bCoord_congr_conj, MulEquiv.apply_symm_apply, hθ,
      ← bCoord_kappa_of_mem γ' hγ'Ω, ← hγ']
    simp only [map_mul, map_inv]
  have huniq : (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ *
        (spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ =
      (spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ *
        (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ →
      fixedSubgroup ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) ≤
        fixedSubgroup ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩) →
      (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ = η := by
    intro hc hle
    have hc' : s₀ * s = s * s₀ := by
      apply CFSG.ComponentClassification.UnbalancedCatalog.kappa_inclusion_injective hQ hT hE hd
      have h1 := congrArg (MulAut.congr ε) hc
      rw [map_mul, map_mul, hθ, hθs] at h1
      simpa only [MonoidHom.coe_comp, Function.comp_apply, map_mul] using h1
    obtain ⟨c, hc2⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K' 2) (1 / Q v)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero, one_div, inv_eq_zero] at hc2
      exact hv hc2
    have hv'1 : Q (c • v) = 1 := by
      rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, _root_.sq, ← hc2, one_div,
        inv_mul_cancel₀ hv]
    have hv'0 : Q (c • v) ≠ 0 := by rw [hv'1]; exact one_ne_zero
    have hs₀v' : s₀.val = reflMat Q (c • v) hv'0 := by rw [hs₀v, reflMat_smul v hv hc0 hv'0]
    have hsv' : (s.val : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K') *ᵥ (c • v) =
        c • v :=
      (comm_reflMat_iff hQ s.2 hv'1 hv'0).1 (by
        rw [← hs₀v']
        exact (congrArg Subtype.val hc').symm)
    have hfixv : ∀ A ∈ matrixDerived Q, A * s.val = s.val * A →
        (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K') *ᵥ (c • v) = c • v := by
      intro A hA hAs
      have hmem : ε.symm (matrixProjectiveProjection Q ⟨A, hA⟩) ∈
          fixedSubgroup ((spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) :=
        (bCoord_mem_fixedSubgroup_iff hQ0 ε hθs ⟨A, hA⟩).2 hAs.symm
      have hAs₀ := (bCoord_mem_fixedSubgroup_iff hQ0 ε hθ ⟨A, hA⟩).1 (hle hmem)
      have h2 : A * reflMat Q (c • v) hv'0 = reflMat Q (c • v) hv'0 * A := by
        rw [← hs₀v']
        exact hAs₀.symm
      exact (comm_reflMat_iff hQ (matrixDerived_le_isometries Q hA) hv'1 hv'0).1 h2
    obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1
      (hM2 n K' Q hQ hT hE s hs j hj hrank w hw hfixw (c • v) hsv' hfixv)
    have hc'1 : c' = 1 := by
      have h3 := congrArg Q hc'
      rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hw, mul_one, hv'1, _root_.sq] at h3
      exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.eq_one_of_mul_self_eq_one_of_charTwo h3
    have hvw : c • v = w := by rw [← hc', hc'1, one_smul]
    have hs₀ρ : s₀ = ρI := by
      apply Subtype.ext
      change s₀.val = ρ
      rw [hs₀v', hρ]
      exact reflMat_congr hvw hv'0 hw0
    apply (MulAut.congr ε).injective
    refine hθ.trans ?_
    rw [hs₀ρ]
    exact hηε.symm
  exact ⟨hj, h2j, ψ, η, hψinj, hα, hη, hfix, hz, huniq⟩

end CFSG.SeitzReduction.SymplecticPilot
