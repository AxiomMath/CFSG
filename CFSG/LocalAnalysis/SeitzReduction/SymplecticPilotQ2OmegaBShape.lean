module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlParamMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)
open CFSG.RankThree.OrthogonalInvolutions (commSpace)
open CFSG.RankThree.PartOne.AUTSL (reflMat reflMat_mem_isometries reflMat_mul_self comm_reflMat_iff
  mul_reflMat_mem_iff finrank_commSpace_reflMat reflMat_congr mem_matrixDerived_iff_even)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

@[expose] def OmegaBShapeOn {G : Type} [Group G] (G₀ : Subgroup G) (N : ℕ) (K : Type) [Field K]
    (θ α : MulAut G₀) (j : ℕ) : Prop :=
  1 ≤ j ∧ 2 * j ≤ N ∧ ∃ (ψ : StatedSp N K →* G₀) (η : MulAut G₀),
    Function.Injective ψ ∧ α = MulAut.conj (ψ (spARep N j)) * η ∧
    fixedSubgroup η = ψ.range ∧
    fixedSubgroup α = (centralizer ({spARep N j} : Set (StatedSp N K))).map ψ ∧
    (∃ z : G₀, η = MulAut.conj z * θ * (MulAut.conj z)⁻¹) ∧
    (θ * α = α * θ → fixedSubgroup α ≤ fixedSubgroup θ → θ = η)

section Model

variable {G : Type} [Group G] {G₀ : Subgroup G} {N : ℕ} {K : Type} [Field K]
  {K' : Type} [Field K'] [Finite K'] [CharP K' 2] {Q : QuadraticForm K' (Fin (2 * (N + 1)) → K')}

theorem omegaBShapeOn_of_model (σ : K ≃+* K') (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (N + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hImg : matrixProjectiveImage Q = ⊤) (ε : G₀ ≃* matrixProjectiveDerived Q)
    {θ α : MulAut G₀} {s₀ : matrixIsometries Q} (hs₀ : s₀ * s₀ = 1)
    (hr₀ : finrank K' (commSpace (matrixLinearIso s₀.val)) = 1)
    (hθ : MulAut.congr ε θ = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₀))
    {j : ℕ} (hj : 1 ≤ j) (hB : SpOmegaModelBType ε α j) : OmegaBShapeOn G₀ N K θ α j := by
  have hd : 1 ≤ 2 * (N + 1) := by omega
  obtain ⟨β, s₁, hs₁, hr₁, hβ⟩ := hB
  obtain ⟨s, hs, hrs, hθs⟩ := bCoord_exists_kappa_of_conj hImg hs₁ hβ
  have hrank : finrank K' (commSpace (matrixLinearIso s.val)) = 2 * j + 1 := by
    rw [hrs, ← lagRank_sub_one_eq_finrank_commSpace]
    exact hr₁
  have h2j : 2 * j ≤ N := by
    have h1 := bCoord_two_mul_finrank_le hQ hs
    rw [hrank] at h1
    omega
  obtain ⟨w, hw, -, hfixw⟩ := bCoord_canonical hQ hs ⟨j, hrank⟩
  have hw0 : Q w ≠ 0 := by rw [hw]; exact one_ne_zero
  have hQ0 : ∃ v, Q v ≠ 0 := ⟨w, hw0⟩
  obtain ⟨φ, hφinj, hφmem, hφsurj, hφa⟩ :=
    omegaBSpParamInput_holds N K' Q hQ hT hE s hs j hj hrank w hw0 hw hfixw
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = reflMat Q w hw0 := ⟨_, rfl⟩
  have hρO : ρ ∈ matrixIsometries Q := hρ ▸ reflMat_mem_isometries w hw0
  have hρρ : ρ * ρ = 1 := hρ ▸ reflMat_mul_self w hw0
  have hcomm : ∀ γ : GL (Fin (2 * (N + 1))) K', γ ∈ matrixIsometries Q →
      (γ * ρ = ρ * γ ↔
        (γ : Matrix (Fin (2 * (N + 1))) (Fin (2 * (N + 1))) K') *ᵥ w = w) :=
    fun γ hγ => hρ ▸ comm_reflMat_iff hQ hγ hw hw0
  rw [← hρ] at hφmem hφsurj hφa
  set ρI : matrixIsometries Q := ⟨ρ, hρO⟩ with hρI
  set φ' : StatedSp N K →* GL (Fin (2 * (N + 1))) K' :=
    φ.comp (F4Pilot.statedSpCongr σ N).toMonoidHom with hφ'
  have hφ'mem : ∀ x, φ' x ∈ matrixDerived Q ∧ φ' x * ρ = ρ * φ' x := fun x => hφmem _
  have hφ'a : φ' (spARep N j) = s.val * ρ := by
    rw [hφ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, bCoord_statedSpCongr_spARep, hφa]
  set φc : StatedSp N K →* matrixDerived Q :=
    φ'.codRestrict (matrixDerived Q) (fun x => (hφ'mem x).1) with hφc
  have hφcval : ∀ x, ((φc x : matrixDerived Q) : GL (Fin (2 * (N + 1))) K') = φ' x :=
    fun x => rfl
  have hφcinj : Function.Injective φc := fun x y h =>
    (F4Pilot.statedSpCongr σ N).injective (hφinj (congrArg Subtype.val h))
  have hφcsurj : ∀ A : matrixDerived Q, A.val * ρ = ρ * A.val → ∃ x, φc x = A := by
    intro A hA
    obtain ⟨x, hx⟩ := hφsurj A.val A.2 hA
    refine ⟨(F4Pilot.statedSpCongr σ N).symm x, Subtype.ext ?_⟩
    rw [hφcval, hφ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      hx]
  set ψ : StatedSp N K →* G₀ :=
    ε.symm.toMonoidHom.comp ((matrixProjectiveProjection Q).comp φc) with hψ
  have hψinj : Function.Injective ψ :=
    ε.symm.injective.comp ((bCoord_proj_injective hQ0).comp hφcinj)
  have hψx : ∀ x, ε (ψ x) = matrixProjectiveProjection Q (φc x) := fun x => by
    simp [hψ]
  have hψx' : ∀ x, ψ x = ε.symm (matrixProjectiveProjection Q (φc x)) := fun x => by
    simp [hψ]
  set η : MulAut G₀ := (MulAut.congr ε).symm
    (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q ρI)) with hηdef
  have hηε : MulAut.congr ε η =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q ρI) := by
    rw [hηdef, MulEquiv.apply_symm_apply]
  have hα : α = MulAut.conj (ψ (spARep N j)) * η := by
    apply (MulAut.congr ε).injective
    rw [hθs, map_mul, bCoord_congr_conj, hηε, hψx, bCoord_conj_proj_eq, ← map_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    change s.val = (φc (spARep N j) : GL (Fin (2 * (N + 1))) K') * ρ
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
  have hfix : fixedSubgroup α = (centralizer ({spARep N j} : Set (StatedSp N K))).map ψ := by
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
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hφcval (spARep N j), hφ'a, hx]
      calc A.val * (s.val * ρ) = A.val * s.val * ρ := (mul_assoc _ _ _).symm
        _ = s.val * A.val * ρ := by rw [h]
        _ = s.val * (A.val * ρ) := mul_assoc _ _ _
        _ = s.val * (ρ * A.val) := by rw [hAρ]
        _ = s.val * ρ * A.val := (mul_assoc _ _ _).symm
    · rintro ⟨x, hx, hxy⟩
      have h1 : matrixProjectiveProjection Q (φc x) = matrixProjectiveProjection Q A := by
        rw [← hψx, hxy, MulEquiv.apply_symm_apply]
      rw [← bCoord_proj_injective hQ0 h1, hφcval]
      have hxa := mem_centralizer_singleton_iff.1 hx
      have h3 : Commute (φ' x) (s.val * ρ) := by
        have h4 := congrArg (fun z => ((φc z : matrixDerived Q) : GL (Fin (2 * (N + 1))) K')) hxa
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
  have hz : ∃ z : G₀, η = MulAut.conj z * θ * (MulAut.conj z)⁻¹ := by
    refine ⟨ε.symm (matrixProjectiveProjection Q ⟨γ'.val, hγ'Ω⟩), (MulAut.congr ε).injective ?_⟩
    rw [hηε, map_mul, map_mul, map_inv, bCoord_congr_conj, MulEquiv.apply_symm_apply, hθ,
      ← bCoord_kappa_of_mem γ' hγ'Ω, ← hγ']
    simp only [map_mul, map_inv]
  have huniq : θ * α = α * θ → fixedSubgroup α ≤ fixedSubgroup θ → θ = η := by
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
    have hsv' : (s.val : Matrix (Fin (2 * (N + 1))) (Fin (2 * (N + 1))) K') *ᵥ (c • v) =
        c • v :=
      (comm_reflMat_iff hQ s.2 hv'1 hv'0).1 (by
        rw [← hs₀v']
        exact (congrArg Subtype.val hc').symm)
    have hfixv : ∀ A ∈ matrixDerived Q, A * s.val = s.val * A →
        (A : Matrix (Fin (2 * (N + 1))) (Fin (2 * (N + 1))) K') *ᵥ (c • v) = c • v := by
      intro A hA hAs
      have hmem : ε.symm (matrixProjectiveProjection Q ⟨A, hA⟩) ∈ fixedSubgroup α :=
        (bCoord_mem_fixedSubgroup_iff hQ0 ε hθs ⟨A, hA⟩).2 hAs.symm
      have hAs₀ := (bCoord_mem_fixedSubgroup_iff hQ0 ε hθ ⟨A, hA⟩).1 (hle hmem)
      have h2 : A * reflMat Q (c • v) hv'0 = reflMat Q (c • v) hv'0 * A := by
        rw [← hs₀v']
        exact hAs₀.symm
      exact (comm_reflMat_iff hQ (matrixDerived_le_isometries Q hA) hv'1 hv'0).1 h2
    obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1
      (omegaBFixedVectorInput_holds N K' Q hQ hT hE s hs j hj hrank w hw hfixw (c • v) hsv'
        hfixv)
    have hc'1 : c' = 1 := by
      have h3 := congrArg Q hc'
      rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hw, mul_one, hv'1, _root_.sq] at h3
      exact
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.eq_one_of_mul_self_eq_one_of_charTwo h3
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

theorem omegaBCoset_of_model (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (N + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (ε : G₀ ≃* matrixProjectiveDerived Q) {θ : MulAut G₀} {s₀ : matrixIsometries Q}
    (hs₀ : s₀ * s₀ = 1) (hr₀ : finrank K' (commSpace (matrixLinearIso s₀.val)) = 1)
    (hθ : MulAut.congr ε θ = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₀))
    (y : G₀) (hy : (MulAut.conj y * θ) * (MulAut.conj y * θ) = 1) :
    (∃ β : MulAut G₀, β * θ = (MulAut.conj y * θ) * β) ∨
      ∃ j, 1 ≤ j ∧ SpOmegaModelBType ε (MulAut.conj y * θ) j := by
  have hd : 1 ≤ 2 * (N + 1) := by omega
  obtain ⟨Y, hY⟩ := matrixProjectiveProjection_surjective Q (ε y)
  set u : matrixIsometries Q := ⟨Y.val, matrixDerived_le_isometries Q Y.2⟩ * s₀ with hu
  have hθu : MulAut.congr ε (MulAut.conj y * θ) =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q u) := by
    rw [map_mul, bCoord_congr_conj, hθ, ← hY, bCoord_conj_proj_eq, ← map_mul, ← map_mul]
  have huu : u * u = 1 := by
    apply CFSG.ComponentClassification.UnbalancedCatalog.kappa_inclusion_injective hQ hT hE hd
    simp only [MonoidHom.coe_comp, Function.comp_apply, map_mul, map_one]
    rw [← hθu, ← map_mul, hy, map_one]
  have hs₀not : s₀.val ∉ matrixDerived Q := by
    rw [mem_matrixDerived_iff_even hQ hT s₀.2, hr₀]
    decide
  have hunot : u.val ∉ matrixDerived Q := by
    intro hu'
    apply hs₀not
    have h1 : s₀.val = Y.val⁻¹ * u.val := by
      rw [hu, Subgroup.coe_mul, ← mul_assoc]
      simp
    rw [h1]
    exact mul_mem (inv_mem Y.2) hu'
  have hodd : Odd (finrank K' (commSpace (matrixLinearIso u.val))) := by
    rw [← Nat.not_even_iff_odd]
    exact fun hev => hunot ((mem_matrixDerived_iff_even hQ hT u.2).2 hev)
  obtain ⟨m, hm⟩ := hodd
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · left
    have hr1 : finrank K' (commSpace (matrixLinearIso u.val)) = 1 := by omega
    obtain ⟨γ, hγ⟩ := exists_conj_of_rank_eq_one hQ hT huu hs₀
      (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hr1)
      (by rw [lagRank_sub_one_eq_finrank_commSpace]; exact hr₀)
    exact exists_conj_of_linearClass_conj ε (β := 1) (β₀ := 1)
      (by rw [inv_one, one_mul, mul_one]; exact hθu)
      (by rw [inv_one, one_mul, mul_one]; exact hθ) hγ
  · right
    refine ⟨m, hmpos, 1, u, huu, ?_, ?_⟩
    · rw [lagRank_sub_one_eq_finrank_commSpace, hm]
    · rw [inv_one, one_mul, mul_one]
      exact hθu

end Model

end CFSG.SeitzReduction.SymplecticPilot
