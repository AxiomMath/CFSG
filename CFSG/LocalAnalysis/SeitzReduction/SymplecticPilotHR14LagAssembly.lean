module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagInner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaClasses

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap Module Subgroup CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.PartOne.AUTSL (reflMat reflMat_mulVec reflMat_congr conj_reflMat
  matrixLinearIso_apply)

section Reflections

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_reflection_of_finrank_eq_one [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgg : g * g = 1)
    (h1 : finrank K (omegaInvSpace g) = 1) :
    ∃ w, Q w ≠ 0 ∧ ∀ v, g v = v - (polar Q w v / Q w) • w := by
  have hne : omegaInvSpace g ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : omegaInvSpace g = K ∙ w := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hw
    · rw [finrank_span_singleton hw0, h1]
  have hQw : Q w ≠ 0 := by
    intro hQw
    have hev : Even (finrank K (omegaInvSpace g)) :=
      CFSG.RankThree.OrthogonalInvolutions.even_finrank_commSpace_of_forall_eq_zero hQ hg hgg
        fun u hu => by
          change u ∈ omegaInvSpace g at hu
          rw [hspan] at hu
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
          rw [map_smul_eq_sq, hQw, mul_zero]
    rw [h1] at hev
    exact Nat.not_even_one hev
  refine ⟨w, hQw, fun v => ?_⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    (show omegaInvNil g v ∈ K ∙ w from hspan ▸ omegaInvNil_mem_omegaInvSpace g v)
  have key : c = polar Q w v / Q w := by
    rw [eq_div_iff hQw]
    by_cases hc0 : c = 0
    · have hNv : omegaInvNil g v = 0 := by rw [← hc, hc0, zero_smul]
      have h0 := (omegaInvNil_eq_zero_iff hQ hg hgg).1 hNv w hw
      rw [hc0, zero_mul, polar_comm, h0]
    · have e := map_omegaInvNil hg v
      rw [← hc, map_smul_eq_sq, polar_smul_right_eq] at e
      have e' : c * (c * Q w - polar Q v w) = 0 := by linear_combination e
      have e'' := sub_eq_zero.1 ((mul_eq_zero.1 e').resolve_left hc0)
      rw [polar_comm]
      exact e''
  have hgv : g v = v + omegaInvNil g v := by
    rw [omegaInvNil_apply]
    abel
  rw [hgv, ← hc, key, omegaInv_sub_eq_add K]

end Reflections

section Matrix

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_eq_reflMat_of_rank_eq_one [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (s : matrixIsometries Q) (hs : s * s = 1)
    (h1 : (((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1).rank = 1) :
    ∃ w, ∃ hw : Q w ≠ 0, (s : GL (Fin d) K) = reflMat Q w hw := by
  have hg : matrixLinearIso (s : GL (Fin d) K) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := s.2
  have hgg : matrixLinearIso (s : GL (Fin d) K) * matrixLinearIso (s : GL (Fin d) K) = 1 := by
    rw [← map_mul, ← Subgroup.coe_mul, hs, Subgroup.coe_one, map_one]
  rw [lagRank_sub_one_eq_finrank_commSpace] at h1
  obtain ⟨w, hw, hf⟩ := exists_reflection_of_finrank_eq_one hQ hg hgg h1
  refine ⟨w, hw, matrixLinearIso.injective (LinearEquiv.ext fun v => ?_)⟩
  rw [hf, matrixLinearIso_apply (reflMat Q w hw), reflMat_mulVec]

theorem reflMat_smul (w : Fin d → K) (hw : Q w ≠ 0) {c : K} (hc : c ≠ 0)
    (hcw : Q (c • w) ≠ 0) : reflMat Q (c • w) hcw = reflMat Q w hw := by
  apply matrixLinearIso.injective
  refine LinearEquiv.ext fun v => ?_
  rw [matrixLinearIso_apply, matrixLinearIso_apply, reflMat_mulVec, reflMat_mulVec,
    polar_smul_left_eq, map_smul_eq_sq, smul_smul]
  congr 2
  field_simp

theorem exists_conj_reflMat [Finite K] [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {w w' : Fin d → K} (hw : Q w ≠ 0) (hw' : Q w' ≠ 0) :
    ∃ γ ∈ matrixIsometries Q, γ * reflMat Q w hw * γ⁻¹ = reflMat Q w' hw' := by
  obtain ⟨P, r, hr, hP, -, -⟩ := CFSG.RankThree.Classical.exists_hypPair_tail_decomposition hQ hT
  have hP01 := hP 0 1 (by omega) (by omega) (by omega)
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q w' / Q w)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hc
    exact hc.elim hw' hw
  have hQcw : Q (c • w) = Q w' := by rw [map_smul_eq_sq, _root_.sq, ← hc, div_mul_cancel₀ _ hw]
  have hcw0 : c • w ≠ 0 := smul_ne_zero hc0 fun h => hw (by rw [h, QuadraticMap.map_zero])
  have hw'0 : w' ≠ 0 := fun h => hw' (by rw [h, QuadraticMap.map_zero])
  obtain ⟨γ₀, hγ₀E, hγ₀⟩ := exists_mem_elementaryGroup_apply_eq hQ hP01 hcw0 hw'0 hQcw
  set γ := matrixLinearIso.symm γ₀ with hγdef
  have hγ : γ ∈ matrixIsometries Q := by
    change matrixLinearIso γ ∈ TauCeti.QuadraticMap.orthogonalGroup Q
    rw [hγdef, MulEquiv.apply_symm_apply]
    exact elementaryGroup_le_orthogonalGroup Q hγ₀E
  have hγv : Matrix.mulVec γ.val (c • w) = w' := by
    rw [← matrixLinearIso_apply, hγdef, MulEquiv.apply_symm_apply, hγ₀]
  have hcwQ : Q (c • w) ≠ 0 := by
    rw [hQcw]
    exact hw'
  refine ⟨γ, hγ, ?_⟩
  rw [← reflMat_smul w hw hc0 hcwQ, conj_reflMat hγ (c • w) hcwQ (by rw [hγv]; exact hw')]
  exact reflMat_congr hγv _ _

end Matrix

section Classes

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem exists_conj_of_linearClass_conj {X : Type*} [Group X] {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (ε : X ≃* matrixProjectiveDerived Q) {θ θ₀ : MulAut X}
    {β β₀ : MulAut (matrixProjectiveDerived Q)} {s s₀ γ : matrixIsometries Q}
    (hβ : β⁻¹ * MulAut.congr ε θ * β =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s))
    (hβ₀ : β₀⁻¹ * MulAut.congr ε θ₀ * β₀ =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₀))
    (hγ : γ * s₀ * γ⁻¹ = s) : ∃ β' : MulAut X, β' * θ₀ = θ * β' := by
  refine ⟨(MulAut.congr ε).symm (β * matrixProjectiveConjugationHom Q
    (matrixIsometryInclusion Q γ) * β₀⁻¹), (MulAut.congr ε).injective ?_⟩
  have h1 : MulAut.congr ε θ =
      β * matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) * β⁻¹ := by
    rw [← hβ]
    group
  have h2 : MulAut.congr ε θ₀ =
      β₀ * matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s₀) * β₀⁻¹ := by
    rw [← hβ₀]
    group
  simp only [map_mul, MulEquiv.apply_symm_apply]
  rw [h1, h2, ← hγ]
  simp only [map_mul, map_inv]
  group

end Classes

section Rows

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem normalizerMonoidHom_one_conj_eq {G : Type} [Group G] {M : Subgroup G} {t : G}
    (htN : t ∈ normalizer (M : Set G)) (hg1 : (1 : G)⁻¹ * t * 1 ∈ normalizer (M : Set G)) :
    M.normalizerMonoidHom ⟨(1 : G)⁻¹ * t * 1, hg1⟩ = M.normalizerMonoidHom ⟨t, htN⟩ := by
  congr 1
  exact Subtype.ext (by simp)

theorem exists_conj_of_rank_eq_one {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {s s₀ : matrixIsometries Q} (hs : s * s = 1) (hs₀ : s₀ * s₀ = 1)
    (h1 : (((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1).rank = 1)
    (h0 : (((s₀ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1).rank = 1) :
    ∃ γ : matrixIsometries Q, γ * s₀ * γ⁻¹ = s := by
  obtain ⟨w, hw, hsw⟩ := exists_eq_reflMat_of_rank_eq_one hQ s hs h1
  obtain ⟨w₀, hw₀, hsw₀⟩ := exists_eq_reflMat_of_rank_eq_one hQ s₀ hs₀ h0
  obtain ⟨γ, hγ, hγs⟩ := exists_conj_reflMat hQ hT hw₀ hw
  refine ⟨⟨γ, hγ⟩, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hsw₀, hsw]
  exact hγs

end Rows

end CFSG.SeitzReduction.SymplecticPilot
