module

public import CFSG.RankThree.PartOne.AUTSL.OmegaDickson
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrIso
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.S11d.OutOrthogonal

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.PartOne.AUTSL
  CFSG.RankThree.PartOne.OutStructure
open scoped commutatorElement

section Plus

variable {K : Type} [Field K] (n : ℕ)

theorem coordinateQuadPlus_fieldMap (σ : K ≃+* K) (v : Fin (2 * n) → K) :
    coordinateQuadPlus n K (coordinateFieldMap (2 * n) σ v) =
      σ (coordinateQuadPlus n K v) := by
  rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply, map_sum]
  simp only [coordinateFieldMap_apply, map_mul]

@[expose] noncomputable def plusFieldHom : (K ≃+* K) →* similarityPairs (coordinateQuadPlus n K)
    where
  toFun σ := fieldPair (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldMap n σ)
  map_one' := Subtype.ext (SemidirectProduct.ext rfl rfl)
  map_mul' σ τ := Subtype.ext (SemidirectProduct.ext (by
    change (1 : GL (Fin (2 * n)) K) = 1 * (glFieldAut (Fin (2 * n)) K σ) 1
    simp) rfl)

theorem plusFieldHom_left (σ : K ≃+* K) : (plusFieldHom n σ).val.left = 1 := rfl

theorem plusFieldHom_right (σ : K ≃+* K) : (plusFieldHom n σ).val.right = σ := rfl

@[expose] noncomputable def plusVec (hn : 1 ≤ n) : Fin (2 * n) → K :=
  Pi.single (plusIndexEquiv n (.inl ⟨0, hn⟩)) 1 + Pi.single (plusIndexEquiv n (.inr ⟨0, hn⟩)) 1

theorem plusVec_inl (hn : 1 ≤ n) (i : Fin n) :
    plusVec n hn (plusIndexEquiv n (.inl i)) = if i = ⟨0, hn⟩ then (1 : K) else 0 := by
  simp [plusVec, Pi.single_apply, (plusIndexEquiv n).injective.eq_iff]

theorem plusVec_inr (hn : 1 ≤ n) (i : Fin n) :
    plusVec n hn (plusIndexEquiv n (.inr i)) = if i = ⟨0, hn⟩ then (1 : K) else 0 := by
  simp [plusVec, Pi.single_apply, (plusIndexEquiv n).injective.eq_iff]

theorem coordinateQuadPlus_plusVec (hn : 1 ≤ n) :
    coordinateQuadPlus n K (plusVec n hn) = 1 := by
  rw [coordinateQuadPlus_apply]
  simp only [plusVec_inl, plusVec_inr]
  rw [Finset.sum_eq_single ⟨0, hn⟩]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

theorem coordinateFieldMap_plusVec (hn : 1 ≤ n) (σ : K ≃+* K) :
    coordinateFieldMap (2 * n) σ (plusVec n hn) = plusVec n hn := by
  funext m
  rw [coordinateFieldMap_apply]
  by_cases h : m = plusIndexEquiv n (.inl ⟨0, hn⟩) ∨ m = plusIndexEquiv n (.inr ⟨0, hn⟩)
  · rcases h with rfl | rfl <;> simp [plusVec, (plusIndexEquiv n).injective.eq_iff]
  · push Not at h
    simp [plusVec, h.1, h.2]

end Plus

section Refl

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem glFieldAut_reflMat (σ : K ≃+* K)
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) {w : Fin d → K}
    (hwσ : coordinateFieldMap d σ w = w) (hw1 : Q w = 1) (hw : Q w ≠ 0) :
    glFieldAut (Fin d) K σ (reflMat Q w hw) = reflMat Q w hw := by
  apply matrixLinearIso.injective
  refine LinearEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ : ∃ x, coordinateFieldMap d σ x = y :=
    ⟨(coordinateFieldMap d σ).symm y, by simp⟩
  have h1 : matrixLinearIso (glFieldAut (Fin d) K σ (reflMat Q w hw)) (coordinateFieldMap d σ x) =
      coordinateFieldMap d σ (matrixLinearIso (reflMat Q w hw) x) :=
    (coordinateFieldMap_matrix σ (reflMat Q w hw) x).symm
  rw [h1, matrixLinearIso_apply, matrixLinearIso_apply, reflMat_mulVec, reflMat_mulVec]
  have hpolar : QuadraticMap.polar Q w (coordinateFieldMap d σ x) =
      σ (QuadraticMap.polar Q w x) := by
    have e : w + coordinateFieldMap d σ x = coordinateFieldMap d σ (w + x) := by
      rw [map_add, hwσ]
    rw [QuadraticMap.polar, QuadraticMap.polar, e, hQσ, hQσ, hw1, map_sub, map_sub, map_one]
  funext m
  simp only [coordinateFieldMap_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hpolar, hw1,
    div_one, map_sub, map_mul]
  have := congrFun hwσ m
  rw [coordinateFieldMap_apply] at this
  rw [this]

end Refl

section Decomp

theorem aut_mul_conj_eq {P : Type*} [Group P] (φ : MulAut P) (y : P) :
    φ * MulAut.conj y = MulAut.conj (φ y) * φ := by
  have := aut_mul_conj_mul_inv φ y
  rwa [mul_inv_eq_iff_eq_mul] at this

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem exists_conj_mul_fieldAut (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hQ : ∃ v, Q v ≠ 0) (F : (K ≃+* K) →* similarityPairs Q)
    (hFr : ∀ σ, (F σ).val.right = σ) {w : Fin d → K} (hw : Q w ≠ 0)
    (hcomm : ∀ σ, F σ * matrixIsometryInclusion Q ⟨reflMat Q w hw, reflMat_mem_isometries w hw⟩ =
      matrixIsometryInclusion Q ⟨reflMat Q w hw, reflMat_mem_isometries w hw⟩ * F σ)
    {α : MulAut (matrixProjectiveDerived Q)} (hα : α ∈ matrixProjectiveImage Q) {e : ℕ}
    (he : Odd e) (hαe : α ^ e ∈ inn (matrixProjectiveDerived Q)) :
    ∃ (x : matrixProjectiveDerived Q) (σ : K ≃+* K),
      α = MulAut.conj x * matrixProjectiveConjugationHom Q (F σ) := by
  set Ψ := matrixProjectiveConjugationHom Q with hΨ
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff Q α).1 hα
  have hgΨ : Ψ g = α := hg
  set σ₀ : K ≃+* K := g.val.right with hσ₀
  set ℓ : similarityPairs Q := (F σ₀)⁻¹ * g with hℓdef
  have hℓ : ℓ ∈ linearSimilarityPairs Q := by
    refine MonoidHom.mem_ker.2 ?_
    simp only [hℓdef, map_mul, map_inv, fieldProjection_apply, hFr, hσ₀, inv_mul_cancel]
  obtain ⟨B, hB⟩ := exists_isometry_of_linear Q hQ ⟨ℓ, hℓ⟩
  have hΨℓ : Ψ ℓ = Ψ (matrixIsometryInclusion Q B) := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨C, rfl⟩ := matrixProjectiveProjection_surjective Q x
    change matrixProjectiveConjugation Q ℓ _ =
      matrixProjectiveConjugation Q (matrixIsometryInclusion Q B) _
    rw [matrixProjectiveConjugation_mk, matrixProjectiveConjugation_mk]
    congr 1
    apply Subtype.ext
    rw [hB C, matrixDerivedConjugation_val]
    simp only [matrixIsometryInclusion_val, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      map_one, MulAut.one_apply]
  have hαΨ : α = Ψ (F σ₀) * Ψ (matrixIsometryInclusion Q B) := by
    rw [← hgΨ, ← hΨℓ, ← map_mul]
    congr 1
    simp [hℓdef]
  have hinner : ∀ (B' : matrixIsometries Q) (hB' : B'.val ∈ matrixDerived Q),
      Ψ (matrixIsometryInclusion Q B') =
        MulAut.conj (matrixProjectiveProjection Q ⟨B'.val, hB'⟩) := by
    intro B' hB'
    refine MulEquiv.ext fun x => ?_
    obtain ⟨C, rfl⟩ := matrixProjectiveProjection_surjective Q x
    exact matrixProjectiveConjugation_incl Q ⟨B'.val, hB'⟩ C
  have hφconj : ∀ y : matrixProjectiveDerived Q, Ψ (F σ₀) * MulAut.conj y =
      MulAut.conj (Ψ (F σ₀) y) * Ψ (F σ₀) := fun y => aut_mul_conj_eq _ y
  by_cases hBΩ : B.val ∈ matrixDerived Q
  · refine ⟨Ψ (F σ₀) (matrixProjectiveProjection Q ⟨B.val, hBΩ⟩), σ₀, ?_⟩
    rw [hαΨ, hinner B hBΩ, hφconj]
  ·
    have hBr : B.val * reflMat Q w hw ∈ matrixDerived Q := by
      rcases mem_or_mul_reflMat_mem hnd hT B.2 w hw with h | h
      · exact absurd h hBΩ
      · exact h
    set r : matrixIsometries Q := ⟨reflMat Q w hw, reflMat_mem_isometries w hw⟩ with hr
    set B' : matrixIsometries Q := ⟨B.val * reflMat Q w hw, mul_mem B.2 r.2⟩ with hB'
    have hBB' : matrixIsometryInclusion Q B =
        matrixIsometryInclusion Q B' * matrixIsometryInclusion Q r := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      change B.val = B.val * reflMat Q w hw * reflMat Q w hw
      rw [mul_assoc, reflMat_mul_self, mul_one]
    have hrr : Ψ (matrixIsometryInclusion Q r) * Ψ (matrixIsometryInclusion Q r) = 1 := by
      rw [← map_mul, ← map_mul]
      have : r * r = 1 := Subtype.ext (reflMat_mul_self w hw)
      rw [this, map_one, map_one]
    have hφρ : Ψ (F σ₀) * Ψ (matrixIsometryInclusion Q r) =
        Ψ (matrixIsometryInclusion Q r) * Ψ (F σ₀) := by
      rw [← map_mul, ← map_mul, hcomm]
    set φ := Ψ (F σ₀) with hφ
    set ρ := Ψ (matrixIsometryInclusion Q r) with hρ
    set y' := matrixProjectiveProjection Q ⟨B.val * reflMat Q w hw, hBr⟩ with hy'
    have hα2 : α = MulAut.conj (φ y') * (φ * ρ) := by
      rw [hαΨ, hBB', map_mul, hinner B' hBr, ← mul_assoc, hφconj, mul_assoc]
    set π : MulAut (matrixProjectiveDerived Q) →* MulAut (matrixProjectiveDerived Q) ⧸
      inn (matrixProjectiveDerived Q) := QuotientGroup.mk' _ with hπ
    have hπconj : ∀ z, π (MulAut.conj z) = 1 := fun z =>
      (QuotientGroup.eq_one_iff _).2 ⟨z, rfl⟩
    have hbb : π ρ * π ρ = 1 := by rw [← map_mul, hrr, map_one]
    have hcom : Commute (π φ) (π ρ) := by
      change π φ * π ρ = π ρ * π φ
      rw [← map_mul π, ← map_mul π, hφρ]
    have hπα : π α = π φ * π ρ := by rw [hα2, map_mul, map_mul, hπconj, one_mul]
    obtain ⟨m, rfl⟩ := he
    have hρe : π ρ ^ (2 * m + 1) = π ρ := by
      rw [pow_succ, pow_mul, sq, hbb, one_pow, one_mul]
    have h1 : π α ^ (2 * m + 1) = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 hαe
    rw [hπα, hcom.mul_pow, hρe] at h1
    have hρ' : π ρ = (π φ ^ (2 * m + 1))⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hπα' : π α = π (Ψ (F (σ₀ ^ ((1 : ℤ) - ((2 * m + 1 : ℕ) : ℤ))))) := by
      rw [map_zpow, map_zpow, map_zpow, hπα, hρ', ← zpow_natCast, ← zpow_neg, ← zpow_one_add]
      congr 1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hπα'
    obtain ⟨z, hz⟩ := hπα'
    set σ'' : K ≃+* K := σ₀ ^ ((1 : ℤ) - ((2 * m + 1 : ℕ) : ℤ)) with hσ''
    refine ⟨Ψ (F σ'') z⁻¹, σ'', ?_⟩
    have h2 : α = Ψ (F σ'') * MulAut.conj z⁻¹ := by
      rw [map_inv, hz]
      group
    rw [h2, aut_mul_conj_eq]

end Decomp

section PlusDecomp

variable {K : Type} [Field K] [Finite K] [CharP K 2] (n : ℕ)

theorem exists_conj_mul_plusFieldAut (hn : 1 ≤ n)
    (hnd : (QuadraticMap.polarBilin (coordinateQuadPlus n K)).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, coordinateQuadPlus n K x = 0)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (hα : α ∈ matrixProjectiveImage (coordinateQuadPlus n K)) {e : ℕ} (he : Odd e)
    (hαe : α ^ e ∈ inn (matrixProjectiveDerived (coordinateQuadPlus n K))) :
    ∃ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) (σ : K ≃+* K),
      α = MulAut.conj x *
        matrixProjectiveConjugationHom (coordinateQuadPlus n K) (plusFieldHom n σ) := by
  have hw1 := coordinateQuadPlus_plusVec (K := K) n hn
  have hw : coordinateQuadPlus n K (plusVec n hn) ≠ 0 := by rw [hw1]; exact one_ne_zero
  refine exists_conj_mul_fieldAut (coordinateQuadPlus n K) hnd hT ⟨_, hw⟩ (plusFieldHom n)
    (fun σ => plusFieldHom_right n σ) hw ?_ hα he hαe
  intro σ
  apply Subtype.ext
  apply SemidirectProduct.ext
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, SemidirectProduct.mul_left,
      SemidirectProduct.mul_left, matrixIsometryInclusion_val, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, plusFieldHom_left, plusFieldHom_right, map_one, one_mul,
      mul_one]
    exact glFieldAut_reflMat (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldMap n σ)
      (coordinateFieldMap_plusVec n hn σ) hw1 hw
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, SemidirectProduct.mul_right,
      SemidirectProduct.mul_right, matrixIsometryInclusion_val, SemidirectProduct.right_inl,
      plusFieldHom_right, mul_one, one_mul]

end PlusDecomp

end CFSG.AGLEmbedding.ParabAutIrr
