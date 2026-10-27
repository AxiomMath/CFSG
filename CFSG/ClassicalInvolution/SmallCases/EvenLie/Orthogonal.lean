module

public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Basic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenOrthogonalComponents

public noncomputable section

namespace CFSG.ClassicalInvolution

open QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.UnbalancingLocal.EvenOrthogonalComponents
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  (orthogonal_geometry_char_two_reflection_separation)

variable {K : Type} [Field K] {d : ℕ}

section Regular

variable [Finite K] [CharP K 2] {Q : QuadraticForm K (Fin d → K)}
  (hQ : Q.polarBilin.Nondegenerate)
  (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q)

include hQ hT hE in
theorem exists_two_radical_of_two_le_rank
    (H : Subgroup (MulAut (matrixProjectiveDerived Q)))
    (hInn : CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ H)
    (hHE : H ≤ matrixProjectiveImage Q) (s : matrixIsometries Q)
    (hs2 : orderOf (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) = 2)
    (hrank : 2 ≤ (((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1).rank) :
    ∃ R : Subgroup (MulAut (matrixProjectiveDerived Q)),
      R ≤ H ⊓ Subgroup.centralizer
        {matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)} ∧
      (∀ β ∈ H ⊓ Subgroup.centralizer
        {matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)},
          β ∈ Subgroup.normalizer (R : Set _)) ∧
      (∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k = 1) ∧
      (∀ x ∈ H ⊓ Subgroup.centralizer
        {matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)},
          x ∈ Subgroup.centralizer (R : Set _) → ∃ k : ℕ, x ^ 2 ^ k = 1) := by
  have hd : 1 ≤ d := by have := six_le hQ hT; omega
  have := finite_mulAut_matrixProjectiveDerived Q
  set α := matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) with hαdef
  set S := matrixLinearEquiv s.val with hSdef
  have hss : s * s = 1 := by
    apply isometryKappa_injective hQ hT hE
    rw [map_mul, map_one]
    change α * α = 1
    rw [← pow_two, ← hs2, pow_orderOf_eq_one]
  have hSS : ∀ v, S (S v) = v := fun v => by
    have h := congrArg (fun A : matrixIsometries Q => matrixLinearEquiv A.val v) hss
    simp only [Subgroup.coe_mul, matrixLinearEquiv_mul, LinearEquiv.mul_apply,
      Subgroup.coe_one] at h
    rw [h]
    exact Matrix.one_mulVec v
  have hiso : ∀ v, Q (S v) = Q v := (mem_matrixIsometries_iff Q s.val).mp s.2
  have hpol : ∀ x y, polar Q (S x) (S y) = polar Q x y := fun x y => by
    rw [polar, polar, ← map_add, hiso, hiso, hiso]
  set N : (Fin d → K) →ₗ[K] (Fin d → K) := (S : (Fin d → K) →ₗ[K] (Fin d → K)) - LinearMap.id
    with hNdef
  have hN : ∀ v, N v = S v - v := fun v => rfl
  have hadj : ∀ v w, polar Q (N v) w = polar Q v (N w) := fun v w => by
    rw [hN, hN, polar_sub_left, polar_sub_right]
    have h := hpol v (S w)
    rw [hSS] at h
    rw [← h]
  have hNN : ∀ v, N (N v) = 0 := fun v => by
    rw [hN, hN, map_sub, hSS]
    rw [show v - S v - (S v - v) = (2 : K) • (v - S v) by module, CharTwo.two_eq_zero,
      zero_smul]
  have hNM : N = (((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1).mulVecLin := by
    apply LinearMap.ext
    intro v
    rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  set W := LinearMap.range N with hWdef
  have hWrank : 2 ≤ finrank K W := by
    rw [hWdef, hNM]
    exact hrank
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0 := by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    rw [hadj, hNN, polar_zero_right]
  have hker : ∀ x, x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W ↔ N x = 0 := by
    intro x
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      apply eq_zero_of_polar_eq_zero hQ
      intro v
      have h1 : polar Q (N v) x = 0 := h _ ⟨v, rfl⟩
      rw [hadj, polar_comm] at h1
      exact h1
    · rintro h _ ⟨v, rfl⟩
      change polar Q (N v) x = 0
      rw [hadj, h, polar_zero_right]
  obtain ⟨-, -, -, hR4, -, hnormR, hcentR⟩ :=
    flagRadicalCentralizer_of_regular hQ hT hE W hWiso hWrank
  set R := flagRadicalImage Q W with hRdef
  have hcommS : ∀ x : unitMultiplierPairs Q,
      matrixProjectiveConjugationHom Q x.1 * α = α * matrixProjectiveConjugationHom Q x.1 →
        ∀ v, coordinateSemilinearMap x.1.val (S v) = S (coordinateSemilinearMap x.1.val v) := by
    intro x hx v
    have hinc : matrixIsometryInclusion Q s ∈ unitMultiplierPairs Q := fun v => by
      rw [matrixIsometryInclusion_val, coordinateSemilinearMap_inl]
      exact hiso v
    have h2 : matrixProjectiveConjugationHom Q
        ((x.1 * matrixIsometryInclusion Q s) * (matrixIsometryInclusion Q s * x.1)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, ← hαdef, hx, mul_inv_cancel]
    have h3 := eq_one_of_kappa_eq_one Q hQ hT hE hd
      (mul_mem (mul_mem x.2 hinc) (inv_mem (mul_mem hinc x.2))) h2
    have h4 := mul_inv_eq_one.mp h3
    have h5 := congrArg (fun y : similarityPairs Q => coordinateSemilinearMap y.val v) h4
    simp only [Subgroup.coe_mul, coordinateSemilinearMap_mul, matrixIsometryInclusion_val,
      coordinateSemilinearMap_inl] at h5
    exact h5
  have hRX : R ≤ H ⊓ Subgroup.centralizer {α} := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨g1, -, g3⟩ := hg
    refine Subgroup.mem_inf.mpr ⟨hInn ⟨matrixProjectiveProjection Q g,
      (matrixProjectiveConjugationHom_derived Q g).symm⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hgs : ∀ v, matrixLinearEquiv g.val (S v) = S (matrixLinearEquiv g.val v) := by
      intro v
      have h1 : matrixLinearEquiv g.val (N v) = N v := g1 _ ⟨v, rfl⟩
      have h2 : N (matrixLinearEquiv g.val v - v) = 0 := (hker _).1 (g3 v)
      rw [hN] at h1
      rw [map_sub, hN, hN] at h2
      rw [map_sub] at h1
      calc matrixLinearEquiv g.val (S v) = S v - v + matrixLinearEquiv g.val v := by
            rw [← h1]; abel
        _ = S (matrixLinearEquiv g.val v) := by
            rw [← sub_eq_zero]
            rw [show S v - v + matrixLinearEquiv g.val v - S (matrixLinearEquiv g.val v) =
              -(S (matrixLinearEquiv g.val v) - matrixLinearEquiv g.val v - (S v - v)) by abel,
              h2, neg_zero]
    have hpair : matrixIsometryInclusion Q s * matrixDerivedInclusion Q g =
        matrixDerivedInclusion Q g * matrixIsometryInclusion Q s := by
      change matrixIsometryInclusion Q s *
          matrixIsometryInclusion Q (Subgroup.inclusion (matrixDerived_le_isometries Q) g) =
        matrixIsometryInclusion Q (Subgroup.inclusion (matrixDerived_le_isometries Q) g) *
          matrixIsometryInclusion Q s
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      apply matrixLinearIso.injective
      apply LinearEquiv.ext
      intro v
      change matrixLinearEquiv (s.val * g.val) v = matrixLinearEquiv (g.val * s.val) v
      rw [matrixLinearEquiv_mul, matrixLinearEquiv_mul, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply]
      exact (hgs v).symm
    change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) *
        matrixProjectiveConjugationHom Q (matrixDerivedInclusion Q g) =
      matrixProjectiveConjugationHom Q (matrixDerivedInclusion Q g) *
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)
    rw [← map_mul, ← map_mul, hpair]
  have hnorm : ∀ β ∈ H ⊓ Subgroup.centralizer {α},
      β ∈ Subgroup.normalizer (R : Set (MulAut (matrixProjectiveDerived Q))) := by
    rintro β ⟨hβH, hβC⟩
    have hβE : β ∈ (unitKappa Q).range := by
      rw [range_unitKappa Q]
      exact hHE hβH
    obtain ⟨x, rfl⟩ := hβE
    have hxα : matrixProjectiveConjugationHom Q x.1 * α =
        α * matrixProjectiveConjugationHom Q x.1 := by
      have h := Subgroup.mem_centralizer_iff.mp hβC α (Set.mem_singleton α)
      exact h.symm
    have hTS := hcommS x hxα
    set T := coordinateSemilinearMap x.1.val with hTdef
    refine hnormR x.1 ?_ ?_
    · rintro _ ⟨u, rfl⟩
      refine ⟨T u, ?_⟩
      change S (T u) - T u = T (N u)
      rw [hN, map_sub, hTS]
    · intro v hv
      rw [hker] at hv ⊢
      rw [hN] at hv ⊢
      rw [← hTS, ← map_sub, hv, map_zero]
  refine ⟨R, hRX, hnorm, fun r hr => ⟨2, hR4 r hr⟩, fun x hx hxc => ?_⟩
  obtain ⟨k, hk⟩ := hcentR ⟨x, Subgroup.mem_inf.mpr ⟨hxc, hHE hx.1⟩⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

include hQ hT hE in
theorem noNonsolvableClassical_matrixProjectiveDerived :
    NoNonsolvableClassical (matrixProjectiveDerived Q) := by
  intro x hx
  have : Finite (matrixProjectiveDerived Q) := by
    have : Finite (GL (Fin d) K) := inferInstance
    infer_instance
  have hconj := conj_injective_matrixProjectiveDerived hQ hT hE
  obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective Q x
  have hα : MulAut.conj (matrixProjectiveProjection Q g) =
      matrixProjectiveConjugationHom Q
        (matrixIsometryInclusion Q (Subgroup.inclusion (matrixDerived_le_isometries Q) g)) :=
    (matrixProjectiveConjugationHom_derived Q g).symm
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hx
    omega
  have hg2 : g * g = 1 := by
    apply derivedKappa_injective hQ hT hE
    rw [map_mul, map_one, derivedKappa, MonoidHom.comp_apply,
      matrixProjectiveConjugationHom_derived, ← map_mul, ← pow_two, ← hx, pow_orderOf_eq_one,
      map_one]
  have hrank := two_le_rank_of_mem_derived hQ hT hE g hg1 hg2
  obtain ⟨R, hRX, hnorm, hR, hcent⟩ := exists_two_radical_of_two_le_rank hQ hT hE
    (CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q)) le_rfl
    (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨h, rfl⟩ := matrixProjectiveProjection_surjective Q y
      exact ⟨_, matrixProjectiveConjugationHom_derived Q h⟩)
    (Subgroup.inclusion (matrixDerived_le_isometries Q) g)
    (by rw [← hα, orderOf_injective _ hconj]; exact hx) hrank
  rw [← hα] at hRX hnorm hcent
  exact NoNonsolvableClassicalAt.of_two_radical
    (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)) hconj R hRX
    hnorm hR hcent hx

end Regular

theorem noNonsolvableClassical_of_pOmega_model {T : Type} [Group T] {t : StatedLieTag} {n f : ℕ}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (hT : StatedClassicalModel T t n 2 f) :
    NoNonsolvableClassical T := by
  obtain ⟨-, hf, hn⟩ := hT.1
  rcases ht with rfl | rfl
  · obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := hT
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
    have hreg := regular_coordinateQuadPlus n K (by omega)
    have hcomm := commutator_coordinateQuadPlus n K (by omega)
    exact NoNonsolvableClassical.of_mulEquiv (coordinatePlusWitnessEquiv K eT)
      (noNonsolvableClassical_matrixProjectiveDerived hreg.1 hreg.2 hcomm)
  · obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨eT⟩⟩ := hT
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
    have hreg := regular_coordinateQuadMinus n K b c hn hirr
    have hcomm := commutator_coordinateQuadMinus n K b c hn hirr
    exact NoNonsolvableClassical.of_mulEquiv (coordinateMinusWitnessEquiv K (by omega) b c eT)
      (noNonsolvableClassical_matrixProjectiveDerived hreg.1 hreg.2 hcomm)

end CFSG.ClassicalInvolution
