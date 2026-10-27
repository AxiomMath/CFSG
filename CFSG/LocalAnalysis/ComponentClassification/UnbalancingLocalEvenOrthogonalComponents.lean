module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaHigherRank
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalComponentFree
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailCharTwoSign

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  (orthogonal_geometry_char_two_reflection_separation)

namespace EvenOrthogonalComponents

variable {K : Type} [Field K] {d : ℕ}

section Regular

variable [Finite K] [CharP K 2] {Q : QuadraticForm K (Fin d → K)}
  (hQ : Q.polarBilin.Nondegenerate)
  (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q)

omit [Finite K] in
include hQ hT hE in
theorem conj_injective_matrixProjectiveDerived :
    Function.Injective (MulAut.conj : matrixProjectiveDerived Q →*
      MulAut (matrixProjectiveDerived Q)) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective Q y
  have h1 : derivedKappa Q g = 1 := by
    rw [derivedKappa, MonoidHom.comp_apply, matrixProjectiveConjugationHom_derived, hy]
  rw [(derivedKappa_injective hQ hT hE) (h1.trans (map_one _).symm), map_one]

include hQ hT hE in
theorem two_le_rank_of_mem_derived (g : matrixDerived Q) (hg1 : g ≠ 1) (hg2 : g * g = 1) :
    2 ≤ (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1).rank := by
  set S := matrixLinearEquiv (g : GL (Fin d) K) with hSdef
  have hSS : ∀ v, S (S v) = v := fun v => by
    have h := congrArg (fun A : matrixDerived Q => matrixLinearEquiv (A : GL (Fin d) K) v) hg2
    simp only [Subgroup.coe_mul, matrixLinearEquiv_mul, LinearEquiv.mul_apply,
      Subgroup.coe_one] at h
    rw [h]
    exact Matrix.one_mulVec v
  have hiso : ∀ v, Q (S v) = Q v :=
    (mem_matrixIsometries_iff Q _).mp (matrixDerived_le_isometries Q g.2)
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
  have hNM : N = (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1).mulVecLin := by
    apply LinearMap.ext
    intro v
    rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  have hN0 : N ≠ 0 := by
    intro h0
    apply hg1
    apply Subtype.ext
    apply matrixLinearIso.injective
    apply LinearEquiv.ext
    intro v
    have h1 : S v - v = 0 := by rw [← hN, h0, LinearMap.zero_apply]
    rw [sub_eq_zero] at h1
    change S v = matrixLinearEquiv 1 v
    rw [h1]
    exact (Matrix.one_mulVec v).symm
  change 2 ≤ finrank K (LinearMap.range (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) -
    1).mulVecLin)
  rw [← hNM]
  by_contra hlt
  push Not at hlt
  have hne : LinearMap.range N ≠ ⊥ := fun h0 => hN0 (LinearMap.range_eq_bot.mp h0)
  have hrank1 : finrank K (LinearMap.range N) = 1 := by
    have h0 : finrank K (LinearMap.range N) ≠ 0 := fun h => hne (Submodule.finrank_eq_zero.mp h)
    omega
  obtain ⟨⟨v, hvW⟩, hv0, hspan⟩ := finrank_eq_one_iff'.mp hrank1
  have hv0' : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hmult : ∀ x, ∃ c : K, N x = c • v := fun x => by
    obtain ⟨c, hc⟩ := hspan ⟨N x, LinearMap.mem_range_self N x⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y, polar Q v y ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv0' (eq_zero_of_polar_eq_zero hQ hc)
  obtain ⟨l₀, hl₀⟩ := hmult y₀
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = l₀ / polar Q v y₀ := ⟨_, rfl⟩
  have hNx : ∀ x, N x = (μ * polar Q x v) • v := fun x => by
    obtain ⟨c, hc⟩ := hmult x
    have h1 := hadj x y₀
    rw [hc, hl₀, polar_smul_left, polar_smul_right, smul_eq_mul, smul_eq_mul] at h1
    have hc' : c = μ * polar Q x v := by
      rw [hμ, div_mul_eq_mul_div, eq_div_iff hy₀]
      linear_combination h1
    rw [hc, hc']
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hN0
    apply LinearMap.ext
    intro x
    rw [hNx, h0, zero_mul, zero_smul, LinearMap.zero_apply]
  have hQv : μ * Q v = -1 := by
    have h1 := hiso y₀
    have hS : S y₀ = y₀ + (μ * polar Q y₀ v) • v := by
      rw [← hNx, hN]
      abel
    rw [hS, QuadraticMap.map_add (⇑Q) y₀, QuadraticMap.map_smul, polar_smul_right] at h1
    have hb : polar Q y₀ v = polar Q v y₀ := polar_comm Q y₀ v
    rw [hb, smul_eq_mul] at h1
    have h2 : μ * polar Q v y₀ * polar Q v y₀ * (1 + μ * Q v) = 0 := by linear_combination h1
    have hb0 : polar Q v y₀ ≠ 0 := hy₀
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exfalso
      exact mul_ne_zero (mul_ne_zero hμ0 hb0) hb0 h3
    · linear_combination h3
  have hQv0 : Q v ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hQv
    exact one_ne_zero (neg_eq_zero.mp hQv.symm)
  have hSv : S = reflect Q v := by
    apply LinearEquiv.ext
    intro x
    rw [reflect_apply hQv0]
    have hS : S x = x + N x := by rw [hN]; abel
    rw [hS, hNx, polar_comm Q x v]
    have hμ' : μ = -(Q v)⁻¹ := by
      field_simp
      linear_combination hQv
    rw [hμ', sub_eq_add_neg, ← neg_smul]
    congr 2
    field_simp
  have hSE : S ∈ elementaryGroup Q := by
    rw [← hE]
    have hmap : (matrixDerived Q).map matrixLinearIso.toMonoidHom ≤
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
      rw [matrixDerived, Subgroup.map_commutator]
      exact Subgroup.commutator_mono (Subgroup.map_comap_le _ _) (Subgroup.map_comap_le _ _)
    exact hmap ⟨g, g.2, rfl⟩
  obtain ⟨-, -, -, hsep⟩ := orthogonal_geometry_char_two_reflection_separation hQ hT
  exact hsep v hQv0 (hSv ▸ hSE)

include hQ hT hE in
theorem no_component_of_two_le_rank
    (H : Subgroup (MulAut (matrixProjectiveDerived Q)))
    (hInn : CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ H)
    (hHE : H ≤ matrixProjectiveImage Q) (s : matrixIsometries Q)
    (hs2 : orderOf (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) = 2)
    (hrank : 2 ≤ (((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1).rank) :
    ∀ B : Subgroup ↥(H ⊓ Subgroup.centralizer
      {matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)}), ¬ IsComponent B := by
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
  refine ComponentFree.no_component_of_two_radical hRX hnorm (fun r hr => ⟨2, hR4 r hr⟩)
    fun x hx hxc => ?_
  obtain ⟨k, hk⟩ := hcentR ⟨x, Subgroup.mem_inf.mpr ⟨hxc, hHE hx.1⟩⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

include hQ hT hE in
theorem no_component_inner_centralizer (x : matrixProjectiveDerived Q) (hx : orderOf x = 2) :
    ∀ B : Subgroup ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixProjectiveDerived Q) ⊓ Subgroup.centralizer ({MulAut.conj x} : Set _)),
      ¬ IsComponent B := by
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
  rw [hα]
  refine no_component_of_two_le_rank hQ hT hE _ le_rfl ?_ _ ?_ hrank
  · rintro _ ⟨y, rfl⟩
    obtain ⟨h, rfl⟩ := matrixProjectiveProjection_surjective Q y
    exact ⟨_, matrixProjectiveConjugationHom_derived Q h⟩
  · rw [← hα, orderOf_injective _ hconj]
    exact hx

end Regular

end EvenOrthogonalComponents

open EvenOrthogonalComponents

theorem even_orthogonal_involution_centralizers_component_free {T : Type} [Group T]
    {t : StatedLieTag} {n f : ℕ} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (hn : 4 ≤ n)
    (hf : 1 ≤ f) (hT : StatedClassicalModel T t n 2 f) (u : T) (hu : orderOf u = 2) :
    ∀ B : Subgroup (Subgroup.centralizer ({u} : Set T)), ¬ IsComponent B := by
  rcases ht with rfl | rfl
  · obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := hT
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
    have hreg := regular_coordinateQuadPlus n K (by omega)
    have hcomm := commutator_coordinateQuadPlus n K (by omega)
    set e := coordinatePlusWitnessEquiv K eT
    refine ComponentFree.no_component_centralizer e
      (conj_injective_matrixProjectiveDerived hreg.1 hreg.2 hcomm) u ?_
    exact no_component_inner_centralizer hreg.1 hreg.2 hcomm (e u)
      ((orderOf_injective e.toMonoidHom e.injective u).trans hu)
  · obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨eT⟩⟩ := hT
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
    have hreg := regular_coordinateQuadMinus n K b c hn hirr
    have hcomm := commutator_coordinateQuadMinus n K b c hn hirr
    set e := coordinateMinusWitnessEquiv K (by omega) b c eT
    refine ComponentFree.no_component_centralizer e
      (conj_injective_matrixProjectiveDerived hreg.1 hreg.2 hcomm) u ?_
    exact no_component_inner_centralizer hreg.1 hreg.2 hcomm (e u)
      ((orderOf_injective e.toMonoidHom e.injective u).trans hu)

end CFSG.ComponentClassification.UnbalancingLocal
