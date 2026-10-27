module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaFlagRadical
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace OmegaRadical

theorem eq_one_of_mem_oddCore_of_two_pow {G : Type*} [Group G] [Finite G] {x : G}
    (hx : x ∈ CFSG.oddCore G) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card (CFSG.oddCore G) := Subgroup.orderOf_dvd_natCard _ hx
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (CFSG.oddCore G)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr EvenCatalog.odd_card_oddCore)
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

theorem oddCore_eq_bot_of_radical {M : Type*} [Group M] [Finite M] {X R : Subgroup M}
    (hRX : R ≤ X) (hnorm : ∀ x ∈ X, x ∈ Subgroup.normalizer (R : Set M))
    (hR : ∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k = 1)
    (hcent : ∀ x ∈ X, x ∈ Subgroup.centralizer (R : Set M) → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    CFSG.oddCore X = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  have hqR : (q : M) ∈ Subgroup.centralizer (R : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    set c : X := q * ⟨r, hRX hr⟩ * q⁻¹ * (⟨r, hRX hr⟩ : X)⁻¹
    have hcQ : c ∈ CFSG.oddCore X := by
      have h1 : (⟨r, hRX hr⟩ : X) * q⁻¹ * (⟨r, hRX hr⟩ : X)⁻¹ ∈ CFSG.oddCore X :=
        (inferInstance : (CFSG.oddCore X).Normal).conj_mem _ (inv_mem hq) _
      have h2 := mul_mem hq h1
      rwa [show q * ((⟨r, hRX hr⟩ : X) * q⁻¹ * (⟨r, hRX hr⟩ : X)⁻¹) = c by
        simp only [c]; group] at h2
    have hcR : (c : M) ∈ R := by
      have h1 : (q : M) * r * (q : M)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hnorm q q.2) r).mp hr
      have h2 := mul_mem h1 (inv_mem hr)
      simpa [c] using h2
    obtain ⟨k, hk⟩ := hR _ hcR
    have hc1 : c = 1 :=
      eq_one_of_mem_oddCore_of_two_pow hcQ (Subtype.ext (by simpa using hk))
    have hc1' : (q : M) * r * (q : M)⁻¹ * r⁻¹ = 1 := by
      simpa [c] using congrArg Subtype.val hc1
    have := mul_inv_eq_one.mp hc1'
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  obtain ⟨k, hk⟩ := hcent _ q.2 hqR
  exact eq_one_of_mem_oddCore_of_two_pow hq (Subtype.ext (by simpa using hk))

variable {K : Type} [Field K] {d : ℕ}

theorem finite_mulAut_matrixProjectiveDerived [Finite K] (Q : QuadraticForm K (Fin d → K)) :
    Finite (MulAut (matrixProjectiveDerived Q)) :=
  Finite.of_injective (fun e : MulAut (matrixProjectiveDerived Q) =>
    (e : matrixProjectiveDerived Q → matrixProjectiveDerived Q))
    fun _ _ hab => MulEquiv.ext (congrFun hab)

@[expose] def HigherRankOddCore (Q : QuadraticForm K (Fin d → K)) : Prop :=
  ∀ H : Subgroup (MulAut (matrixProjectiveDerived Q)), inner (matrixProjectiveDerived Q) ≤ H →
    H ≤ matrixProjectiveImage Q → ∀ s : matrixIsometries Q,
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) ∈ H →
      orderOf (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) = 2 →
      2 ≤ (((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1).rank →
      CFSG.oddCore ↥(H ⊓ Subgroup.centralizer
        {matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)}) = ⊥

section Regular

variable [Finite K] [CharP K 2] {Q : QuadraticForm K (Fin d → K)}
  (hQ : Q.polarBilin.Nondegenerate)
  (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q)

omit [Finite K] in
include hQ hT hE in
theorem isometryKappa_injective :
    Function.Injective ((matrixProjectiveConjugationHom Q).comp (matrixIsometryInclusion Q)) := by
  have hd : 1 ≤ d := by have := six_le hQ hT; omega
  rw [injective_iff_map_eq_one]
  intro A hA
  have hmem : matrixIsometryInclusion Q A ∈ unitMultiplierPairs Q := fun v => by
    rw [matrixIsometryInclusion_val, coordinateSemilinearMap_inl]
    exact (mem_matrixIsometries_iff Q A.val).mp A.2 v
  have h1 := eq_one_of_kappa_eq_one Q hQ hT hE hd hmem hA
  exact matrixIsometryInclusion_injective Q (h1.trans (map_one _).symm)

include hQ hT hE in
theorem higherRankOddCore_of_regular : HigherRankOddCore Q := by
  have hd : 1 ≤ d := by have := six_le hQ hT; omega
  have := finite_mulAut_matrixProjectiveDerived Q
  intro H hInn hHE s hsH hs2 hrank
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
  refine oddCore_eq_bot_of_radical hRX hnorm (fun r hr => ⟨2, hR4 r hr⟩) fun x hx hxc => ?_
  obtain ⟨k, hk⟩ := hcentR ⟨x, Subgroup.mem_inf.mpr ⟨hxc, hHE hx.1⟩⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end Regular

end OmegaRadical

open OmegaRadical in
theorem even_orthogonal_higher_rank_linear_involution_odd_core (G : Type) [Group G]
    (t : StatedLieTag) (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (n f : ℕ)
    (h : StatedClassicalModel G t n 2 f) :
    match t with
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)),
          HigherRankOddCore (coordinateQuadPlus n K)
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)),
          HigherRankOddCore (coordinateQuadMinus n K hn b c)
    | _ => False := by
  rcases ht with rfl | rfl
  · obtain ⟨-, hf, hn⟩ := h.1
    intro K _ _ hK _
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
    have hreg := regular_coordinateQuadPlus n K (by omega)
    exact higherRankOddCore_of_regular hreg.1 hreg.2
      (commutator_coordinateQuadPlus n K (by omega))
  · obtain ⟨-, hf, hn⟩ := h.1
    intro hn1 K _ _ hK b c hirr _
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
    have hreg := regular_coordinateQuadMinus n K b c hn hirr
    exact higherRankOddCore_of_regular hreg.1 hreg.2
      (commutator_coordinateQuadMinus n K b c hn hirr)

end CFSG.ComponentClassification.UnbalancedCatalog
