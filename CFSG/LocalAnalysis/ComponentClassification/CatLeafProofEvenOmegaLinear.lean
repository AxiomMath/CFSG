module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSLGraph
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenOrthogonalComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaLinearInvolution

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical

variable {K : Type} [Field K] {d : ℕ}

section Regular

variable [Finite K] [CharP K 2] {Q : QuadraticForm K (Fin d → K)}
  (hQ : Q.polarBilin.Nondegenerate)
  (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q)

omit [Finite K] in
include hQ hT hE in
theorem inner_inf_centralizer_kappa (s : matrixIsometries Q) :
    inner (matrixProjectiveDerived Q) ⊓
        centralizer {matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)} =
      ((matrixDerived Q ⊓ centralizer {(s : GL (Fin d) K)}).subgroupOf
        (matrixIsometries Q)).map
          ((matrixProjectiveConjugationHom Q).comp (matrixIsometryInclusion Q)) := by
  have hκ := isometryKappa_injective hQ hT hE
  ext x
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective Q y
    rw [← matrixProjectiveConjugationHom_derived] at hy ⊢
    refine ⟨Subgroup.inclusion (matrixDerived_le_isometries Q) g, ?_, rfl⟩
    have h1 := mem_centralizer_singleton_iff.mp hy
    have h2 : Subgroup.inclusion (matrixDerived_le_isometries Q) g * s =
        s * Subgroup.inclusion (matrixDerived_le_isometries Q) g := by
      apply hκ
      simp only [MonoidHom.comp_apply, map_mul]
      exact h1
    refine ⟨g.2, mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val h2
  · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
    have h2 : a * s = s * a := Subtype.ext (mem_centralizer_singleton_iff.mp ha2)
    refine ⟨⟨matrixProjectiveProjection Q ⟨a, ha1⟩, ?_⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    · rw [← matrixProjectiveConjugationHom_derived]
      rfl
    · change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q a) *
          matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) *
          matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q a)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, h2]

omit [Finite K] in
include hQ hT hE in
theorem nonempty_fixed_kappa_equiv (s : matrixIsometries Q) :
    Nonempty (fixedSubgroup (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) ≃*
      ↥(matrixDerived Q ⊓ centralizer {(s : GL (Fin d) K)})) := by
  have hcj := UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
    hQ hT hE
  exact ⟨((fixedInnerEquiv hcj _).trans ((MulEquiv.subgroupCongr
    (inner_inf_centralizer_kappa hQ hT hE s)).trans
      (Subgroup.equivMapOfInjective _ _ (isometryKappa_injective hQ hT hE)).symm)).trans
    (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans (matrixDerived_le_isometries Q)))⟩

include hQ hT hE in
theorem isCharacteristicP_inner_centralizer_of_two_le_rank (s : matrixIsometries Q)
    (hs2 : orderOf (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) = 2)
    (hrank : 2 ≤ (((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1).rank) :
    IsCharacteristicP 2 ↥(inner (matrixProjectiveDerived Q) ⊓ Subgroup.centralizer
      {matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)}) := by
  have hd : 1 ≤ d := by have := six_le hQ hT; omega
  have := finite_mulAut_matrixProjectiveDerived Q
  set H := inner (matrixProjectiveDerived Q) with hHdef
  have hInn : inner (matrixProjectiveDerived Q) ≤ H := le_rfl
  have hHE : H ≤ matrixProjectiveImage Q := matrixProjective_inner_le_image Q
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
  refine RankTwoChar2C0.isCharacteristicP_of_le_normalizer hRX
    (fun r => ⟨2, Subtype.ext (by simpa using hR4 r r.2)⟩) hnorm fun x hx hxc => ?_
  obtain ⟨k, hk⟩ := hcentR ⟨x, Subgroup.mem_inf.mpr ⟨hxc, hHE hx.1⟩⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end Regular

variable [Finite K] {f n : ℕ}

theorem even_omega_symmetry_fixed_equiv (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {v : Fin (2 * n) → K} (hv : Q v = 1)
    (hout : symmetryAut Q v ∉ inner (matrixProjectiveDerived Q)) :
    Nonempty (fixedSubgroup (symmetryAut Q v) ≃* StatedSp (n - 1) K) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨-, -, halt, hnd, hdim, ρ, -, -, hker, hmapD, -⟩ :=
    evenOrthogonalSymmetryCentralizer_of_regular hf hK (by omega) Q hQ hT hE v hv
  obtain ⟨e₁⟩ := nonempty_fixed_kappa_equiv hQ hT hE (symmetryIsometry Q v)
  have hsD : symmetryGL Q v ∉ matrixDerived Q := fun h => hout (by
    refine ⟨matrixProjectiveProjection Q ⟨symmetryGL Q v, h⟩, ?_⟩
    rw [← matrixProjectiveConjugationHom_derived]
    rfl)
  set D := (matrixDerived Q ⊓ symmetryCentralizer Q v).subgroupOf (symmetryCentralizer Q v)
    with hDdef
  have hinj : Function.Injective (ρ.comp D.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxk : (x : symmetryCentralizer Q v) ∈ ρ.ker := hx
    rw [hker, mem_zpowers_iff] at hxk
    obtain ⟨i, hi⟩ := hxk
    have hsq : (⟨symmetryGL Q v, symmetryGL_mem_symmetryCentralizer⟩ :
        symmetryCentralizer Q v) * ⟨symmetryGL Q v, symmetryGL_mem_symmetryCentralizer⟩ = 1 :=
      Subtype.ext (symmetryGL_mul_self Q v)
    rcases Int.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [← two_mul, _root_.zpow_mul, zpow_two, hsq, _root_.one_zpow] at hi
      exact Subtype.ext hi.symm
    · exfalso
      rw [_root_.zpow_add, _root_.zpow_mul, zpow_two, hsq, _root_.one_zpow, one_mul, zpow_one] at hi
      have hxD := (mem_subgroupOf.mp x.2).1
      rw [← hi] at hxD
      exact hsD hxD
  have hrange : (ρ.comp D.subtype).range =
      LocalAnalysis.ComponentInitial.bilinIsometryGroup (vQuotForm Q v) := by
    rw [MonoidHom.range_comp, range_subtype, hDdef, hmapD]
  have heq : matrixDerived Q ⊓ centralizer {((symmetryIsometry Q v : matrixIsometries Q) :
      GL (Fin (2 * n)) K)} = matrixDerived Q ⊓ symmetryCentralizer Q v := by
    rw [symmetryCentralizer, ← inf_assoc, inf_eq_left.mpr (matrixDerived_le_isometries Q)]
  have hdimU : Module.finrank K (vQuot Q v) = 2 * (n - 1) := by omega
  obtain ⟨eSp⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp (vQuotForm Q v) halt hnd
    hdimU
  have : Finite (GL (Fin (n - 1) ⊕ Fin (n - 1)) K) :=
    Finite.of_injective Units.val Units.val_injective
  exact ⟨((e₁.trans (MulEquiv.subgroupCongr heq)).trans
      ((Subgroup.subgroupOfEquivOfLe inf_le_right).symm.trans
        ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)))).trans
      ((bilinIsometryGroupEquiv _).trans eSp)⟩

theorem even_omega_symmetry_evenLieConclusion (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {v : Fin (2 * n) → K} (hv : Q v = 1)
    (hout : symmetryAut Q v ∉ inner (matrixProjectiveDerived Q))
    (M : Subgroup (fixedSubgroup (symmetryAut Q v))) (hM : IsPComponent 2 M) :
    EvenLieConclusion M := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite (GL (Fin (n - 1) ⊕ Fin (n - 1)) K) :=
    Finite.of_injective Units.val Units.val_injective
  obtain ⟨Φ⟩ := even_omega_symmetry_fixed_equiv hf hK hn hQ hT hE hv hout
  exact evenLieConclusion_of_mulEquiv Φ
    (fun M' hM' => evenLieConclusion_statedSp hf hK (by omega) M' hM') hM

theorem even_omega_linear_fixed_cases (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (s : matrixIsometries Q)
    (hs2 : orderOf (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) = 2)
    (hout : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) ∉
      inner (matrixProjectiveDerived Q)) :
    IsCharacteristicP 2
        (fixedSubgroup (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s))) ∨
      Nonempty (fixedSubgroup (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) ≃*
        StatedSp (n - 1) K) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hss : s * s = 1 := by
    apply isometryKappa_injective hQ hT hE
    rw [map_mul, map_one]
    change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) *
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) = 1
    have h2 := pow_orderOf_eq_one
      (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s))
    rw [hs2] at h2
    rw [← pow_two]
    exact h2
  have hs1 : (s : GL (Fin (2 * n)) K) ≠ 1 := by
    intro h
    have h1 : s = 1 := Subtype.ext h
    rw [h1, map_one, map_one, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  by_cases hr : 2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank
  · left
    have hcj := UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
      hQ hT hE
    exact LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv (fixedInnerEquiv hcj _).symm
      (isCharacteristicP_inner_centralizer_of_two_le_rank hQ hT hE s hs2 hr)
  · obtain ⟨v, hv, hsv⟩ := exists_symmetry_of_rank_le_one hQ s.2
      (congrArg Subtype.val hss) hs1 (by omega)
    have hincl : s = symmetryIsometry Q v := Subtype.ext hsv
    subst hincl
    exact Or.inr (even_omega_symmetry_fixed_equiv hf hK hn hQ hT hE hv hout)

theorem even_omega_linear_evenLieConclusion (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (s : matrixIsometries Q)
    (hs2 : orderOf (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) = 2)
    (hout : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) ∉
      inner (matrixProjectiveDerived Q))
    (M : Subgroup (fixedSubgroup (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s))))
    (hM : IsPComponent 2 M) : EvenLieConclusion M := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite (GL (Fin (n - 1) ⊕ Fin (n - 1)) K) :=
    Finite.of_injective Units.val Units.val_injective
  rcases even_omega_linear_fixed_cases hf hK hn hQ hT hE s hs2 hout with hch | ⟨⟨Φ⟩⟩
  · exact absurd hM (not_isPComponent_of_isCharacteristicP hch M)
  · exact evenLieConclusion_of_mulEquiv Φ
      (fun M' hM' => evenLieConclusion_statedSp hf hK (by omega) M' hM') hM

end CFSG.ComponentClassification.CatLeafProof
