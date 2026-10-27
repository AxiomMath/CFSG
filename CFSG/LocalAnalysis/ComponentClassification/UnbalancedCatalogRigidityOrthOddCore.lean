module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityAlternating
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthRestrict

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer (mem_matrixDerived_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs
  mem_unitMultiplierPairs_iff)

variable {K : Type} [Field K] {d : ℕ}

abbrev derivedSymmetryCentralizer (Q : QuadraticForm K (Fin d → K)) (v : Fin d → K) :
    Subgroup (GL (Fin d) K) :=
  matrixDerived Q ⊓ symmetryCentralizer Q v

abbrev symmetryIsometry (Q : QuadraticForm K (Fin d → K)) (v : Fin d → K) :
    matrixIsometries Q :=
  ⟨symmetryGL Q v, symmetryGL_mem Q v⟩

abbrev symmetryAut (Q : QuadraticForm K (Fin d → K)) (v : Fin d → K) :
    MulAut (matrixProjectiveDerived Q) :=
  matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q (symmetryIsometry Q v))

theorem symmetryAut_sq (Q : QuadraticForm K (Fin d → K)) (v : Fin d → K) :
    symmetryAut Q v ^ 2 = 1 := by
  have h : symmetryIsometry Q v * symmetryIsometry Q v = 1 :=
    Subtype.ext (symmetryGL_mul_self Q v)
  simp only [symmetryAut, pow_two, ← map_mul, h, map_one]

variable {Q : QuadraticForm K (Fin d → K)}

theorem symmetryGL_mul_mem_matrixDerived [CharP K 2]
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {z v : Fin d → K} (hz : Q z = 1) (hv : Q v = 1)
    (hzv : polar Q z v = 0) : symmetryGL Q z * symmetryGL Q v ∈ matrixDerived Q := by
  rw [mem_matrixDerived_iff, map_mul, matrixLinearIso_symmetryGL, matrixLinearIso_symmetryGL,
    reflect_mul_reflect_eq_eichler hz hv hzv, hE]
  exact eichler_mem_elementaryGroup Q _ _

theorem symmetryGL_mem_symmetryCentralizer_of [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    {z v : Fin d → K} (hz : Q z = 1) (hv : Q v = 1) (hzv : polar Q z v = 0) :
    symmetryGL Q z ∈ symmetryCentralizer Q v :=
  ⟨symmetryGL_mem Q z, (mem_centralizer_symmetryGL_iff hQ hv (symmetryGL_mem Q z)).mpr (by
    rw [symmetryGL_mulVec_of_charTwo hz, hzv, zero_smul, add_zero])⟩

abbrev conjIsometry (S : similarityPairs Q) (g : matrixIsometries Q) : matrixIsometries Q :=
  ⟨matrixConjugation S.val g, matrixConjugation_mem_isometries Q S g g.2⟩

theorem conj_inclusion_eq (S : similarityPairs Q) (g : matrixIsometries Q) :
    S * matrixIsometryInclusion Q g * S⁻¹ = matrixIsometryInclusion Q (conjIsometry S g) := by
  apply Subtype.ext
  change _ = SemidirectProduct.inl (matrixConjugation S.val g)
  rw [matrixConjugation_inl]
  rfl

theorem conj_kappa_inclusion (S : similarityPairs Q) (g : matrixIsometries Q) :
    matrixProjectiveConjugationHom Q S *
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g) *
          (matrixProjectiveConjugationHom Q S)⁻¹ =
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q (conjIsometry S g)) := by
  rw [← conj_inclusion_eq, map_mul, map_mul, map_inv]

theorem semilinear_commute_of_conj_eq {S : similarityPairs Q} {g : matrixIsometries Q}
    (h : S * matrixIsometryInclusion Q g * S⁻¹ = matrixIsometryInclusion Q g) (x : Fin d → K) :
    coordinateSemilinearMap S.val (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ x) =
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ coordinateSemilinearMap S.val x := by
  have h1 : S * matrixIsometryInclusion Q g = matrixIsometryInclusion Q g * S :=
    mul_inv_eq_iff_eq_mul.mp h
  have h2 := congrArg (fun y : similarityPairs Q => coordinateSemilinearMap y.val x) h1
  simp only [Subgroup.coe_mul, coordinateSemilinearMap_mul, matrixIsometryInclusion_val,
    coordinateSemilinearMap_inl, matrixLinearEquiv_apply] at h2
  exact h2

theorem conjIsometry_mem {S : similarityPairs Q} {v : Fin d → K}
    (hSv : S * matrixIsometryInclusion Q (symmetryIsometry Q v) * S⁻¹ =
      matrixIsometryInclusion Q (symmetryIsometry Q v))
    {g : matrixIsometries Q} (hg : (g : GL (Fin d) K) ∈ derivedSymmetryCentralizer Q v) :
    (conjIsometry S g : GL (Fin d) K) ∈ derivedSymmetryCentralizer Q v := by
  have hs : matrixConjugation S.val (symmetryGL Q v) = symmetryGL Q v := by
    have h1 := conj_inclusion_eq S (symmetryIsometry Q v)
    rw [hSv] at h1
    exact (congrArg Subtype.val (matrixIsometryInclusion_injective Q h1)).symm
  refine ⟨?_, (conjIsometry S g).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  · change matrixConjugation S.val g ∈ matrixDerived Q
    rw [← matrixDerived_invariant Q S]
    exact Subgroup.mem_map_of_mem _ hg.1
  · change matrixConjugation S.val g * symmetryGL Q v =
      symmetryGL Q v * matrixConjugation S.val g
    have hgs : (g : GL (Fin d) K) * symmetryGL Q v = symmetryGL Q v * g :=
      Subgroup.mem_centralizer_singleton_iff.mp hg.2.2
    rw [← hs, ← map_mul, hgs, map_mul]

section Regular

variable [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
  (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q)
include hQ hT hE

theorem conj_inclusion_eq_of_commute (hd : 1 ≤ d) {S : similarityPairs Q}
    (hS : S ∈ unitMultiplierPairs Q) {g : matrixIsometries Q}
    (hc : Commute (matrixProjectiveConjugationHom Q S)
      (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g))) :
    S * matrixIsometryInclusion Q g * S⁻¹ = matrixIsometryInclusion Q g :=
  kappa_eq_of_unit hQ hT hE hd
    (mul_mem (mul_mem hS (inclusion_mem_unitMultiplierPairs g)) (inv_mem hS))
    (inclusion_mem_unitMultiplierPairs g)
    (by rw [map_mul, map_mul, map_inv, hc.eq, mul_inv_cancel_right])

variable [Finite K]

theorem eq_one_or_eq_of_commute (hd : 3 ≤ d) {v : Fin d → K} (hv : Q v = 1)
    {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q)
    (hα : Commute (matrixProjectiveConjugationHom Q S) (symmetryAut Q v))
    (hN : ∀ g : matrixIsometries Q, (g : GL (Fin d) K) ∈ derivedSymmetryCentralizer Q v →
      Commute (matrixProjectiveConjugationHom Q S)
        (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g))) :
    S = 1 ∨ S = matrixIsometryInclusion Q (symmetryIsometry Q v) := by
  have hd1 : 1 ≤ d := by omega
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hvv : polar Q v v = 0 := by rw [polar_self, hv, two_nsmul, CharTwo.add_self_eq_zero]
  have hSv := conj_inclusion_eq_of_commute hQ hT hE hd1 hS hα
  have hTv : coordinateSemilinearMap S.val v = v := by
    have hc := semilinear_commute_of_conj_eq hSv
    exact semilinear_apply_eq_of_commute_symmetry hQ hv hS hc
  have hfix : ∀ z, Q z = 1 → polar Q z v = 0 → coordinateSemilinearMap S.val z = z := by
    intro z hz hzv
    have hmem : ((symmetryIsometry Q z * symmetryIsometry Q v : matrixIsometries Q) :
        GL (Fin d) K) ∈ derivedSymmetryCentralizer Q v :=
      ⟨symmetryGL_mul_mem_matrixDerived hE hz hv hzv,
        mul_mem (symmetryGL_mem_symmetryCentralizer_of hQ hz hv hzv)
          symmetryGL_mem_symmetryCentralizer⟩
    have h1 := conj_inclusion_eq_of_commute hQ hT hE hd1 hS (hN _ hmem)
    rw [map_mul] at h1
    have h2 : S * matrixIsometryInclusion Q (symmetryIsometry Q z) * S⁻¹ =
        matrixIsometryInclusion Q (symmetryIsometry Q z) := by
      calc S * matrixIsometryInclusion Q (symmetryIsometry Q z) * S⁻¹
          _ = (S * (matrixIsometryInclusion Q (symmetryIsometry Q z) *
              matrixIsometryInclusion Q (symmetryIsometry Q v)) * S⁻¹) *
                (S * matrixIsometryInclusion Q (symmetryIsometry Q v) * S⁻¹)⁻¹ := by group
          _ = _ := by rw [h1, hSv, mul_inv_cancel_right]
    have hc := semilinear_commute_of_conj_eq h2
    exact semilinear_apply_eq_of_commute_symmetry hQ hz hS hc
  have hperp : ∀ u, polar Q v u = 0 → ∃ a : K, coordinateSemilinearMap S.val u = u + a • v := by
    intro u hu
    obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (1 + Q u)
    have hz : Q (u + b • v) = 1 := by
      have h1 := QuadraticMap.map_add Q u (b • v)
      rw [QuadraticMap.map_smul, hv, polar_smul_right, polar_comm, hu, smul_eq_mul,
        smul_eq_mul] at h1
      rw [h1]
      linear_combination -hb + Q u * h22
    have hzv : polar Q (u + b • v) v = 0 := by
      rw [polar_add_left, polar_smul_left, polar_comm, hu, hvv, smul_zero, add_zero]
    have h1 := hfix _ hz hzv
    rw [map_add, coordinateSemilinearMap_smul, hTv] at h1
    exact ⟨b - S.val.right b, by linear_combination (norm := module) h1⟩
  obtain ⟨u₀, hu₀v, hu₀⟩ : ∃ u₀ : Fin d → K, polar Q v u₀ = 0 ∧ u₀ ∉ K ∙ v := by
    have hpos : 0 < Module.finrank K (vQuot Q v) := by
      have := finrank_vQuot hQ hv
      omega
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨x, (mem_vPerp Q v).mp x.2, fun hmem => hx ((Submodule.Quotient.mk_eq_zero _).mpr hmem)⟩
  have hσ : S.val.right = 1 := by
    refine RingEquiv.ext fun c => ?_
    change S.val.right c = c
    obtain ⟨a, ha⟩ := hperp u₀ hu₀v
    obtain ⟨a', ha'⟩ := hperp (c • u₀) (by rw [polar_smul_right, hu₀v, smul_zero])
    rw [coordinateSemilinearMap_smul, ha] at ha'
    by_contra hne
    apply hu₀
    have hne' : S.val.right c - c ≠ 0 := sub_ne_zero.mpr hne
    have h1 : (S.val.right c - c) • u₀ = (a' - S.val.right c * a) • v := by
      linear_combination (norm := module) ha'
    refine Submodule.mem_span_singleton.mpr ⟨(S.val.right c - c)⁻¹ * (a' - S.val.right c * a), ?_⟩
    rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hne', one_smul]
  obtain ⟨A, hAdef⟩ : ∃ A, S.val.left = A := ⟨_, rfl⟩
  have hTA : ∀ x, coordinateSemilinearMap S.val x = (A : Matrix (Fin d) (Fin d) K) *ᵥ x := by
    intro x
    rw [coordinateSemilinearMap_apply, hσ, hAdef]
    rfl
  have hA : A ∈ matrixIsometries Q := by
    rw [mem_matrixIsometries_iff]
    intro x
    rw [matrixLinearEquiv_apply, ← hTA, (mem_unitMultiplierPairs_iff Q S).mp hS x, hσ]
    rfl
  have hSA : S = matrixIsometryInclusion Q ⟨A, hA⟩ := by
    apply Subtype.ext
    rw [matrixIsometryInclusion_val]
    exact SemidirectProduct.ext hAdef hσ
  have hAv : (A : Matrix (Fin d) (Fin d) K) *ᵥ v = v := by rw [← hTA, hTv]
  have hAc : A ∈ symmetryCentralizer Q v :=
    ⟨hA, (mem_centralizer_symmetryGL_iff hQ hv hA).mpr hAv⟩
  have hres : symmetryRestrict hQ hv ⟨A, hAc⟩ = 1 := by
    apply Units.ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [symmetryRestrict_mk, Units.val_one, Module.End.one_apply, Submodule.Quotient.eq]
      obtain ⟨a, ha⟩ := hperp x ((mem_vPerp Q v).mp x.2)
      refine Submodule.mem_comap.mpr (Submodule.mem_span_singleton.mpr ⟨a, ?_⟩)
      change a • v = (A : Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K) - x
      rw [← hTA, ha, add_sub_cancel_left]
  rcases eq_one_or_eq_symmetryGL_of_restrict_eq_one hQ hv hres with h | h
  · left
    have h1 : (⟨A, hA⟩ : matrixIsometries Q) = 1 := Subtype.ext h
    rw [hSA, h1, map_one]
  · right
    have h1 : (⟨A, hA⟩ : matrixIsometries Q) = symmetryIsometry Q v := Subtype.ext h
    rw [hSA, h1]

end Regular

theorem oddCore_derivedSymmetryCentralizer {f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hdn : d = 2 * n) (hn : 3 ≤ n) [CharP K 2] [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {v : Fin d → K} (hv : Q v = 1) :
    CFSG.oddCore (derivedSymmetryCentralizer Q v) = ⊥ := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have hle : derivedSymmetryCentralizer Q v ≤ symmetryCentralizer Q v := fun g hg => hg.2
  set φ : derivedSymmetryCentralizer Q v →* bilinIsometryGroup (vQuotForm Q v) :=
    ((symmetryRestrict hQ hv).comp (Subgroup.inclusion hle)).codRestrict _
      (fun g => symmetryRestrict_mem hQ hv _) with hφ
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨g, hg, hgy⟩ : y.val ∈ ((derivedSymmetryCentralizer Q v).subgroupOf
        (symmetryCentralizer Q v)).map (symmetryRestrict hQ hv) := by
      rw [map_derived_symmetryRestrict hQ hv hE]
      exact y.2
    exact ⟨⟨g, Subgroup.mem_subgroupOf.mp hg⟩, Subtype.ext hgy⟩
  have hSp : CFSG.oddCore (bilinIsometryGroup (vQuotForm Q v)) = ⊥ := by
    have hdim : Module.finrank K (vQuot Q v) = 2 * (n - 1) := by
      have := finrank_vQuot hQ hv
      omega
    exact EvenCatalog.oddCore_eq_bot_of_mulEquiv (bilinIsometryGroupEquiv _).symm
      (oddCore_isometryGroup_eq_bot_of_isAlt hf hK _ (vQuotForm_isAlt Q v)
        (vQuotForm_nondegenerate hQ hv0) hdim (by omega) (Or.inl (by omega)))
  refine oddCore_eq_bot_of_surjective φ hsurj hSp fun x hx => ?_
  have hx1 : symmetryRestrict hQ hv (Subgroup.inclusion hle x) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rcases eq_one_or_eq_symmetryGL_of_restrict_eq_one hQ hv hx1 with h | h
  · have h1 : x = 1 := Subtype.ext h
    rw [h1, one_pow]
  · apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two, Subgroup.coe_one]
    change (x : GL (Fin d) K) * x = 1
    rw [show (x : GL (Fin d) K) = symmetryGL Q v from h, symmetryGL_mul_self]

theorem oddCore_centralizer_symmetryAut {f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hdn : d = 2 * n) (hn : 3 ≤ n) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {v : Fin d → K} (hv : Q v = 1)
    (H : Subgroup (MulAut (matrixProjectiveDerived Q)))
    (hInn : (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range
      ≤ H)
    (hHE : H ≤ matrixProjectiveImage Q) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {symmetryAut Q v}) = ⊥ := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hd : 1 ≤ d := by omega
  have hd3 : 3 ≤ d := by omega
  set Y := H ⊓ Subgroup.centralizer {symmetryAut Q v} with hY
  have hle : derivedSymmetryCentralizer Q v ≤ matrixIsometries Q := fun g hg => hg.2.1
  set ψ : derivedSymmetryCentralizer Q v →* MulAut (matrixProjectiveDerived Q) :=
    (matrixProjectiveConjugationHom Q).comp
      ((matrixIsometryInclusion Q).comp (Subgroup.inclusion hle)) with hψ
  have hψinj : Function.Injective ψ :=
    (kappa_inclusion_injective hQ hT hE hd).comp (Subgroup.inclusion_injective hle)
  have hNY : ψ.range ≤ Y := by
    rintro _ ⟨g, rfl⟩
    have hgD : (g : GL (Fin d) K) ∈ matrixDerived Q := g.2.1
    refine ⟨hInn ⟨matrixProjectiveProjection Q (⟨(g : GL (Fin d) K), hgD⟩ : matrixDerived Q),
      ?_⟩, ?_⟩
    · exact (kappa_derived_eq_conj (⟨(g : GL (Fin d) K), hgD⟩ : matrixDerived Q)).symm
    · have hc : Commute (Subgroup.inclusion hle g) (symmetryIsometry Q v) :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2.2.2)
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((hc.map (matrixIsometryInclusion Q)).map (matrixProjectiveConjugationHom Q)).eq
  set N := ψ.range.subgroupOf Y with hN
  have hNnormal : N.Normal := by
    constructor
    intro x hx y
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨g, hg⟩ := hx
    obtain ⟨S, hS, hSy⟩ := exists_unit_rep (hHE y.2.1)
    have hα : Commute (matrixProjectiveConjugationHom Q S) (symmetryAut Q v) := by
      rw [hSy]
      exact Subgroup.mem_centralizer_singleton_iff.mp y.2.2
    have hSv := conj_inclusion_eq_of_commute hQ hT hE hd hS hα
    refine ⟨⟨_, conjIsometry_mem hSv (g := Subgroup.inclusion hle g) g.2⟩, ?_⟩
    change matrixProjectiveConjugationHom Q
        (matrixIsometryInclusion Q (conjIsometry S (Subgroup.inclusion hle g))) =
      (y : MulAut (matrixProjectiveDerived Q)) * x * (y : MulAut (matrixProjectiveDerived Q))⁻¹
    rw [← conj_kappa_inclusion, hSy, ← hg]
    rfl
  have hNodd : CFSG.oddCore N = ⊥ :=
    EvenCatalog.oddCore_eq_bot_of_mulEquiv
      ((MonoidHom.ofInjective hψinj).trans (Subgroup.subgroupOfEquivOfLe hNY).symm)
      (oddCore_derivedSymmetryCentralizer hf hK hdn hn hQ hE hv)
  have hcent : ∀ y ∈ Subgroup.centralizer (N : Set Y), y ^ 2 = 1 := by
    intro y hy
    obtain ⟨S, hS, hSy⟩ := exists_unit_rep (hHE y.2.1)
    have hα : Commute (matrixProjectiveConjugationHom Q S) (symmetryAut Q v) := by
      rw [hSy]
      exact Subgroup.mem_centralizer_singleton_iff.mp y.2.2
    have hNc : ∀ g : matrixIsometries Q, (g : GL (Fin d) K) ∈ derivedSymmetryCentralizer Q v →
        Commute (matrixProjectiveConjugationHom Q S)
          (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g)) := by
      intro g hg
      have hmemN : (⟨ψ ⟨g, hg⟩, hNY ⟨⟨g, hg⟩, rfl⟩⟩ : Y) ∈ (N : Set Y) :=
        Subgroup.mem_subgroupOf.mpr ⟨⟨g, hg⟩, rfl⟩
      have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy _ hmemN)
      change matrixProjectiveConjugationHom Q S *
          matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g) =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g) *
          matrixProjectiveConjugationHom Q S
      rw [hSy]
      exact h1.symm
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hSy]
    rcases eq_one_or_eq_of_commute hQ hT hE hd3 hv hS hα hNc with h | h
    · rw [h, map_one, one_pow]
    · rw [h]
      exact symmetryAut_sq Q v
  exact oddCore_eq_bot_of_normal_of_centralizer hNnormal hNodd hcent

end CFSG.ComponentClassification.UnbalancedCatalog
