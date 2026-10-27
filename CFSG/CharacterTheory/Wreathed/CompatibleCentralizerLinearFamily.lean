module

public import CFSG.CharacterTheory.Wreathed.NormalCentralizerBlockOrbits
public import CFSG.CharacterTheory.Wreathed.DefectNormalizerBrauerCorrespondence
public import CFSG.CharacterTheory.Wreathed.LinearCharacterBlockDefect
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalBrauerDefectGrowth
public import CFSG.CharacterTheory.TwoRankLowerBound.CommutingSubgroupProduct
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Core

public section

open scoped BigOperators Classical Pointwise

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers BlockOrbits

variable {G : Type*} [Group G]

@[expose] def CompatibleCentralizerFamily (p : ℕ) (P : Subgroup G)
    (θ : Subgroup.centralizer (P : Set G) → ℂ)
    (ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ) : Prop :=
  (∀ Q : Subgroup G, IsPGroup p Q → Q ≠ ⊥ →
    ∀ z : Subgroup.centralizer (Q : Set G), (z : G) ∈ Q → ψ Q z = 1) ∧
  (∀ Q : Subgroup G, IsPGroup p Q → Q ≠ ⊥ → ∀ (h : G) (g : Subgroup.centralizer (Q : Set G))
    (g' : Subgroup.centralizer ((Q.map (MulAut.conj h⁻¹).toMonoidHom : Subgroup G) : Set G)),
    (g' : G) = h⁻¹ * g * h → ψ (Q.map (MulAut.conj h⁻¹).toMonoidHom) g' = ψ Q g) ∧
  (∀ Q Q₁ : Subgroup G, IsPGroup p Q → Q ≠ ⊥ → IsPGroup p Q₁ → Q ≤ Q₁ →
    ∀ (g : Subgroup.centralizer (Q₁ : Set G)) (g' : Subgroup.centralizer (Q : Set G)),
      (g' : G) = g → ψ Q g' = ψ Q₁ g) ∧
  (∀ g : Subgroup.centralizer (P : Set G), (ψ P g : ℂ) = θ g)

namespace CompatibleFamily

theorem family_congr (ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ)
    {Q₁ Q₂ : Subgroup G} (h : Q₁ = Q₂) (g₁ : Subgroup.centralizer (Q₁ : Set G))
    (g₂ : Subgroup.centralizer (Q₂ : Set G)) (hg : (g₁ : G) = g₂) : ψ Q₁ g₁ = ψ Q₂ g₂ := by
  subst h
  rw [Subtype.ext hg]

theorem family_conj_invariant {p : ℕ} {P : Subgroup G}
    {θ : Subgroup.centralizer (P : Set G) → ℂ}
    {ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ}
    (hψ : CompatibleCentralizerFamily p P θ ψ) {Q : Subgroup G} (hQp : IsPGroup p Q)
    (hQ1 : Q ≠ ⊥) {h : G} (hh : h ∈ Subgroup.normalizer (Q : Set G))
    (c c' : Subgroup.centralizer (Q : Set G)) (hc' : (c' : G) = h * c * h⁻¹) :
    ψ Q c' = ψ Q c := by
  have hmap : Q.map (MulAut.conj h⁻¹⁻¹).toMonoidHom = Q := by
    rw [inv_inv]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hh
  have hmem : (c' : G) ∈
      Subgroup.centralizer ((Q.map (MulAut.conj h⁻¹⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    rw [hmap]
    exact c'.property
  have hvalue := hψ.2.1 Q hQp hQ1 h⁻¹ c ⟨c', hmem⟩ (by
    change (c' : G) = h⁻¹⁻¹ * c * h⁻¹
    rw [inv_inv]
    exact hc')
  rw [← hvalue]
  exact family_congr ψ hmap.symm c' ⟨c', hmem⟩ rfl

section Product

variable (Q : Subgroup G) (μ : Subgroup.centralizer (Q : Set G) →* ℂˣ)

theorem product_value_unique (hμ : ∀ z : Subgroup.centralizer (Q : Set G), (z : G) ∈ Q → μ z = 1)
    {q q' : G} (hq : q ∈ Q) (hq' : q' ∈ Q) (c c' : Subgroup.centralizer (Q : Set G))
    (h : q * (c : G) = q' * c') : μ c = μ c' := by
  have hz : (c' : G) * (c : G)⁻¹ = q'⁻¹ * q := by
    calc (c' : G) * (c : G)⁻¹ = q'⁻¹ * (q' * c') * (c : G)⁻¹ := by group
      _ = q'⁻¹ * (q * c) * (c : G)⁻¹ := by rw [h]
      _ = q'⁻¹ * q := by group
  have hzQ : ((c' * c⁻¹ : Subgroup.centralizer (Q : Set G)) : G) ∈ Q := by
    change (c' : G) * (c : G)⁻¹ ∈ Q
    rw [hz]
    exact Q.mul_mem (Q.inv_mem hq') hq
  have h1 := hμ (c' * c⁻¹) hzQ
  have hc' : c' = (c' * c⁻¹) * c := by group
  rw [hc', map_mul, h1, one_mul]

variable {Q} in
theorem product_decomposition_exists {K : Subgroup G}
    (hK : ∀ x ∈ K, ∃ q ∈ Q, ∃ c ∈ Subgroup.centralizer (Q : Set G), x = q * c) (x : K) :
    ∃ c : Subgroup.centralizer (Q : Set G), ∃ q ∈ Q, (x : G) = q * c := by
  obtain ⟨q, hq, c, hc, hx⟩ := hK x x.property
  exact ⟨⟨c, hc⟩, q, hq, hx⟩

noncomputable def productLinearCharacter
    (hμ : ∀ z : Subgroup.centralizer (Q : Set G), (z : G) ∈ Q → μ z = 1) (K : Subgroup G)
    (hK : ∀ x ∈ K, ∃ q ∈ Q, ∃ c ∈ Subgroup.centralizer (Q : Set G), x = q * c) : K →* ℂˣ where
  toFun x := μ (Classical.choose (product_decomposition_exists hK x))
  map_one' := by
    obtain ⟨q, hq, hx⟩ := Classical.choose_spec (product_decomposition_exists hK 1)
    have h := product_value_unique Q μ hμ hq Q.one_mem
      (Classical.choose (product_decomposition_exists hK 1)) 1 (by
        rw [← hx]
        simp)
    rw [h, map_one]
  map_mul' x y := by
    obtain ⟨q, hq, hx⟩ := Classical.choose_spec (product_decomposition_exists hK x)
    obtain ⟨q', hq', hy⟩ := Classical.choose_spec (product_decomposition_exists hK y)
    obtain ⟨q'', hq'', hxy⟩ := Classical.choose_spec (product_decomposition_exists hK (x * y))
    set c := Classical.choose (product_decomposition_exists hK x)
    set c' := Classical.choose (product_decomposition_exists hK y)
    set c'' := Classical.choose (product_decomposition_exists hK (x * y))
    rw [← map_mul]
    apply product_value_unique Q μ hμ hq'' (Q.mul_mem hq hq')
    have hcomm : (c : G) * q' = q' * c := (Subgroup.mem_centralizer_iff.mp c.property q' hq').symm
    rw [← hxy]
    change (x : G) * y = q * q' * ((c : G) * c')
    rw [hx, hy]
    calc q * (c : G) * (q' * c') = q * ((c : G) * q') * c' := by group
      _ = q * (q' * c) * c' := by rw [hcomm]
      _ = q * q' * ((c : G) * c') := by group

theorem productLinearCharacter_apply
    (hμ : ∀ z : Subgroup.centralizer (Q : Set G), (z : G) ∈ Q → μ z = 1) (K : Subgroup G)
    (hK : ∀ x ∈ K, ∃ q ∈ Q, ∃ c ∈ Subgroup.centralizer (Q : Set G), x = q * c) (x : K)
    {q : G} (hq : q ∈ Q) (c : Subgroup.centralizer (Q : Set G)) (hx : (x : G) = q * c) :
    productLinearCharacter Q μ hμ K hK x = μ c := by
  obtain ⟨q₀, hq₀, hx₀⟩ := Classical.choose_spec (product_decomposition_exists hK x)
  exact product_value_unique Q μ hμ hq₀ hq _ c (hx₀.symm.trans hx)

end Product

section Linear

theorem linear_value_mem {C : Type*} [Group C] [Finite C] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsPrime] (μ : C →* ℂˣ) (c : C) : (μ c : ℂ) ∈ localizedComplexIntegerRing ideal :=
  rootOfUnity_mem_localizedComplexIntegerRing ideal (orderOf c) (orderOf_pos c) _ (by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one])

@[expose] noncomputable def linearWeightedResidue {K C : Type*} [Group K] [Group C] [Fintype C]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (ι : C → K) (μ : C →* ℂˣ)
    (w : centralCoefficientSubring (G := K) (localizedComplexIntegerRing ideal)) :
    ComplexAlgebraicIntegers ⧸ ideal :=
  ∑ c : C, localizedComplexIntegerResidue ideal
      ⟨w.val.coeff (ι c), centralCoefficientSubring_coefficients _ w (ι c)⟩ *
    localizedComplexIntegerResidue ideal ⟨μ c, linear_value_mem ideal μ c⟩

theorem localCentralCharacterHom_linear {K : Type*} [Group K] [Fintype K]
    (basis : FiniteIrreducibleCharacterBasis K) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (μ : K →* ℂˣ) (ℓ : basis.index)
    (hℓ : ∀ k, (basis.representation ℓ).character k = μ k)
    (w : centralCoefficientSubring (G := K) (localizedComplexIntegerRing ideal)) :
    (localCentralCharacterHom basis ideal ℓ w : ℂ) = ∑ k : K, w.val.coeff k * (μ k : ℂ) := by
  rw [localCentralCharacterHom_coe]
  unfold centralCharacterScalar characterPairing
  have hdegree : (basis.representation ℓ).character 1 = 1 := by
    rw [hℓ, map_one, Units.val_one]
  have hcard : (Nat.card K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [hdegree, div_one, mul_inv_cancel_left₀ hcard]
  rw [← Equiv.sum_comp (Equiv.inv K)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Equiv.inv_apply, inv_inv, hℓ]

theorem centralCharacterResidueHom_linear {K : Type*} [Group K] [Fintype K]
    (basis : FiniteIrreducibleCharacterBasis K) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (μ : K →* ℂˣ) (ℓ : basis.index)
    (hℓ : ∀ k, (basis.representation ℓ).character k = μ k)
    (w : centralCoefficientSubring (G := K) (localizedComplexIntegerRing ideal)) :
    centralCharacterResidueHom basis ideal ℓ w = linearWeightedResidue ideal id μ w := by
  have hlocal : localCentralCharacterHom basis ideal ℓ w =
      ∑ k : K, (⟨w.val.coeff k, centralCoefficientSubring_coefficients _ w k⟩ :
        localizedComplexIntegerRing ideal) * ⟨μ k, linear_value_mem ideal μ k⟩ := by
    apply Subtype.ext
    rw [localCentralCharacterHom_linear basis ideal μ ℓ hℓ w]
    push_cast
    rfl
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal ℓ w) = _
  rw [hlocal, map_sum]
  unfold linearWeightedResidue
  simp only [map_mul, id]

theorem exists_linear_label {K : Type*} [Group K] [Fintype K]
    (basis : FiniteIrreducibleCharacterBasis K) (μ : K →* ℂˣ) :
    ∃ ℓ : basis.index, ∀ k, (basis.representation ℓ).character k = μ k := by
  let data : FiniteComplexRepresentation K :=
    { vector := (principalFiniteComplexRepresentation K).vector
      representation := CFSG.Section1.representationTwistByCharacter μ
        (principalFiniteComplexRepresentation K).representation }
  have hirreducible : data.IsIrreducible :=
    CFSG.Section1.irreducible_twistByCharacter μ _
      (principalFiniteComplexRepresentation_isIrreducible K)
  obtain ⟨ℓ, hℓ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis data hirreducible
  refine ⟨ℓ, fun k => ?_⟩
  rw [hℓ]
  change (CFSG.Section1.representationTwistByCharacter μ
    (principalFiniteComplexRepresentation K).representation).character k = _
  rw [CFSG.Section1.representationTwistByCharacter_character, Pi.mul_apply]
  have h1 := congrFun (principalFiniteComplexRepresentation_character K) k
  change (principalFiniteComplexRepresentation K).representation.character k = 1 at h1
  rw [h1, mul_one]

end Linear

section Weighted

variable [Fintype G]

@[expose] def WeightedLocalBlock (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (Q H : Subgroup G) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (μ : Subgroup.centralizer (Q : Set G) →* ℂˣ) (basis : FiniteIrreducibleCharacterBasis H)
    (β : basis.index) : Prop :=
  ∀ w : centralCoefficientSubring (G := H) (localizedComplexIntegerRing ideal),
    centralCharacterResidueHom basis ideal β w =
      linearWeightedResidue ideal (Subgroup.inclusion hCH) μ w

theorem linearWeightedResidue_inclusion (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (Q H : Subgroup G) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (μ : Subgroup.centralizer (Q : Set G) →* ℂˣ)
    (a : externalCommonCentralCoefficientSubring (localizedComplexIntegerRing ideal) Q H hCH) :
    linearWeightedResidue ideal (Subgroup.inclusion hCH) μ
        (externalCommonCentralCoefficientInclusion _ Q H hCH a) =
      linearWeightedResidue ideal id μ a.val := by
  unfold linearWeightedResidue
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  apply Subtype.ext
  exact embedded_coeff (Subgroup.inclusion hCH) (Subgroup.inclusion_injective hCH) a.val.val c

theorem weightedLocalBlock_iff_match (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (Q H : Subgroup G)
    (hQ : IsPGroup p Q) (hQH : Q ≤ H) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Q : Set G)) (μ : Subgroup.centralizer (Q : Set G) →* ℂˣ)
    (basis : FiniteIrreducibleCharacterBasis H)
    (centralizerBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Q : Set G)))
    (ℓ : centralizerBasis.index) (hℓ : ∀ c, (centralizerBasis.representation ℓ).character c = μ c)
    (β : basis.index) :
    WeightedLocalBlock ideal Q H hCH μ basis β ↔
      ExternalResidueMatch Q H hCH basis ideal centralizerBasis β ℓ := by
  constructor
  · intro hβ a
    rw [centralCharacterResidueHom_linear centralizerBasis ideal μ ℓ hℓ, hβ,
      linearWeightedResidue_inclusion]
  · intro hmatch w
    rw [externalCentralRestriction_residue ideal p Q H hQ hQH hCH hHN basis w β, ← hmatch,
      centralCharacterResidueHom_linear centralizerBasis ideal μ ℓ hℓ]
    rfl

theorem weightedLocalBlock_same (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (Q H : Subgroup G) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (μ : Subgroup.centralizer (Q : Set G) →* ℂˣ) (basis : FiniteIrreducibleCharacterBasis H)
    {β β' : basis.index} (hβ : WeightedLocalBlock ideal Q H hCH μ basis β)
    (hβ' : WeightedLocalBlock ideal Q H hCH μ basis β') :
    sameCoefficientBlock basis (localizedComplexIntegerRing ideal) β β' := by
  rw [sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
  apply RingHom.ext
  intro w
  rw [hβ w, hβ' w]

theorem brauer_weightedLocalBlock (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (Q H : Subgroup G)
    (hQ : IsPGroup p Q) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Q : Set G)) (μ : Subgroup.centralizer (Q : Set G) →* ℂˣ)
    (basis : FiniteIrreducibleCharacterBasis H) {β : basis.index}
    (hβ : WeightedLocalBlock ideal Q H hCH μ basis β)
    (z : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal)) :
    brauerNormalizerCharacterResidueHom ideal p Q hQ H hCH hHN basis β z =
      linearWeightedResidue ideal (Subgroup.centralizer (Q : Set G)).subtype μ z := by
  change centralCharacterResidueHom basis ideal β
    (centralNormalizerCoefficientProjection _ Q H hCH hHN z) = _
  rw [hβ]
  unfold linearWeightedResidue
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  apply Subtype.ext
  change (centralNormalizerCoefficientProjection _ Q H hCH hHN z).val.coeff
    (Subgroup.inclusion hCH c) = z.val.coeff c
  rw [centralNormalizerCoefficientProjection_coeff]
  exact ite_eq_left (show ((Subgroup.inclusion hCH c : H) : G) ∈
    Subgroup.centralizer (Q : Set G) from c.property)

theorem weightedLocalBlock_of_linear (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (Q H : Subgroup G)
    (hQ : IsPGroup p Q) (hQH : Q ≤ H) (hCH : Subgroup.centralizer (Q : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Q : Set G)) (μ : Subgroup.centralizer (Q : Set G) →* ℂˣ)
    (basis : FiniteIrreducibleCharacterBasis H) (ν : H →* ℂˣ) (ℓ : basis.index)
    (hℓ : ∀ x, (basis.representation ℓ).character x = ν x)
    (hν : ∀ c, ν (Subgroup.inclusion hCH c) = μ c) :
    WeightedLocalBlock ideal Q H hCH μ basis ℓ := by
  intro w
  rw [externalCentralRestriction_residue ideal p Q H hQ hQH hCH hHN basis w ℓ,
    centralCharacterResidueHom_linear basis ideal ν ℓ hℓ]
  unfold linearWeightedResidue
  symm
  apply Fintype.sum_of_injective (Subgroup.inclusion hCH) (Subgroup.inclusion_injective hCH)
  · intro x hx
    have hzero : (externalCommonCentralCoefficientInclusion _ Q H hCH
        (externalCentralRestriction ideal Q H hCH hHN w)).val.coeff x = 0 :=
      embedded_coeff_zero (Subgroup.inclusion hCH) _ x hx
    have hres : localizedComplexIntegerResidue ideal
        ⟨(externalCommonCentralCoefficientInclusion _ Q H hCH
          (externalCentralRestriction ideal Q H hCH hHN w)).val.coeff (id x),
          centralCoefficientSubring_coefficients _ _ _⟩ = 0 := by
      have hsub : (⟨(externalCommonCentralCoefficientInclusion _ Q H hCH
          (externalCentralRestriction ideal Q H hCH hHN w)).val.coeff (id x),
          centralCoefficientSubring_coefficients _ _ _⟩ : localizedComplexIntegerRing ideal) = 0 :=
        Subtype.ext hzero
      rw [hsub, map_zero]
    rw [hres, zero_mul]
  · intro c
    congr 2
    · apply Subtype.ext
      exact ((embedded_coeff (Subgroup.inclusion hCH) (Subgroup.inclusion_injective hCH) _ c).trans
        (externalCentralRestriction_coeff ideal Q H hCH hHN w c)).symm
    · apply Subtype.ext
      exact congrArg Units.val (hν c).symm

end Weighted

section Conjugate

theorem conj_mem_centralizer_map (S : Subgroup G) (g : G) {c : G}
    (hc : c ∈ Subgroup.centralizer (S : Set G)) :
    g * c * g⁻¹ ∈
      Subgroup.centralizer ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro y ⟨s, hs, rfl⟩
  have hcs := Subgroup.mem_centralizer_iff.mp hc s hs
  change g * s * g⁻¹ * (g * c * g⁻¹) = g * c * g⁻¹ * (g * s * g⁻¹)
  calc g * s * g⁻¹ * (g * c * g⁻¹) = g * (s * c) * g⁻¹ := by group
    _ = g * (c * s) * g⁻¹ := by rw [hcs]
    _ = g * c * g⁻¹ * (g * s * g⁻¹) := by group

theorem normalizer_decomposition_conj (S : Subgroup G)
    (hNS : ∀ x ∈ Subgroup.normalizer (S : Set G),
      ∃ q ∈ S, ∃ c ∈ Subgroup.centralizer (S : Set G), x = q * c) (g : G) :
    ∀ x ∈ Subgroup.normalizer ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G),
      ∃ q ∈ S.map (MulAut.conj g).toMonoidHom,
        ∃ c ∈ Subgroup.centralizer ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G),
          x = q * c := by
  intro x hx
  have hx' : g⁻¹ * x * g ∈ Subgroup.normalizer (S : Set G) := by
    have hmap : (S.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        S.map (MulAut.conj g).toMonoidHom := Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
    have hback := congrArg (fun K : Subgroup G => K.map (MulAut.conj g⁻¹).toMonoidHom) hmap
    simp only [conjugation_subgroup_map_mul, inv_mul_cancel, conjugation_subgroup_map_one] at hback
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change S.map (MulAut.conj (g⁻¹ * x * g)).toMonoidHom = S
    rw [show g⁻¹ * x * g = g⁻¹ * (x * g) by group]
    exact hback
  obtain ⟨s, hs, c, hc, hdecomposition⟩ := hNS _ hx'
  refine ⟨g * s * g⁻¹, ⟨s, hs, rfl⟩, g * c * g⁻¹, conj_mem_centralizer_map S g hc, ?_⟩
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = g * (s * c) * g⁻¹ := by rw [hdecomposition]
    _ = g * s * g⁻¹ * (g * c * g⁻¹) := by group

variable [Fintype G]

theorem linearWeightedResidue_conj {p : ℕ} {P : Subgroup G}
    {θ : Subgroup.centralizer (P : Set G) → ℂ}
    {ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ}
    (hψ : CompatibleCentralizerFamily p P θ ψ) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (S : Subgroup G) (hSp : IsPGroup p S) (hS1 : S ≠ ⊥) (g : G)
    (z : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal)) :
    linearWeightedResidue ideal
        (Subgroup.centralizer ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)).subtype
        (ψ (S.map (MulAut.conj g).toMonoidHom)) z =
      linearWeightedResidue ideal (Subgroup.centralizer (S : Set G)).subtype (ψ S) z := by
  set Q := S.map (MulAut.conj g).toMonoidHom with hQ
  have hmap : S.map (MulAut.conj g⁻¹⁻¹).toMonoidHom = Q := by rw [inv_inv]
  let e : Subgroup.centralizer (S : Set G) → Subgroup.centralizer (Q : Set G) := fun c =>
    ⟨g * c * g⁻¹, conj_mem_centralizer_map S g c.property⟩
  have he : Function.Bijective e := by
    constructor
    · intro c c' hcc'
      apply Subtype.ext
      have h := congrArg Subtype.val hcc'
      change g * (c : G) * g⁻¹ = g * c' * g⁻¹ at h
      simpa using h
    · intro c'
      have hmem : g⁻¹ * c' * g⁻¹⁻¹ ∈ Subgroup.centralizer
          ((Q.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) :=
        conj_mem_centralizer_map Q g⁻¹ c'.property
      have hback : Q.map (MulAut.conj g⁻¹).toMonoidHom = S := by
        rw [hQ, conjugation_subgroup_map_mul, inv_mul_cancel, conjugation_subgroup_map_one]
      rw [hback] at hmem
      refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
      change g * (g⁻¹ * c' * g⁻¹⁻¹) * g⁻¹ = c'
      group
  unfold linearWeightedResidue
  refine (Fintype.sum_bijective e he _ _ fun c => ?_).symm
  have hz : z.val.coeff (g * c * g⁻¹) = z.val.coeff c :=
    central_groupAlgebra_coeff_conjugation z.val (centralCoefficientSubring_commutes _ z) c g
  have hmem : g * (c : G) * g⁻¹ ∈ Subgroup.centralizer
      ((S.map (MulAut.conj g⁻¹⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    rw [hmap]
    exact (e c).property
  have hvalue := hψ.2.1 S hSp hS1 g⁻¹ c ⟨_, hmem⟩ (by
    change g * (c : G) * g⁻¹ = g⁻¹⁻¹ * c * g⁻¹
    rw [inv_inv])
  have hψc : ψ Q (e c) = ψ S c := by
    rw [← hvalue]
    exact family_congr ψ hmap.symm (e c) ⟨_, hmem⟩ rfl
  congr 2
  · exact Subtype.ext hz.symm
  · exact Subtype.ext (congrArg Units.val hψc.symm)

theorem linearWeightedResidue_orbit {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    {θ : Subgroup.centralizer (P : Set G) → ℂ}
    {ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ}
    (hψ : CompatibleCentralizerFamily p P θ ψ) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (Q D N : Subgroup G)
    (hQp : IsPGroup p Q) (hQ1 : Q ≠ ⊥) (hDp : IsPGroup p D) (hQD : Q ≤ D)
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) (hDN : D ≤ N)
    (hCN : Subgroup.centralizer (Q : Set G) ≤ N)
    (w : centralCoefficientSubring (G := N) (localizedComplexIntegerRing ideal)) :
    linearWeightedResidue ideal (Subgroup.inclusion hCN) (ψ Q) w =
      linearWeightedResidue ideal
        (Subgroup.inclusion ((Subgroup.centralizer_le hQD).trans hCN)) (ψ D) w := by
  let : MulAction D (Subgroup.centralizer (Q : Set G)) :=
    { smul := fun d c => centralizerConjugation Q d (hDQ d.property) c
      one_smul := fun c => Subtype.ext (by
        change (1 : G) * c * (1 : G)⁻¹ = c
        group)
      mul_smul := fun d d' c => Subtype.ext (by
        change ((d * d' : D) : G) * c * ((d * d' : D) : G)⁻¹ =
          (d : G) * ((d' : G) * c * (d' : G)⁻¹) * (d : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hsmul : ∀ (d : D) (c : Subgroup.centralizer (Q : Set G)),
      ((d • c : Subgroup.centralizer (Q : Set G)) : G) = d * c * (d : G)⁻¹ := fun _ _ => rfl
  let weight : Subgroup.centralizer (Q : Set G) → ComplexAlgebraicIntegers ⧸ ideal := fun c =>
    localizedComplexIntegerResidue ideal
        ⟨w.val.coeff (Subgroup.inclusion hCN c), centralCoefficientSubring_coefficients _ w _⟩ *
      localizedComplexIntegerResidue ideal ⟨ψ Q c, linear_value_mem ideal (ψ Q) c⟩
  have hinvariant :
      ∀ (d : D) (c : Subgroup.centralizer (Q : Set G)), weight (d • c) = weight c := by
    intro d c
    have hcoeff : w.val.coeff (Subgroup.inclusion hCN (d • c)) =
        w.val.coeff (Subgroup.inclusion hCN c) := by
      have hequal : Subgroup.inclusion hCN (d • c) =
          (⟨d, hDN d.property⟩ : N) * Subgroup.inclusion hCN c * (⟨d, hDN d.property⟩ : N)⁻¹ :=
        Subtype.ext rfl
      rw [hequal]
      exact central_groupAlgebra_coeff_conjugation w.val
        (centralCoefficientSubring_commutes _ w) _ _
    have hψd : ψ Q (d • c) = ψ Q c :=
      family_conj_invariant hψ hQp hQ1 (hDQ d.property) c (d • c) (hsmul d c)
    change localizedComplexIntegerResidue ideal ⟨_, _⟩ *
        localizedComplexIntegerResidue ideal ⟨_, _⟩ =
      localizedComplexIntegerResidue ideal ⟨_, _⟩ * localizedComplexIntegerResidue ideal ⟨_, _⟩
    congr 2
    · exact Subtype.ext hcoeff
    · exact Subtype.ext (congrArg Units.val hψd)
  have hfixed : ∀ c : Subgroup.centralizer (Q : Set G),
      c ∈ MulAction.fixedPoints D (Subgroup.centralizer (Q : Set G)) ↔
        (c : G) ∈ Subgroup.centralizer (D : Set G) := by
    intro c
    rw [MulAction.mem_fixedPoints, Subgroup.mem_centralizer_iff]
    constructor
    · intro hfix d hd
      have h := congrArg Subtype.val (hfix ⟨d, hd⟩)
      rw [hsmul] at h
      calc d * (c : G) = d * c * d⁻¹ * d := by group
        _ = c * d := by rw [h]
    · intro hcomm d
      apply Subtype.ext
      rw [hsmul, hcomm d d.property]
      group
  have hsum := p_group_invariant_sum_fixedPoints p hDp weight hinvariant
  unfold linearWeightedResidue
  change ∑ c, weight c = _
  rw [hsum]
  have hle : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.centralizer_le hQD
  symm
  apply Fintype.sum_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  · intro c hc
    rw [ite_eq_right]
    intro hmem
    exact hc ⟨⟨c, (hfixed c).mp hmem⟩, rfl⟩
  · intro c
    rw [ite_eq_left ((hfixed _).mpr c.property)]
    have hψc : ψ Q (Subgroup.inclusion hle c) = ψ D c :=
      hψ.2.2.1 Q D hQp hQ1 hDp hQD c (Subgroup.inclusion hle c) rfl
    change localizedComplexIntegerResidue ideal ⟨_, _⟩ *
        localizedComplexIntegerResidue ideal ⟨_, _⟩ =
      localizedComplexIntegerResidue ideal ⟨_, _⟩ * localizedComplexIntegerResidue ideal ⟨_, _⟩
    congr 2
    exact Subtype.ext (congrArg Units.val hψc.symm)

theorem pSubgroup_subconjugate_sylow {p : ℕ} [Fact p.Prime] (S : Sylow p G) {Q : Subgroup G}
    (hQ : IsPGroup p Q) : subgroupSubconjugate Q (S : Subgroup G) := by
  obtain ⟨P', hP'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P' S
  refine ⟨g, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  have hmem : (MulAut.conj g) q ∈ ((g • P' : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul q (MulAut.conj g) _ (hP' hq)
  rw [hg] at hmem
  exact hmem

omit [Fintype G] in
theorem join_centralizer_decomposition (Q : Subgroup G) :
    ∀ x ∈ Q ⊔ Subgroup.centralizer (Q : Set G),
      ∃ q ∈ Q, ∃ c ∈ Subgroup.centralizer (Q : Set G), x = q * c := by
  have hcommute : ∀ (first : Q) (second : Subgroup.centralizer (Q : Set G)),
      Commute (first : G) (second : G) := fun first second =>
    (Subgroup.mem_centralizer_iff.mp second.property first first.property)
  have hle : Q ⊔ Subgroup.centralizer (Q : Set G) ≤
      (commutingSubgroupProduct Q (Subgroup.centralizer (Q : Set G)) hcommute).range := by
    apply sup_le
    · intro q hq
      exact ⟨(⟨q, hq⟩, 1), mul_one q⟩
    · intro c hc
      exact ⟨(1, ⟨c, hc⟩), one_mul c⟩
  intro x hx
  obtain ⟨⟨q, c⟩, hqc⟩ := hle hx
  exact ⟨q, q.property, c, c.property, hqc.symm⟩

end Conjugate

section Main

variable [Fintype G]

theorem family_local_blocks_weighted (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (S : Sylow p G) (hS1 : (S : Subgroup G) ≠ ⊥)
    (hNS : ∀ x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
      ∃ q ∈ (S : Subgroup G), ∃ c ∈ Subgroup.centralizer ((S : Subgroup G) : Set G), x = q * c)
    {θ : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ}
    {ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ}
    (hψ : CompatibleCentralizerFamily p (S : Subgroup G) θ ψ) (B : basis.index)
    (hBres : ∀ z, centralCharacterResidueHom basis ideal B z =
      linearWeightedResidue ideal (Subgroup.centralizer ((S : Subgroup G) : Set G)).subtype
        (ψ S) z)
    (hBdef : coefficientBlockDefect basis ideal p B S) :
    ∀ (Q : Subgroup G) (hQp : IsPGroup p Q), Q ≠ ⊥ → ∀ (H : Subgroup G) (_hQH : Q ≤ H)
      (hCH : Subgroup.centralizer (Q : Set G) ≤ H) (hHN : H ≤ Subgroup.normalizer (Q : Set G))
      (localBasis : FiniteIrreducibleCharacterBasis H) (β : localBasis.index),
      brauerNormalizerCharacterResidueHom ideal p Q hQp H hCH hHN localBasis β =
        centralCharacterResidueHom basis ideal B →
      WeightedLocalBlock ideal Q H hCH (ψ Q) localBasis β := by
  by_contra hcontra
  push Not at hcontra
  let counterexample : Subgroup G → Prop := fun Q =>
    ∃ (hQp : IsPGroup p Q), Q ≠ ⊥ ∧ ∃ (H : Subgroup G) (_hQH : Q ≤ H)
      (hCH : Subgroup.centralizer (Q : Set G) ≤ H) (hHN : H ≤ Subgroup.normalizer (Q : Set G))
      (localBasis : FiniteIrreducibleCharacterBasis H) (β : localBasis.index),
      brauerNormalizerCharacterResidueHom ideal p Q hQp H hCH hHN localBasis β =
        centralCharacterResidueHom basis ideal B ∧
      ¬ WeightedLocalBlock ideal Q H hCH (ψ Q) localBasis β
  obtain ⟨Q₀, hQ₀p, hQ₀1, H₀, hQH₀, hCH₀, hHN₀, basis₀, β₀, hβ₀, hnot₀⟩ := hcontra
  let : Nonempty {Q : Subgroup G // counterexample Q} :=
    ⟨⟨Q₀, hQ₀p, hQ₀1, H₀, hQH₀, hCH₀, hHN₀, basis₀, β₀, hβ₀, hnot₀⟩⟩
  obtain ⟨⟨Q, hQ⟩, hmax⟩ := Finite.exists_max
    (fun Q : {Q : Subgroup G // counterexample Q} => Nat.card Q.val)
  obtain ⟨hQp, hQ1, H, hQH, hCH, hHN, localBasis, β, hβB, hβ⟩ := hQ
  have hlarger : ∀ (D : Subgroup G) (hDp : IsPGroup p D), D ≠ ⊥ → Nat.card Q < Nat.card D →
      ∀ (J : Subgroup G) (_hDJ : D ≤ J) (hCJ : Subgroup.centralizer (D : Set G) ≤ J)
        (hJN : J ≤ Subgroup.normalizer (D : Set G)) (jBasis : FiniteIrreducibleCharacterBasis J)
        (γ : jBasis.index),
        brauerNormalizerCharacterResidueHom ideal p D hDp J hCJ hJN jBasis γ =
          centralCharacterResidueHom basis ideal B →
        WeightedLocalBlock ideal D J hCJ (ψ D) jBasis γ := by
    intro D hDp hD1 hlt J hDJ hCJ hJN jBasis γ hγ
    by_contra hnot
    exact (Nat.not_lt_of_ge (hmax ⟨D, hDp, hD1, J, hDJ, hCJ, hJN, jBasis, γ, hγ, hnot⟩)) hlt
  obtain ⟨centralizerBasis⟩ :=
    finiteIrreducibleCharacterBasis_exists (G := Subgroup.centralizer (Q : Set G))
  obtain ⟨ψLabel, hψLabel⟩ := exists_linear_label centralizerBasis (ψ Q)
  have hinvariant : ∀ (h : G) (hh : h ∈ Subgroup.normalizer (Q : Set G)),
      LabelTransport centralizerBasis centralizerBasis (centralizerConjugation Q h hh) ψLabel
        ψLabel := by
    intro h hh x
    rw [hψLabel, hψLabel, family_conj_invariant hψ hQp hQ1 hh x _ rfl]
  obtain ⟨θ', hθ'⟩ := externalCommonCentralizer_residue_restriction_exists ideal Q H hCH localBasis
    centralizerBasis β
  obtain ⟨normalizerBasis⟩ :=
    finiteIrreducibleCharacterBasis_exists (G := Subgroup.normalizer (Q : Set G))
  obtain ⟨βN, hβN⟩ := externalCommonCentralizer_residue_extension_exists ideal Q
    (Subgroup.normalizer (Q : Set G)) Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)
    normalizerBasis centralizerBasis θ'
  have hmatchH : ExternalResidueMatch Q H hCH localBasis ideal centralizerBasis β θ' := hθ'
  have hmatchN : ExternalResidueMatch Q (Subgroup.normalizer (Q : Set G))
      (Subgroup.centralizer_le_normalizer _) normalizerBasis ideal centralizerBasis βN θ' :=
    fun a => (hβN a).symm
  have hβNB : brauerNormalizerCharacterResidueHom ideal p Q hQp (Subgroup.normalizer (Q : Set G))
      (Subgroup.centralizer_le_normalizer _) le_rfl normalizerBasis βN =
        centralCharacterResidueHom basis ideal B := by
    apply RingHom.ext
    intro z
    rw [external_brauer_apply_of_match ideal p Q _ hQp _ le_rfl normalizerBasis centralizerBasis
      hmatchN z, ← external_brauer_apply_of_match ideal p Q H hQp hCH hHN localBasis
      centralizerBasis hmatchH z, hβB]
  have hβN' : ¬ WeightedLocalBlock ideal Q (Subgroup.normalizer (Q : Set G))
      (Subgroup.centralizer_le_normalizer _) (ψ Q) normalizerBasis βN := by
    intro hweighted
    apply hβ
    have hψN := (weightedLocalBlock_iff_match ideal p Q _ hQp Subgroup.le_normalizer _ le_rfl (ψ Q)
      normalizerBasis centralizerBasis ψLabel hψLabel βN).mp hweighted
    obtain ⟨-, -, horbit, -⟩ := external_block_orbits ideal p Q (Subgroup.normalizer (Q : Set G))
      hQp Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _) le_rfl normalizerBasis
      centralizerBasis
    obtain ⟨h, θ'', htransport, hsame⟩ := ((horbit βN).2 ψLabel hψN θ').mp hmatchN
    rw [labelTransport_unique htransport (hinvariant h (le_rfl (a := Subgroup.normalizer
      (Q : Set G)) h.property))] at hsame
    have hequal := (sameCoefficientBlock_iff_centralCharacterResidueHom_eq centralizerBasis ideal
      ψLabel θ').mp hsame
    apply (weightedLocalBlock_iff_match ideal p Q H hQp hQH hCH hHN (ψ Q) localBasis
      centralizerBasis
      ψLabel hψLabel β).mpr
    intro a
    rw [hequal]
    exact hmatchH a
  obtain ⟨DN, hDN⟩ := coefficientBlockDefect_exists normalizerBasis ideal p βN
  have : (Q.subgroupOf (Subgroup.normalizer (Q : Set G))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hQDN : Q.subgroupOf (Subgroup.normalizer (Q : Set G)) ≤ DN :=
    normal_p_le_coefficientBlockDefect normalizerBasis ideal p
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G))) hQp.comap_subtype hDN
  by_cases hEq : DN = Q.subgroupOf (Subgroup.normalizer (Q : Set G))
  ·
    rw [hEq] at hDN
    have hBQ : coefficientBlockDefect basis ideal p B Q :=
      defect_normalizer_brauer_image_defect basis ideal p Q hQp normalizerBasis hDN hβNB
    obtain ⟨g, hg⟩ := coefficientBlockDefect_conjugate basis ideal hBdef hBQ
    have hQcard : Nat.card Q = p ^ (Nat.card G).factorization p := by
      rw [← hg, conjugation_subgroup_card, Sylow.card_eq_multiplicity]
    subst hg
    have hdecomposition := normalizer_decomposition_conj (S : Subgroup G) hNS g
    have hSp : IsPGroup p (S : Subgroup G) := S.isPGroup'
    let ν := productLinearCharacter _ (ψ ((S : Subgroup G).map (MulAut.conj g).toMonoidHom))
      (hψ.1 _ hQp hQ1) _ hdecomposition
    obtain ⟨δ, hδ⟩ := exists_linear_label normalizerBasis ν
    have hδweighted := weightedLocalBlock_of_linear ideal p _ _ hQp Subgroup.le_normalizer
      (Subgroup.centralizer_le_normalizer _) le_rfl _ normalizerBasis ν δ hδ (fun c =>
        productLinearCharacter_apply _ _ _ _ hdecomposition _ (q := 1) (Subgroup.one_mem _) c
          (by rw [one_mul]; rfl))
    let QSylow : Sylow p G := Sylow.ofCard _ hQcard
    have hδdefect := (CFSG.Wreathed.linear_character_block_has_sylow_defect normalizerBasis ideal p
      ν δ hδ (QSylow.subtype Subgroup.le_normalizer)).1
    change coefficientBlockDefect normalizerBasis ideal p δ
      (((S : Subgroup G).map (MulAut.conj g).toMonoidHom).subgroupOf
        (Subgroup.normalizer (((S : Subgroup G).map (MulAut.conj g).toMonoidHom : Subgroup G) :
          Set G))) at hδdefect
    have hδB : brauerNormalizerCharacterResidueHom ideal p _ hQp _
        (Subgroup.centralizer_le_normalizer _) le_rfl normalizerBasis δ =
          centralCharacterResidueHom basis ideal B := by
      apply RingHom.ext
      intro z
      rw [brauer_weightedLocalBlock ideal p _ _ hQp _ le_rfl _ normalizerBasis hδweighted z,
        linearWeightedResidue_conj hψ ideal _ hSp hS1 g z, ← hBres z]
    have hsame := defect_normalizer_brauer_injective ideal p _ hQp normalizerBasis hDN hδdefect
      (hβNB.trans hδB.symm)
    apply hβN'
    intro w
    rw [(sameCoefficientBlock_iff_centralCharacterResidueHom_eq normalizerBasis ideal βN δ).mp
      hsame,
      hδweighted w]
  ·
    let N := Subgroup.normalizer (Q : Set G)
    let D := DN.map N.subtype
    have hDp : IsPGroup p D := (coefficientBlockDefect_isPGroup normalizerBasis ideal hDN).map _
    have hDN' : D ≤ N := Subgroup.map_subtype_le DN
    have hQD : Q ≤ D := by
      rw [← Subgroup.map_subgroupOf_eq_of_le (Subgroup.le_normalizer (H := Q))]
      exact Subgroup.map_mono hQDN
    have hlocalD : D.subgroupOf N = DN :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective N) DN
    have hstrict : Nat.card Q < Nat.card D := by
      have hnotle : ¬Nat.card DN ≤ Nat.card (Q.subgroupOf N) := by
        intro hcard
        exact hEq (Subgroup.eq_of_le_of_card_ge hQDN hcard).symm
      have hcardQ : Nat.card (Q.subgroupOf N) = Nat.card Q := by
        have hcard := Subgroup.card_map_of_injective (K := Q.subgroupOf N)
          (Subgroup.subtype_injective N)
        rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.le_normalizer (H := Q))] at hcard
        exact hcard.symm
      have hcardD : Nat.card D = Nat.card DN :=
        Subgroup.card_map_of_injective (Subgroup.subtype_injective N)
      rw [hcardD, ← hcardQ]
      exact Nat.lt_of_not_ge hnotle
    have hD1 : D ≠ ⊥ := fun hbot => hQ1 (le_bot_iff.mp (hbot ▸ hQD))
    let J := D ⊔ Subgroup.centralizer (D : Set G)
    have hJN : J ≤ N := nested_primary_join_le_first_normalizer Q D hQD hDN'
    have hCJ : Subgroup.centralizer (D : Set G) ≤ J := le_sup_right
    have hJND : J ≤ Subgroup.normalizer (D : Set G) := primary_centralizer_join_le_normalizer D
    have hlocalContains : Subgroup.centralizer (D.subgroupOf N : Set N) ≤ J.subgroupOf N :=
      relativeCentralizer_le_join_subgroupOf D N hDN' (hCJ.trans hJN)
    have hlocalNormalizes : J.subgroupOf N ≤ Subgroup.normalizer (D.subgroupOf N : Set N) :=
      relativeNormalizer_join_subgroupOf D N hDN'
    obtain ⟨internalBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := J.subgroupOf N)
    rw [← hlocalD] at hDN
    obtain ⟨internalLabel, hlocalImage⟩ := brauerNormalizer_local_block_exists_of_subconjugate
      normalizerBasis ideal p (D.subgroupOf N) hDp.comap_subtype (J.subgroupOf N) hlocalContains
      hlocalNormalizes internalBasis hDN (subgroupSubconjugate_refl _)
    obtain ⟨jBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := J)
    obtain ⟨γ, htransport⟩ := centralCharacterResidueHom_transport_exists internalBasis jBasis ideal
      (Subgroup.subgroupOfEquivOfLe hJN) internalLabel
    have hγB : brauerNormalizerCharacterResidueHom ideal p D hDp J hCJ hJND jBasis γ =
        centralCharacterResidueHom basis ideal B := by
      apply RingHom.ext
      intro z
      have htower := centralNormalizerCoefficientProjection_tower
        (localizedComplexIntegerRing ideal)
        Q D N J hQD hDN' hJN (Subgroup.centralizer_le_normalizer _) le_rfl hCJ hJND hlocalContains
        hlocalNormalizes z
      have hvalue := htransport (centralNormalizerCoefficientProjection _ (D.subgroupOf N)
        (J.subgroupOf N) hlocalContains hlocalNormalizes
          (centralNormalizerCoefficientProjection _ Q N (Subgroup.centralizer_le_normalizer _)
            le_rfl z))
      rw [htower] at hvalue
      have hlocalValue := congrArg (fun hom => hom (centralNormalizerCoefficientProjection _ Q N
        (Subgroup.centralizer_le_normalizer _) le_rfl z)) hlocalImage
      have himageValue := congrArg (fun hom => hom z) hβNB
      exact hvalue.trans (hlocalValue.trans himageValue)
    have hγweighted := hlarger D hDp hD1 hstrict J le_sup_left hCJ hJND jBasis γ hγB
    apply hβN'
    intro w
    have hlocalValue := congrArg (fun hom => hom w) hlocalImage
    change centralCharacterResidueHom internalBasis ideal internalLabel
      (centralNormalizerCoefficientProjection _ (D.subgroupOf N) (J.subgroupOf N) hlocalContains
        hlocalNormalizes w) = _ at hlocalValue
    rw [← hlocalValue, ← htransport, hγweighted,
      linearWeightedResidue_orbit hψ ideal Q D N hQp hQ1 hDp hQD hDN' hDN'
        (Subgroup.centralizer_le_normalizer _) w]
    unfold linearWeightedResidue
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 2
    apply Subtype.ext
    dsimp only
    rw [centralCoefficientTransport_coeff, centralNormalizerCoefficientProjection_coeff]
    have hmem : ((Subgroup.subgroupOfEquivOfLe hJN).symm (Subgroup.inclusion hCJ c)).val ∈
        Subgroup.centralizer (D.subgroupOf N : Set N) :=
      (relativeCentralizer_mem_iff D N hDN' _).mpr c.property
    rw [ite_eq_left hmem]
    rfl

end Main

section Twist

variable {K : Type*} [Group K] [Fintype K]

theorem exists_twisted_label (basis : FiniteIrreducibleCharacterBasis K) (μ : K →* ℂˣ)
    (χ : basis.index) :
    ∃ χ' : basis.index, ∀ k, (basis.representation χ').character k =
      (μ k : ℂ) * (basis.representation χ).character k := by
  let data : FiniteComplexRepresentation K :=
    { vector := (basis.representation χ).vector
      representation := CFSG.Section1.representationTwistByCharacter μ
        (basis.representation χ).representation }
  have hirreducible : data.IsIrreducible :=
    CFSG.Section1.irreducible_twistByCharacter μ _ (basis.irreducible χ)
  obtain ⟨χ', hχ'⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis data hirreducible
  refine ⟨χ', fun k => ?_⟩
  rw [hχ']
  change (CFSG.Section1.representationTwistByCharacter μ
    (basis.representation χ).representation).character k = _
  rw [CFSG.Section1.representationTwistByCharacter_character, Pi.mul_apply]

@[expose] noncomputable def twistCentral (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime]
    (μ : K →* ℂˣ) (w : centralCoefficientSubring (G := K) (localizedComplexIntegerRing ideal)) :
    centralCoefficientSubring (G := K) (localizedComplexIntegerRing ideal) :=
  ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun k => w.val.coeff k * μ k), by
    constructor
    · intro k
      exact (localizedComplexIntegerRing ideal).mul_mem
        (centralCoefficientSubring_coefficients _ w k) (linear_value_mem ideal μ k)
    · apply Subring.mem_center_iff.mpr
      intro other
      apply Commute.symm
      apply groupAlgebra_central_of_coeff_conjugation
      intro x g
      change w.val.coeff (g * x * g⁻¹) * (μ (g * x * g⁻¹) : ℂ) = w.val.coeff x * (μ x : ℂ)
      rw [central_groupAlgebra_coeff_conjugation w.val (centralCoefficientSubring_commutes _ w),
        map_mul, map_mul, map_inv, mul_comm (μ g) (μ x), mul_assoc, mul_inv_cancel, mul_one]⟩

theorem twistCentral_coeff (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime]
    (μ : K →* ℂˣ) (w : centralCoefficientSubring (G := K) (localizedComplexIntegerRing ideal))
    (k : K) : (twistCentral ideal μ w).val.coeff k = w.val.coeff k * μ k := rfl

theorem centralCharacterResidueHom_twist (basis : FiniteIrreducibleCharacterBasis K)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (μ : K →* ℂˣ)
    {χ χ' : basis.index}
    (hχ' : ∀ k, (basis.representation χ').character k =
      (μ k : ℂ) * (basis.representation χ).character k)
    (w : centralCoefficientSubring (G := K) (localizedComplexIntegerRing ideal)) :
    centralCharacterResidueHom basis ideal χ' w =
      centralCharacterResidueHom basis ideal χ (twistCentral ideal μ w) := by
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal χ' w) =
    localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal χ _)
  congr 1
  apply Subtype.ext
  rw [localCentralCharacterHom_coe, localCentralCharacterHom_coe]
  unfold centralCharacterScalar characterPairing
  have hdegree : (basis.representation χ').character 1 = (basis.representation χ).character 1 := by
    rw [hχ', map_one, Units.val_one, one_mul]
  rw [hdegree]
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  dsimp only
  rw [hχ', twistCentral_coeff]
  ring

theorem sameCoefficientBlock_twist_iff (basis : FiniteIrreducibleCharacterBasis K)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (μ : K →* ℂˣ)
    {χ₁ χ₂ χ₁' χ₂' : basis.index}
    (h₁ : ∀ k, (basis.representation χ₁').character k =
      (μ k : ℂ) * (basis.representation χ₁).character k)
    (h₂ : ∀ k, (basis.representation χ₂').character k =
      (μ k : ℂ) * (basis.representation χ₂).character k) :
    sameCoefficientBlock basis (localizedComplexIntegerRing ideal) χ₁ χ₂ ↔
      sameCoefficientBlock basis (localizedComplexIntegerRing ideal) χ₁' χ₂' := by
  have hinverse : ∀ {χ χ' : basis.index}, (∀ k, (basis.representation χ').character k =
      (μ k : ℂ) * (basis.representation χ).character k) →
      ∀ k, (basis.representation χ).character k =
        ((μ⁻¹ : K →* ℂˣ) k : ℂ) * (basis.representation χ').character k := by
    intro χ χ' h k
    rw [h, MonoidHom.inv_apply, ← mul_assoc, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ (μ k).ne_zero, one_mul]
  rw [sameCoefficientBlock_iff_centralCharacterResidueHom_eq,
    sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
  constructor
  · intro hequal
    apply RingHom.ext
    intro w
    rw [centralCharacterResidueHom_twist basis ideal μ h₁,
      centralCharacterResidueHom_twist basis ideal μ h₂, hequal]
  · intro hequal
    apply RingHom.ext
    intro w
    rw [centralCharacterResidueHom_twist basis ideal μ⁻¹ (hinverse h₁),
      centralCharacterResidueHom_twist basis ideal μ⁻¹ (hinverse h₂), hequal]

theorem linear_block_eq_twist_principal (basis : FiniteIrreducibleCharacterBasis K)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (μ : K →* ℂˣ)
    (μLabel principal : basis.index) (hμ : ∀ k, (basis.representation μLabel).character k = μ k)
    (hprincipal : (basis.representation principal).character = 1) (θ' : basis.index) :
    θ' ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) μLabel ↔
      ∃ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ k, (basis.representation θ').character k =
          (μ k : ℂ) * (basis.representation χ).character k := by
  have hprincipalTwist : ∀ k, (basis.representation μLabel).character k =
      (μ k : ℂ) * (basis.representation principal).character k := by
    intro k
    rw [hμ, hprincipal, Pi.one_apply, mul_one]
  rw [coefficientBlock_mem_iff]
  constructor
  · intro hsame
    obtain ⟨χ, hχ⟩ := exists_twisted_label basis μ⁻¹ θ'
    have htwist : ∀ k, (basis.representation θ').character k =
        (μ k : ℂ) * (basis.representation χ).character k := by
      intro k
      rw [hχ, MonoidHom.inv_apply, ← mul_assoc, Units.val_inv_eq_inv_val,
        mul_inv_cancel₀ (μ k).ne_zero, one_mul]
    refine ⟨χ, (coefficientBlock_mem_iff _ _ _ _).mpr
      ((sameCoefficientBlock_twist_iff basis ideal μ hprincipalTwist htwist).mpr hsame), htwist⟩
  · rintro ⟨χ, hχ, htwist⟩
    exact (sameCoefficientBlock_twist_iff basis ideal μ hprincipalTwist htwist).mp
      ((coefficientBlock_mem_iff _ _ _ _).mp hχ)

end Twist

end CompatibleFamily

open CompatibleFamily

theorem compatible_family_unique_local_blocks [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (S : Sylow p G) (hS1 : (S : Subgroup G) ≠ ⊥)
    (hNS : ∀ x ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
      ∃ q ∈ (S : Subgroup G), ∃ c ∈ Subgroup.centralizer ((S : Subgroup G) : Set G), x = q * c)
    (θ : Subgroup.centralizer ((S : Subgroup G) : Set G) → ℂ)
    (ψ : ∀ Q : Subgroup G, Subgroup.centralizer (Q : Set G) →* ℂˣ)
    (hψ : CompatibleCentralizerFamily p (S : Subgroup G) θ ψ)
    (normalizerBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (lambdaLabel : normalizerBasis.index)
    (hlambda : ∀ (x : Subgroup.normalizer ((S : Subgroup G) : Set G)) (q : G)
      (c : Subgroup.centralizer ((S : Subgroup G) : Set G)), q ∈ (S : Subgroup G) →
        (x : G) = q * c → (normalizerBasis.representation lambdaLabel).character x = ψ S c)
    (B : basis.index)
    (hB : brauerNormalizerCharacterResidueHom ideal p (S : Subgroup G) S.isPGroup'
      (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _) le_rfl
        normalizerBasis lambdaLabel = centralCharacterResidueHom basis ideal B) :
    coefficientBlockDefect basis ideal p B S ∧
    (∀ Q : Subgroup G, IsPGroup p Q → Q ≠ ⊥ →
      ∃ lambdaQ : (Q ⊔ Subgroup.centralizer (Q : Set G) : Subgroup G) →* ℂˣ,
        ∀ (x : (Q ⊔ Subgroup.centralizer (Q : Set G) : Subgroup G)) (q : G)
          (c : Subgroup.centralizer (Q : Set G)), q ∈ Q → (x : G) = q * c → lambdaQ x = ψ Q c) ∧
    (∀ (Q : Subgroup G) (hQ : IsPGroup p Q), Q ≠ ⊥ → ∀ (H : Subgroup G), Q ≤ H →
      ∀ (hCH : Subgroup.centralizer (Q : Set G) ≤ H) (hHN : H ≤ Subgroup.normalizer (Q : Set G))
        (localBasis : FiniteIrreducibleCharacterBasis H),
        (∃ β, brauerNormalizerCharacterResidueHom ideal p Q hQ H hCH hHN localBasis β =
          centralCharacterResidueHom basis ideal B) ∧
        (∀ β β', brauerNormalizerCharacterResidueHom ideal p Q hQ H hCH hHN localBasis β =
            centralCharacterResidueHom basis ideal B →
          brauerNormalizerCharacterResidueHom ideal p Q hQ H hCH hHN localBasis β' =
            centralCharacterResidueHom basis ideal B →
          sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) β β') ∧
        ∀ (centralizerBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Q : Set G)))
          (ψLabel : centralizerBasis.index),
          (∀ c, (centralizerBasis.representation ψLabel).character c = ψ Q c) →
          ∀ β, brauerNormalizerCharacterResidueHom ideal p Q hQ H hCH hHN localBasis β =
              centralCharacterResidueHom basis ideal B →
            ExternalResidueMatch Q H hCH localBasis ideal centralizerBasis β ψLabel ∧
            ∀ θ', ExternalResidueMatch Q H hCH localBasis ideal centralizerBasis β θ' →
              sameCoefficientBlock centralizerBasis (localizedComplexIntegerRing ideal) θ' ψLabel) ∧
    (∀ (Q : Subgroup G) (hQ : IsPGroup p Q), Q ≠ ⊥ →
      ∀ (localBasis :
          FiniteIrreducibleCharacterBasis (Q ⊔ Subgroup.centralizer (Q : Set G) : Subgroup G))
        (label : localBasis.index),
        (∀ (x : (Q ⊔ Subgroup.centralizer (Q : Set G) : Subgroup G)) (q : G)
          (c : Subgroup.centralizer (Q : Set G)), q ∈ Q → (x : G) = q * c →
            (localBasis.representation label).character x = ψ Q c) →
        brauerNormalizerCharacterResidueHom ideal p Q hQ (Q ⊔ Subgroup.centralizer (Q : Set G))
          le_sup_right (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _))
          localBasis label = centralCharacterResidueHom basis ideal B) ∧
    (∀ (Q : Subgroup G) (hQ : IsPGroup p Q), Q ≠ ⊥ → IsCyclic Q →
      Q ⊔ Subgroup.centralizer (Q : Set G) = Subgroup.centralizer (Q : Set G) ∧
      ∀ (centralizerBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Q : Set G)))
        (ψLabel principal : centralizerBasis.index),
        (∀ c, (centralizerBasis.representation ψLabel).character c = ψ Q c) →
        (centralizerBasis.representation principal).character = 1 →
        brauerNormalizerCharacterResidueHom ideal p Q hQ (Subgroup.centralizer (Q : Set G)) le_rfl
            (Subgroup.centralizer_le_normalizer _) centralizerBasis ψLabel =
          centralCharacterResidueHom basis ideal B ∧
        (∀ β, brauerNormalizerCharacterResidueHom ideal p Q hQ (Subgroup.centralizer (Q : Set G))
            le_rfl (Subgroup.centralizer_le_normalizer _) centralizerBasis β =
              centralCharacterResidueHom basis ideal B →
          sameCoefficientBlock centralizerBasis (localizedComplexIntegerRing ideal) β ψLabel) ∧
        ∀ θ', θ' ∈ coefficientBlock centralizerBasis (localizedComplexIntegerRing ideal) ψLabel ↔
          ∃ χ ∈ coefficientBlock centralizerBasis (localizedComplexIntegerRing ideal) principal,
            ∀ c, (centralizerBasis.representation θ').character c =
              (ψ Q c : ℂ) * (centralizerBasis.representation χ).character c) := by
  have hSp : IsPGroup p (S : Subgroup G) := S.isPGroup'
  have hψS1 := hψ.1 (S : Subgroup G) hSp hS1
  let ν := productLinearCharacter (S : Subgroup G) (ψ S) hψS1 _ hNS
  have hlabel : ∀ x, (normalizerBasis.representation lambdaLabel).character x = ν x := by
    intro x
    obtain ⟨q, hq, c, hc, hx⟩ := hNS x x.property
    rw [hlambda x q ⟨c, hc⟩ hq hx, productLinearCharacter_apply _ _ hψS1 _ hNS x hq ⟨c, hc⟩ hx]
  have hlambdaWeighted := weightedLocalBlock_of_linear ideal p (S : Subgroup G) _ hSp
    Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _) le_rfl (ψ S) normalizerBasis ν
    lambdaLabel hlabel (fun c => productLinearCharacter_apply _ _ hψS1 _ hNS _ (q := 1)
      (Subgroup.one_mem _) c (by rw [one_mul]; rfl))
  have hBres : ∀ z, centralCharacterResidueHom basis ideal B z =
      linearWeightedResidue ideal (Subgroup.centralizer ((S : Subgroup G) : Set G)).subtype
        (ψ S) z := fun z => by
    rw [← hB]
    exact brauer_weightedLocalBlock ideal p _ _ hSp _ le_rfl (ψ S) normalizerBasis hlambdaWeighted z
  have hlambdaDefect := (CFSG.Wreathed.linear_character_block_has_sylow_defect normalizerBasis
    ideal p
    ν lambdaLabel hlabel (S.subtype Subgroup.le_normalizer)).1
  change coefficientBlockDefect normalizerBasis ideal p lambdaLabel
    ((S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G))) at hlambdaDefect
  have hBdef : coefficientBlockDefect basis ideal p B S :=
    defect_normalizer_brauer_image_defect basis ideal p _ hSp normalizerBasis hlambdaDefect hB
  have hmain := family_local_blocks_weighted basis ideal p S hS1 hNS hψ B hBres hBdef
  have hlocal : ∀ (Q : Subgroup G) (hQ : IsPGroup p Q), Q ≠ ⊥ → ∀ (H : Subgroup G), Q ≤ H →
      ∀ (hCH : Subgroup.centralizer (Q : Set G) ≤ H) (hHN : H ≤ Subgroup.normalizer (Q : Set G))
        (localBasis : FiniteIrreducibleCharacterBasis H),
        (∃ β, brauerNormalizerCharacterResidueHom ideal p Q hQ H hCH hHN localBasis β =
          centralCharacterResidueHom basis ideal B) ∧
        (∀ β β', brauerNormalizerCharacterResidueHom ideal p Q hQ H hCH hHN localBasis β =
            centralCharacterResidueHom basis ideal B →
          brauerNormalizerCharacterResidueHom ideal p Q hQ H hCH hHN localBasis β' =
            centralCharacterResidueHom basis ideal B →
          sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) β β') ∧
        ∀ (centralizerBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Q : Set G)))
          (ψLabel : centralizerBasis.index),
          (∀ c, (centralizerBasis.representation ψLabel).character c = ψ Q c) →
          ∀ β, brauerNormalizerCharacterResidueHom ideal p Q hQ H hCH hHN localBasis β =
              centralCharacterResidueHom basis ideal B →
            ExternalResidueMatch Q H hCH localBasis ideal centralizerBasis β ψLabel ∧
            ∀ θ', ExternalResidueMatch Q H hCH localBasis ideal centralizerBasis β θ' →
              sameCoefficientBlock centralizerBasis (localizedComplexIntegerRing ideal) θ'
                ψLabel := by
    intro Q hQ hQ1 H hQH hCH hHN localBasis
    refine ⟨brauerNormalizer_local_block_exists_of_subconjugate basis ideal p Q hQ H hCH hHN
      localBasis hBdef (pSubgroup_subconjugate_sylow S hQ), fun β β' hβ hβ' =>
        weightedLocalBlock_same ideal Q H hCH (ψ Q) localBasis
          (hmain Q hQ hQ1 H hQH hCH hHN localBasis β hβ)
          (hmain Q hQ hQ1 H hQH hCH hHN localBasis β' hβ'),
      fun centralizerBasis ψLabel hψLabel β hβ => ?_⟩
    have hmatch := (weightedLocalBlock_iff_match ideal p Q H hQ hQH hCH hHN (ψ Q) localBasis
      centralizerBasis ψLabel hψLabel β).mp (hmain Q hQ hQ1 H hQH hCH hHN localBasis β hβ)
    refine ⟨hmatch, fun θ' hθ' => ?_⟩
    obtain ⟨-, -, horbit, -⟩ := external_block_orbits ideal p Q H hQ hQH hCH hHN localBasis
      centralizerBasis
    obtain ⟨h, θ'', htransport, hsame⟩ := ((horbit β).2 ψLabel hmatch θ').mp hθ'
    have hinvariant : LabelTransport centralizerBasis centralizerBasis
        (centralizerConjugation Q h (hHN h.property)) ψLabel ψLabel := by
      intro x
      rw [hψLabel, hψLabel, family_conj_invariant hψ hQ hQ1 (hHN h.property) x _ rfl]
    rw [labelTransport_unique htransport hinvariant] at hsame
    exact sameCoefficientBlock_symm _ _ hsame
  refine ⟨hBdef, fun Q hQ hQ1 => ⟨productLinearCharacter Q (ψ Q) (hψ.1 Q hQ hQ1) _
      (join_centralizer_decomposition Q), fun x q c hq hx =>
        productLinearCharacter_apply _ _ _ _ _ x hq c hx⟩, hlocal, ?_, ?_⟩
  · intro Q hQ hQ1 localBasis label hlabelQ
    let νJ := productLinearCharacter Q (ψ Q) (hψ.1 Q hQ hQ1) _ (join_centralizer_decomposition Q)
    have hlab : ∀ x, (localBasis.representation label).character x = νJ x := by
      intro x
      obtain ⟨q, hq, c, hc, hx⟩ := join_centralizer_decomposition Q x x.property
      rw [hlabelQ x q ⟨c, hc⟩ hq hx, productLinearCharacter_apply _ _ _ _ _ x hq ⟨c, hc⟩ hx]
    have hJN : Q ⊔ Subgroup.centralizer (Q : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
      sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)
    have hweighted := weightedLocalBlock_of_linear ideal p Q _ hQ le_sup_left le_sup_right hJN (ψ Q)
      localBasis νJ label hlab (fun c => productLinearCharacter_apply _ _ _ _ _ _ (q := 1)
        (Subgroup.one_mem _) c (by rw [one_mul]; rfl))
    obtain ⟨β, hβ⟩ := (hlocal Q hQ hQ1 _ le_sup_left le_sup_right hJN localBasis).1
    have hβweighted := hmain Q hQ hQ1 _ le_sup_left le_sup_right hJN localBasis β hβ
    apply RingHom.ext
    intro z
    rw [brauer_weightedLocalBlock ideal p Q _ hQ le_sup_right hJN (ψ Q) localBasis hweighted z,
      ← brauer_weightedLocalBlock ideal p Q _ hQ le_sup_right hJN (ψ Q) localBasis hβweighted z, hβ]
  · intro Q hQ hQ1 hcyclic
    have hcommutative : IsMulCommutative Q := inferInstance
    have hQC : Q ≤ Subgroup.centralizer (Q : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact congrArg Subtype.val (hcommutative.is_comm.comm (⟨r, hr⟩ : Q) ⟨q, hq⟩)
    refine ⟨sup_eq_right.mpr hQC, fun centralizerBasis ψLabel principal hψLabel hprincipal => ?_⟩
    have hweighted := weightedLocalBlock_of_linear ideal p Q _ hQ hQC le_rfl
      (Subgroup.centralizer_le_normalizer _) (ψ Q) centralizerBasis (ψ Q) ψLabel hψLabel
      (fun c => rfl)
    obtain ⟨hexists, hunique, -⟩ := hlocal Q hQ hQ1 _ hQC le_rfl
      (Subgroup.centralizer_le_normalizer _) centralizerBasis
    obtain ⟨β, hβ⟩ := hexists
    have hβweighted := hmain Q hQ hQ1 _ hQC le_rfl (Subgroup.centralizer_le_normalizer _)
      centralizerBasis β hβ
    have hψB : brauerNormalizerCharacterResidueHom ideal p Q hQ (Subgroup.centralizer (Q : Set G))
        le_rfl (Subgroup.centralizer_le_normalizer _) centralizerBasis ψLabel =
          centralCharacterResidueHom basis ideal B := by
      apply RingHom.ext
      intro z
      rw [brauer_weightedLocalBlock ideal p Q _ hQ le_rfl (Subgroup.centralizer_le_normalizer _)
          (ψ Q) centralizerBasis hweighted z,
        ← brauer_weightedLocalBlock ideal p Q _ hQ le_rfl (Subgroup.centralizer_le_normalizer _)
          (ψ Q) centralizerBasis hβweighted z, hβ]
    exact ⟨hψB, fun β' hβ' => hunique β' ψLabel hβ' hψB,
      linear_block_eq_twist_principal centralizerBasis ideal (ψ Q) ψLabel principal hψLabel
        hprincipal⟩

end CFSG.Wreathed
