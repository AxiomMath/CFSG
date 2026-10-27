module

public import CFSG.CharacterTheory.Semidihedral.Principal.CentralQuotientBlocks
public import CFSG.CharacterTheory.Semidihedral.Principal.CentralQuotientRegular
public import CFSG.CharacterTheory.Semidihedral.Principal.TensorGapBound

public noncomputable section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u

section Regular

variable {E : Type u} [Group E] [Fintype E] (p : ℕ)

@[expose] def primeRegular (E : Type u) [Group E] (p : ℕ) : Set E := {x | ¬ p ∣ orderOf x}

@[expose] def regularRestriction : (E → ℂ) →ₗ[ℂ] (primeRegular E p → ℂ) :=
  LinearMap.funLeft ℂ ℂ Subtype.val

@[expose] def regularExtension : (primeRegular E p → ℂ) →ₗ[ℂ] (E → ℂ) where
  toFun v x := if h : x ∈ primeRegular E p then v ⟨x, h⟩ else 0
  map_add' v w := by
    funext x
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c v := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

omit [Fintype E] in
theorem regularRestriction_apply (f : E → ℂ) (x : primeRegular E p) :
    regularRestriction p f x = f x := rfl

omit [Fintype E] in
theorem regularRestriction_regularExtension (v : primeRegular E p → ℂ) :
    regularRestriction p (regularExtension p v) = v := by
  funext x
  simp [regularRestriction, regularExtension, LinearMap.funLeft_apply, x.2]

omit [Fintype E] in
theorem regularExtension_regularRestriction (f : E → ℂ) :
    regularExtension p (regularRestriction p f) = characterFunctionMask (primeRegular E p) f := by
  funext x
  simp only [regularExtension, regularRestriction, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.funLeft_apply, characterFunctionMask]
  split_ifs <;> rfl

@[expose] def regularPrincipalSpace (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principal : basis.index) :
    Submodule ℂ (primeRegular E p → ℂ) :=
  (coefficientCharacterSpace basis
    (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)).map
      (regularRestriction p)

omit [Fintype E] in
theorem primeSectionUnion_primeRegular [Fact p.Prime] : primeSectionUnion p (primeRegular E p) := by
  have h := regularElements_primeSectionUnion (G := E) p
  have heq : {x : E | p.Coprime (orderOf x)} = primeRegular E p := by
    ext x
    simp [primeRegular, (Fact.out : p.Prime).coprime_iff_not_dvd]
  rwa [heq] at h

variable (basis : FiniteIrreducibleCharacterBasis E) (ideal : Ideal ComplexAlgebraicIntegers)
  [ideal.IsMaximal] [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
  (principal : basis.index)

theorem regularExtension_mem {v : primeRegular E p → ℂ}
    (hv : v ∈ regularPrincipalSpace p basis ideal principal) :
    regularExtension p v ∈ coefficientCharacterSpace basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) := by
  obtain ⟨f, hf, rfl⟩ := hv
  rw [regularExtension_regularRestriction]
  exact coefficientBlock_section_mask_mem basis ideal p principal _
    (primeSectionUnion_primeRegular p) f hf

@[expose] def regularGram {ℓ : ℕ} (c : Fin ℓ → (primeRegular E p → ℂ)) (i j : Fin ℓ) : ℂ :=
  (Nat.card E : ℂ)⁻¹ * ∑ x, c i x * starRingEnd ℂ (c j x)

theorem regularGram_mul_rows {ℓ : ℕ} (c : Fin ℓ → (primeRegular E p → ℂ))
    (hc : ∀ j, c j ∈ regularPrincipalSpace p basis ideal principal)
    (hind : LinearIndependent ℂ c) (r : basis.index → Fin ℓ → ℂ)
    (hr : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      regularRestriction p (basis.representation χ).character = ∑ j, r χ j • c j)
    (i a : Fin ℓ) :
    ∑ j, regularGram p c i j *
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          starRingEnd ℂ (r χ j) * r χ a = if i = a then 1 else 0 := by
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  have hext := regularExtension_mem p basis ideal principal (hc i)
  have hexp := characterSubsetProjection_identity basis B _ hext
  have hpair : ∀ χ ∈ B, characterPairing (regularExtension p (c i))
      (basis.representation χ).character = ∑ j, starRingEnd ℂ (r χ j) * regularGram p c i j := by
    intro χ hχ
    unfold characterPairing regularGram
    have hsplit : ∑ x : E, regularExtension p (c i) x * (basis.representation χ).character x⁻¹ =
        ∑ x : primeRegular E p, c i x * starRingEnd ℂ (∑ j, r χ j * c j x) := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun x => x ∈ primeRegular E p)]
      have h0 : ∑ x : {x // x ∉ primeRegular E p},
          regularExtension p (c i) x * (basis.representation χ).character (x : E)⁻¹ = 0 :=
        Finset.sum_eq_zero fun x _ => by
          simp only [regularExtension, LinearMap.coe_mk, AddHom.coe_mk, x.2, ↓reduceDIte, zero_mul]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hval : (basis.representation χ).character (x : E) = ∑ j, r χ j * c j x := by
        have := congrFun (hr χ hχ) x
        simpa only [regularRestriction_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          using this
      simp only [regularExtension, LinearMap.coe_mk, AddHom.coe_mk, x.2, ↓reduceDIte]
      rw [← finite_character_conjugate_inverse, hval]
    rw [hsplit]
    simp_rw [map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  have hrestr : c i = ∑ a', (∑ χ ∈ B, characterPairing (regularExtension p (c i))
      (basis.representation χ).character * r χ a') • c a' := by
    have h := congrArg (regularRestriction p) hexp
    rw [regularRestriction_regularExtension] at h
    conv_lhs => rw [← h]
    change regularRestriction p (∑ χ ∈ B, characterPairing (regularExtension p (c i))
      (basis.representation χ).character • (basis.representation χ).character) = _
    rw [map_sum]
    simp_rw [map_smul]
    rw [Finset.sum_congr rfl fun χ hχ => by rw [hr χ hχ]]
    simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  have hcoeff := (Fintype.linearIndependent_iff.mp hind)
    (fun a' => (∑ χ ∈ B, characterPairing (regularExtension p (c i))
      (basis.representation χ).character * r χ a') - if a' = i then 1 else 0) (by
        simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [← hrestr, sub_self]) a
  rw [sub_eq_zero] at hcoeff
  rw [show (if i = a then (1 : ℂ) else 0) = if a = i then 1 else 0 by
    by_cases h : i = a <;> simp [h, eq_comm], ← hcoeff]
  have hrhs : ∑ χ ∈ B, characterPairing (regularExtension p (c i))
      (basis.representation χ).character * r χ a =
      ∑ χ ∈ B, (∑ j, starRingEnd ℂ (r χ j) * regularGram p c i j) * r χ a :=
    Finset.sum_congr rfl fun χ hχ => by rw [hpair χ hχ]
  rw [hrhs]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun χ _ => ?_
  ring

end Regular

section Quotient

variable {H : Type u} [Group H] [Fintype H] (Z : Subgroup H) [Z.Normal] (p : ℕ)

@[expose] def regularQuotientMap : primeRegular H p → primeRegular (H ⧸ Z) p :=
  fun x => ⟨QuotientGroup.mk' Z x, fun h => x.2 (h.trans (orderOf_map_dvd _ _))⟩

@[expose] def regularPullback : (primeRegular (H ⧸ Z) p → ℂ) →ₗ[ℂ] (primeRegular H p → ℂ) :=
  LinearMap.funLeft ℂ ℂ (regularQuotientMap Z p)

omit [Fintype H] in
theorem regularPullback_apply (v : primeRegular (H ⧸ Z) p → ℂ) (x : primeRegular H p) :
    regularPullback Z p v x = v (regularQuotientMap Z p x) := rfl

theorem regularQuotientMap_bijective [Fact p.Prime] (hZ : Z ≤ Subgroup.center H)
    (hZp : IsPGroup p Z) : Function.Bijective (regularQuotientMap Z p) :=
  (central_p_quotient_prime_regular_elements Z hZ hZp).1.bijective

@[expose] def deflation : (H → ℂ) →ₗ[ℂ] (H ⧸ Z → ℂ) where
  toFun f q := (Nat.card Z : ℂ)⁻¹ * ∑ h : H, if (h : H ⧸ Z) = q then f h else 0
  map_add' f g := by
    funext q
    simp only [Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> simp
  map_smul' c f := by
    funext q
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> ring

theorem characterPairing_deflation (f : H → ℂ) (g : H ⧸ Z → ℂ) :
    characterPairing (deflation Z f) g = characterPairing f (g ∘ QuotientGroup.mk' Z) := by
  unfold characterPairing
  have hcard : (Nat.card H : ℂ) = (Nat.card (H ⧸ Z) : ℂ) * (Nat.card Z : ℂ) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, Nat.cast_mul]
  have hsum : ∑ q : H ⧸ Z, deflation Z f q * g q⁻¹ =
      (Nat.card Z : ℂ)⁻¹ * ∑ h : H, f h * g ((h : H ⧸ Z))⁻¹ := by
    simp only [deflation, LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    congr 1
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  rw [hsum, hcard, mul_inv, ← mul_assoc]
  congr 1

omit [Fintype H] in
theorem coefficientCharacterSpace_class {E : Type*} [Group E] [Fintype E]
    (basis : FiniteIrreducibleCharacterBasis E) (support : Finset basis.index) {f : E → ℂ}
    (hf : f ∈ coefficientCharacterSpace basis support) (x c : E) :
    f (c * x * c⁻¹) = f x := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨χ, -, rfl⟩ := hg
    exact Representation.char_conj _ x c
  | zero => rfl
  | add f g _ _ hf hg => simp only [Pi.add_apply, hf, hg]
  | smul a f _ hf => simp only [Pi.smul_apply, hf]

theorem deflation_class {f : H → ℂ} (hf : ∀ x c : H, f (c * x * c⁻¹) = f x) (q c : H ⧸ Z) :
    deflation Z f (c * q * c⁻¹) = deflation Z f q := by
  obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective c
  simp only [deflation, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  refine Fintype.sum_equiv (MulAut.conj c'⁻¹).toEquiv _ _ fun h => ?_
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply, inv_inv]
  have hf' : f (c'⁻¹ * h * c') = f h := by
    have := hf h c'⁻¹
    rwa [inv_inv] at this
  have hiff : ((c'⁻¹ * h * c' : H) : H ⧸ Z) = q ↔
      (h : H ⧸ Z) = (c' : H ⧸ Z) * q * (c' : H ⧸ Z)⁻¹ := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    constructor
    · intro e
      rw [← e]
      group
    · intro e
      rw [e]
      group
  rw [hf']
  by_cases h1 : (h : H ⧸ Z) = (c' : H ⧸ Z) * q * (c' : H ⧸ Z)⁻¹
  · rw [ite_eq_left h1, ite_eq_left (hiff.mpr h1)]
  · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 (hiff.mp h2))]

variable [Fact p.Prime] (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
  [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (hZ : Z ≤ Subgroup.center H) (hZp : IsPGroup p Z)
  (basisH : FiniteIrreducibleCharacterBasis H) (basisQ : FiniteIrreducibleCharacterBasis (H ⧸ Z))
  (principalH : basisH.index) (hprincipalH : (basisH.representation principalH).character = 1)
  (principalQ : basisQ.index) (hprincipalQ : (basisQ.representation principalQ).character = 1)

include hZ hZp hprincipalH hprincipalQ

theorem inflation_mem_principal {f : H ⧸ Z → ℂ}
    (hf : f ∈ coefficientCharacterSpace basisQ
      (coefficientBlock basisQ (localizedComplexIntegerRing ideal) principalQ)) :
    f ∘ QuotientGroup.mk' Z ∈ coefficientCharacterSpace basisH
      (coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH) := by
  obtain ⟨-, -, -, -, -, -, -, -, hinf⟩ := central_p_quotient_relative_block_correspondence
    Z ideal p hZ hZp basisH basisQ principalH hprincipalH principalQ hprincipalQ
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨θ, hθ, rfl⟩ := hg
    obtain ⟨ψ, hψ, hψchar⟩ := hinf θ hθ
    rw [← hψchar]
    exact Submodule.subset_span ⟨ψ, hψ, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
  | smul a f _ hf => exact Submodule.smul_mem _ a hf

theorem deflation_mem_principal {f : H → ℂ}
    (hf : f ∈ coefficientCharacterSpace basisH
      (coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH)) :
    deflation Z f ∈ coefficientCharacterSpace basisQ
      (coefficientBlock basisQ (localizedComplexIntegerRing ideal) principalQ) := by
  obtain ⟨-, -, -, -, -, hchar, -, hprin, -⟩ := central_p_quotient_relative_block_correspondence
    Z ideal p hZ hZp basisH basisQ principalH hprincipalH principalQ hprincipalQ
  set BH := coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH
  set BQ := coefficientBlock basisQ (localizedComplexIntegerRing ideal) principalQ
  have horth : ∀ ψ ∉ BH, characterPairing f (basisH.representation ψ).character = 0 := by
    intro ψ hψ
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨χ, hχ, rfl⟩ := hg
      rw [characterPairing_irreducible _ _ (basisH.irreducible χ) (basisH.irreducible ψ),
        ite_eq_right fun h => hψ (by rw [← basisH.distinct h]; exact hχ)]
    | zero => simp [characterPairing]
    | add f g _ _ hf hg =>
      have hadd : characterPairing (f + g) (basisH.representation ψ).character =
          characterPairing f (basisH.representation ψ).character +
            characterPairing g (basisH.representation ψ).character := by
        unfold characterPairing
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Pi.add_apply]
        ring
      rw [hadd, hf, hg, add_zero]
    | smul a f _ hf =>
      have hsmul : characterPairing (a • f) (basisH.representation ψ).character =
          a * characterPairing f (basisH.representation ψ).character := by
        unfold characterPairing
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [hsmul, hf, mul_zero]
  have hclass : ∀ x c : H ⧸ Z, deflation Z f (c * x * c⁻¹) = deflation Z f x :=
    deflation_class Z (coefficientCharacterSpace_class basisH BH hf)
  have hrec : deflation Z f = ∑ θ ∈ BQ, characterPairing (deflation Z f)
      (basisQ.representation θ).character • (basisQ.representation θ).character := by
    funext q
    rw [finiteIrreducibleCharacterBasis_reconstruction basisQ _ hclass q]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_subset (Finset.subset_univ BQ)]
    intro θ _ hθ
    rw [characterPairing_deflation]
    obtain ⟨ψ, hψ, -⟩ := CFSG.Wreathed.complete_character_basis_contains_irreducible basisH
      (inflatedFiniteComplexRepresentation (QuotientGroup.mk' Z) (basisQ.representation θ))
      (CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective (QuotientGroup.mk' Z)
        (QuotientGroup.mk'_surjective Z) _ (basisQ.irreducible θ))
    have hψBH : ψ ∉ BH := fun h => hθ ((hchar principalH principalQ hprin θ ψ hψ).mp h)
    have hinf : (basisQ.representation θ).character ∘ QuotientGroup.mk' Z =
        (basisH.representation ψ).character := hψ.symm
    rw [hinf, horth ψ hψBH, zero_mul]
  rw [hrec]
  exact Submodule.sum_mem _ fun θ hθ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨θ, hθ, rfl⟩)

theorem exists_principal_deflation_regular {f : H → ℂ}
    (hf : f ∈ coefficientCharacterSpace basisH
      (coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH)) :
    ∃ g ∈ coefficientCharacterSpace basisQ
        (coefficientBlock basisQ (localizedComplexIntegerRing ideal) principalQ),
      ∀ x : primeRegular H p, g (QuotientGroup.mk' Z x) = f x := by
  set fm := characterFunctionMask (primeRegular H p) f with hfm_def
  have hfm := coefficientBlock_section_mask_mem basisH ideal p principalH _
    (primeSectionUnion_primeRegular p) f hf
  refine ⟨(Nat.card Z : ℂ) • deflation Z fm, Submodule.smul_mem _ _
    (deflation_mem_principal Z p ideal hZ hZp basisH basisQ principalH hprincipalH principalQ
      hprincipalQ hfm), fun x => ?_⟩
  have hker : (QuotientGroup.mk' Z).ker = Z := QuotientGroup.ker_mk' Z
  have hZ0 : (Nat.card Z : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  simp only [Pi.smul_apply, smul_eq_mul, deflation, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← mul_assoc, mul_inv_cancel₀ hZ0, one_mul, Finset.sum_eq_single (x : H)]
  · simp only [QuotientGroup.mk'_apply, ite_true, hfm_def, characterFunctionMask, x.2]
  · intro h _ hne
    by_cases hreg : h ∈ primeRegular H p
    · rw [ite_eq_right]
      intro heq
      exact hne (primeRegular_eq_of_map_eq (QuotientGroup.mk' Z) (by rw [hker]; exact hZ)
        (by rw [hker]; exact hZp) hreg x.2 heq)
    · simp [hfm_def, characterFunctionMask, hreg]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem map_regularPullback_eq :
    Submodule.map (regularPullback Z p) (regularPrincipalSpace p basisQ ideal principalQ) =
      regularPrincipalSpace p basisH ideal principalH := by
  apply le_antisymm
  · rintro _ ⟨v, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f ∘ QuotientGroup.mk' Z, inflation_mem_principal Z p ideal hZ hZp basisH basisQ
      principalH hprincipalH principalQ hprincipalQ hf, rfl⟩
  · rintro w ⟨f, hf, rfl⟩
    obtain ⟨g, hg, hgf⟩ := exists_principal_deflation_regular Z p ideal hZ hZp basisH basisQ
      principalH hprincipalH principalQ hprincipalQ hf
    refine ⟨regularRestriction p g, ⟨g, hg, rfl⟩, ?_⟩
    funext x
    exact hgf x

omit hprincipalH hprincipalQ in
theorem regularGram_regularPullback {ℓ : ℕ} (b : Fin ℓ → (primeRegular (H ⧸ Z) p → ℂ))
    (i j : Fin ℓ) :
    regularGram p (fun j => regularPullback Z p (b j)) i j =
      (Nat.card Z : ℂ)⁻¹ * regularGram p b i j := by
  unfold regularGram
  simp only [regularPullback_apply]
  rw [Fintype.sum_bijective (regularQuotientMap Z p) (regularQuotientMap_bijective Z p hZ hZp)
    _ (fun q => b i q * starRingEnd ℂ (b j q)) (fun x => rfl),
    Subgroup.card_eq_card_quotient_mul_card_subgroup Z, Nat.cast_mul, mul_inv]
  ring

theorem central_p_quotient_principal_regular_space_and_Gram {ℓ : ℕ}
    (b : Module.Basis (Fin ℓ) ℂ (regularPrincipalSpace p basisQ ideal principalQ)) :
    Function.Bijective (regularQuotientMap Z p) ∧
    (∃ e : regularPrincipalSpace p basisQ ideal principalQ ≃ₗ[ℂ]
        regularPrincipalSpace p basisH ideal principalH,
      ∀ v, (e v : primeRegular H p → ℂ) = regularPullback Z p v) ∧
    (∀ θ ∈ coefficientBlock basisQ (localizedComplexIntegerRing ideal) principalQ,
      ∃! d : Fin ℓ → ℂ, regularRestriction p (basisQ.representation θ).character =
        ∑ j, d j • (b j : primeRegular (H ⧸ Z) p → ℂ)) ∧
    (∀ χ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
      ∃! a : Fin ℓ → ℂ, regularRestriction p (basisH.representation χ).character =
        ∑ j, a j • regularPullback Z p (b j)) ∧
    ∀ (d : basisQ.index → Fin ℓ → ℂ) (a : basisH.index → Fin ℓ → ℂ),
      (∀ θ ∈ coefficientBlock basisQ (localizedComplexIntegerRing ideal) principalQ,
        regularRestriction p (basisQ.representation θ).character =
          ∑ j, d θ j • (b j : primeRegular (H ⧸ Z) p → ℂ)) →
      (∀ χ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        regularRestriction p (basisH.representation χ).character =
          ∑ j, a χ j • regularPullback Z p (b j)) →
      ∀ j k, ∑ χ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
          starRingEnd ℂ (a χ j) * a χ k =
        (Nat.card Z : ℂ) * ∑ θ ∈ coefficientBlock basisQ (localizedComplexIntegerRing ideal)
          principalQ, starRingEnd ℂ (d θ j) * d θ k := by
  have hmap := map_regularPullback_eq Z p ideal hZ hZp basisH basisQ principalH hprincipalH
    principalQ hprincipalQ
  have hinj : Function.Injective (regularPullback Z p) :=
    LinearMap.funLeft_injective_of_surjective ℂ ℂ _
      (regularQuotientMap_bijective Z p hZ hZp).2
  have hb : LinearIndependent ℂ (fun j => (b j : primeRegular (H ⧸ Z) p → ℂ)) :=
    b.linearIndependent.map' (regularPrincipalSpace p basisQ ideal principalQ).subtype
      (Submodule.ker_subtype _)
  have hpb : LinearIndependent ℂ (fun j => regularPullback Z p (b j)) :=
    hb.map' (regularPullback Z p) (LinearMap.ker_eq_bot.mpr hinj)
  have hpbmem : ∀ j, regularPullback Z p (b j) ∈
      regularPrincipalSpace p basisH ideal principalH := fun j => by
    rw [← hmap]
    exact Submodule.mem_map_of_mem (b j).2
  have hsum : ∀ v : regularPrincipalSpace p basisQ ideal principalQ,
      (v : primeRegular (H ⧸ Z) p → ℂ) =
      ∑ j, b.repr v j • (b j : primeRegular (H ⧸ Z) p → ℂ) := fun v => by
    conv_lhs => rw [← b.sum_repr v]
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  have huniqueH : ∀ (a a' : Fin ℓ → ℂ), ∑ j, a j • regularPullback Z p (b j) =
      ∑ j, a' j • regularPullback Z p (b j) → a = a' := by
    intro a a' h
    funext j
    have := (Fintype.linearIndependent_iff.mp hpb) (fun j => a j - a' j) (by
      simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]) j
    exact sub_eq_zero.mp this
  have huniqueQ : ∀ (d d' : Fin ℓ → ℂ), ∑ j, d j • (b j : primeRegular (H ⧸ Z) p → ℂ) =
      ∑ j, d' j • (b j : primeRegular (H ⧸ Z) p → ℂ) → d = d' := by
    intro d d' h
    funext j
    have := (Fintype.linearIndependent_iff.mp hb) (fun j => d j - d' j) (by
      simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]) j
    exact sub_eq_zero.mp this
  refine ⟨regularQuotientMap_bijective Z p hZ hZp,
    ⟨(Submodule.equivMapOfInjective _ hinj (regularPrincipalSpace p basisQ ideal principalQ)).trans
      (LinearEquiv.ofEq _ _ hmap),
    fun v => rfl⟩, ?_, ?_, ?_⟩
  · intro θ hθ
    have hmem : regularRestriction p (basisQ.representation θ).character ∈
        regularPrincipalSpace p basisQ ideal principalQ :=
      ⟨_, Submodule.subset_span ⟨θ, hθ, rfl⟩, rfl⟩
    refine ⟨fun j => b.repr ⟨_, hmem⟩ j, hsum ⟨_, hmem⟩, fun d hd => huniqueQ _ _ ?_⟩
    rw [← hd]
    exact hsum ⟨_, hmem⟩
  · intro χ hχ
    have hmem : regularRestriction p (basisH.representation χ).character ∈
        regularPrincipalSpace p basisH ideal principalH :=
      ⟨_, Submodule.subset_span ⟨χ, hχ, rfl⟩, rfl⟩
    rw [← hmap] at hmem
    obtain ⟨v, hv, hvχ⟩ := hmem
    have hexp : regularRestriction p (basisH.representation χ).character =
        ∑ j, b.repr ⟨v, hv⟩ j • regularPullback Z p (b j) := by
      rw [← hvχ]
      have := hsum ⟨v, hv⟩
      change regularPullback Z p v = _
      conv_lhs => rw [show v = ((⟨v, hv⟩ : regularPrincipalSpace p basisQ ideal principalQ) :
        primeRegular (H ⧸ Z) p → ℂ) from rfl, this]
      rw [map_sum]
      simp only [map_smul]
    refine ⟨fun j => b.repr ⟨v, hv⟩ j, hexp, fun a ha => huniqueH _ _ ?_⟩
    rw [← ha, ← hexp]
  · intro d a hd ha j k
    have hKQ := regularGram_mul_rows p basisQ ideal principalQ
      (fun j => (b j : primeRegular (H ⧸ Z) p → ℂ)) (fun j => (b j).2) hb d hd
    have hKH := regularGram_mul_rows p basisH ideal principalH
      (fun j => regularPullback Z p (b j)) hpbmem hpb a ha
    set KQ : Matrix (Fin ℓ) (Fin ℓ) ℂ :=
      Matrix.of (regularGram p (fun j => (b j : primeRegular (H ⧸ Z) p → ℂ)))
    set ND : Matrix (Fin ℓ) (Fin ℓ) ℂ := Matrix.of fun j k =>
      ∑ θ ∈ coefficientBlock basisQ (localizedComplexIntegerRing ideal) principalQ,
        starRingEnd ℂ (d θ j) * d θ k
    set NA : Matrix (Fin ℓ) (Fin ℓ) ℂ := Matrix.of fun j k =>
      ∑ χ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        starRingEnd ℂ (a χ j) * a χ k
    have hZ0 : (Nat.card Z : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have h1 : KQ * ND = 1 := by
      ext i a'
      rw [Matrix.mul_apply, Matrix.one_apply]
      exact hKQ i a'
    have h2 : KQ * NA = (Nat.card Z : ℂ) • 1 := by
      ext i a'
      rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      have h := hKH i a'
      simp only [regularGram_regularPullback Z p hZ hZp] at h
      simp only [KQ, NA, Matrix.of_apply]
      have hrw : ∑ x, regularGram p (fun j => (b j : primeRegular (H ⧸ Z) p → ℂ)) i x *
          ∑ χ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
            starRingEnd ℂ (a χ x) * a χ a' =
          (Nat.card Z : ℂ) * ∑ x, (Nat.card Z : ℂ)⁻¹ *
            regularGram p (fun j => (b j : primeRegular (H ⧸ Z) p → ℂ)) i x *
              ∑ χ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
                starRingEnd ℂ (a χ x) * a χ a' := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hZ0, one_mul]
      rw [hrw, h]
    have h3 : ND * KQ = 1 := mul_eq_one_comm.mp h1
    have h4 : NA = (Nat.card Z : ℂ) • ND := by
      calc NA = (ND * KQ) * NA := by rw [h3, Matrix.one_mul]
        _ = ND * (KQ * NA) := Matrix.mul_assoc _ _ _
        _ = (Nat.card Z : ℂ) • ND := by rw [h2, Matrix.mul_smul, Matrix.mul_one]
    have := congrFun (congrFun h4 j) k
    simpa only [NA, ND, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] using this

end Quotient

end CFSG.Semidihedral.Principal
