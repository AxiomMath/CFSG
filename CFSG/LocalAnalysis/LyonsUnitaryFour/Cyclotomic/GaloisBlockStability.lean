module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.ConjugateRepresentation
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.TraceValues
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralClassCoordinates
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCharacterResidueCriterion

public section

namespace CFSG.LyonsUnitaryFour

open IntermediateField CFSG.TwoRankLowerBound.Helpers

section Powers

variable {G : Type*} [Group G]

@[expose] def conjClassesPow (k : ℕ) : ConjClasses G → ConjClasses G :=
  Quotient.lift (fun g => ConjClasses.mk (g ^ k)) fun _ _ h =>
    ConjClasses.mk_eq_mk_iff_isConj.mpr (IsConj.pow k h)

@[simp] theorem conjClassesPow_mk (k : ℕ) (g : G) :
    conjClassesPow k (ConjClasses.mk g) = ConjClasses.mk (g ^ k) := rfl

variable {k : ℕ}

theorem conjClassesPow_injective (hk : (Nat.card G).Coprime k) :
    Function.Injective (conjClassesPow (G := G) k) := by
  intro C D h
  obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C
  obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective D
  rw [conjClassesPow_mk, conjClassesPow_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  refine ⟨c, (powCoprime hk).injective ?_⟩
  simp only [powCoprime_apply]
  rw [← hc, conj_pow]

theorem conjClassesPow_bijective (hk : (Nat.card G).Coprime k) :
    Function.Bijective (conjClassesPow (G := G) k) := by
  refine ⟨conjClassesPow_injective hk, fun C => ?_⟩
  obtain ⟨c, rfl⟩ := ConjClasses.mk_surjective C
  obtain ⟨y, hy⟩ := (powCoprime hk).surjective c
  exact ⟨ConjClasses.mk y, by rw [conjClassesPow_mk, ← hy, powCoprime_apply]⟩

theorem mem_carrier_conjClassesPow_iff (hk : (Nat.card G).Coprime k) (C : ConjClasses G)
    (g : G) : g ^ k ∈ (conjClassesPow k C).carrier ↔ g ∈ C.carrier := by
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mem_carrier_iff_mk_eq, ← conjClassesPow_mk]
  exact (conjClassesPow_injective hk).eq_iff

theorem carrier_conjClassesPow (hk : (Nat.card G).Coprime k) (C : ConjClasses G) :
    (conjClassesPow k C).carrier = (fun g => g ^ k) '' C.carrier ∧
      Nat.card (conjClassesPow k C).carrier = Nat.card C.carrier := by
  have himage : (conjClassesPow k C).carrier = (powCoprime hk) '' C.carrier := by
    ext y
    obtain ⟨x, rfl⟩ := (powCoprime hk).surjective y
    rw [(powCoprime hk).injective.mem_set_image, powCoprime_apply,
      mem_carrier_conjClassesPow_iff hk]
  refine ⟨himage, ?_⟩
  rw [himage, Nat.card_image_of_injective (powCoprime hk).injective]

end Powers

section Basis

variable {G : Type*} [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G) {k : ℕ}

open scoped Classical in
theorem centralCharacterScalar_eq_sum (z : MonoidAlgebra ℂ G) (a : basis.index) :
    centralCharacterScalar basis z a =
      (∑ x : G, z.coeff x * (basis.representation a).character x) /
        (basis.representation a).character 1 := by
  unfold centralCharacterScalar characterPairing
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [mul_inv_cancel_left₀ hG]
  congr 1
  exact Equiv.sum_comp (Equiv.inv G) (fun x => z.coeff x * (basis.representation a).character x)

open scoped Classical in
theorem centralCharacterScalar_conjugacyClassSum_eq (C : ConjClasses G) {c : G}
    (hc : ConjClasses.mk c = C) (a : basis.index) :
    centralCharacterScalar basis (conjugacyClassSum C) a =
      Nat.card C.carrier * (basis.representation a).character c /
        (basis.representation a).character 1 := by
  rw [centralCharacterScalar_eq_sum]
  congr 1
  have hconst : ∀ x : G, (conjugacyClassSum C : MonoidAlgebra ℂ G).coeff x *
      (basis.representation a).character x =
        if x ∈ C.carrier then (basis.representation a).character c else 0 := by
    intro x
    rw [conjugacyClassSum_coeff, ConjClasses.mem_carrier_iff_mk_eq]
    split_ifs with hx
    · rw [one_mul]
      rw [← hc, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hx
      obtain ⟨g, rfl⟩ := hx
      exact (Representation.char_conj (basis.representation a).representation x g).symm
    · rw [zero_mul]
  simp only [hconst]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun x => x ∈ C.carrier).card = Nat.card C.carrier := by
    rw [Nat.card_eq_card_toFinset]
    congr 1
    ext x
    simp
  rw [hcard]

variable {π : Equiv.Perm basis.index}

open scoped Classical in
theorem centralCharacterScalar_conjugacyClassSum_perm (hk : (Nat.card G).Coprime k)
    (hπ : ∀ a g, (basis.representation (π a)).character g =
      (basis.representation a).character (g ^ k)) (C : ConjClasses G) (a : basis.index) :
    centralCharacterScalar basis (conjugacyClassSum C) (π a) =
      centralCharacterScalar basis (conjugacyClassSum (conjClassesPow k C)) a := by
  rw [centralCharacterScalar_eq_sum, centralCharacterScalar_eq_sum, hπ a 1, one_pow]
  congr 1
  simp only [hπ, conjugacyClassSum_coeff]
  conv_rhs => rw [← Equiv.sum_comp (powCoprime hk)]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [powCoprime_apply, ← conjClassesPow_mk, (conjClassesPow_injective hk).eq_iff]

theorem sameCoefficientBlock_perm_iff (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (hk : (Nat.card G).Coprime k)
    (hπ : ∀ a g, (basis.representation (π a)).character g =
      (basis.representation a).character (g ^ k)) (a b : basis.index) :
    sameCoefficientBlock basis (localizedComplexIntegerRing ideal) (π a) (π b) ↔
      sameCoefficientBlock basis (localizedComplexIntegerRing ideal) a b := by
  have hres : ∀ (c : basis.index) (C : ConjClasses G),
      centralCharacterResidueHom basis ideal (π c)
          (centralConjugacyClassSum (localizedComplexIntegerRing ideal) C) =
        centralCharacterResidueHom basis ideal c
          (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (conjClassesPow k C)) := by
    intro c C
    have h : localCentralCharacterHom basis ideal (π c)
          (centralConjugacyClassSum (localizedComplexIntegerRing ideal) C) =
        localCentralCharacterHom basis ideal c
          (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (conjClassesPow k C)) :=
      Subtype.ext (by
        rw [localCentralCharacterHom_coe, localCentralCharacterHom_coe]
        exact centralCharacterScalar_conjugacyClassSum_perm basis hk hπ C c)
    unfold centralCharacterResidueHom
    rw [RingHom.comp_apply, RingHom.comp_apply, h]
  have hclass : ∀ c d : basis.index,
      sameCoefficientBlock basis (localizedComplexIntegerRing ideal) c d ↔
        ∀ C, centralCharacterResidueHom basis ideal c
            (centralConjugacyClassSum (localizedComplexIntegerRing ideal) C) =
          centralCharacterResidueHom basis ideal d
            (centralConjugacyClassSum (localizedComplexIntegerRing ideal) C) := by
    intro c d
    rw [sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
    exact ⟨fun h C => by rw [h], centralCharacterResidueHom_eq_of_class_values basis ideal c d⟩
  rw [hclass, hclass]
  simp only [hres]
  exact ((conjClassesPow_bijective hk).surjective.forall (p := fun C =>
    centralCharacterResidueHom basis ideal a
        (centralConjugacyClassSum (localizedComplexIntegerRing ideal) C) =
      centralCharacterResidueHom basis ideal b
        (centralConjugacyClassSum (localizedComplexIntegerRing ideal) C))).symm

theorem coefficientBlock_image_perm (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (hk : (Nat.card G).Coprime k)
    (hπ : ∀ a g, (basis.representation (π a)).character g =
      (basis.representation a).character (g ^ k)) (a : basis.index) :
    (coefficientBlock basis (localizedComplexIntegerRing ideal) a).map π.toEmbedding =
      coefficientBlock basis (localizedComplexIntegerRing ideal) (π a) := by
  ext b
  rw [Finset.mem_map_equiv, coefficientBlock_mem_iff, coefficientBlock_mem_iff,
    ← sameCoefficientBlock_perm_iff basis ideal hk hπ, π.apply_symm_apply]

theorem finrank_perm_eq
    (hπ : ∀ a g, (basis.representation (π a)).character g =
      (basis.representation a).character (g ^ k)) (a : basis.index) :
    Module.finrank ℂ (basis.representation (π a)).vector =
      Module.finrank ℂ (basis.representation a).vector := by
  have h := hπ a 1
  rw [one_pow, FiniteComplexRepresentation.character, FiniteComplexRepresentation.character,
    Representation.char_one, Representation.char_one] at h
  exact_mod_cast h

theorem perm_principal_eq
    (hπ : ∀ a g, (basis.representation (π a)).character g =
      (basis.representation a).character (g ^ k)) {a : basis.index}
    (ha : (basis.representation a).character = 1) : π a = a := by
  apply basis.distinct
  funext g
  change (basis.representation (π a)).character g = (basis.representation a).character g
  rw [hπ a g, ha, Pi.one_apply, Pi.one_apply]

theorem perm_mem_principal_block_iff (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (hk : (Nat.card G).Coprime k)
    (hπ : ∀ a g, (basis.representation (π a)).character g =
      (basis.representation a).character (g ^ k)) {a : basis.index}
    (ha : (basis.representation a).character = 1) (b : basis.index) :
    π b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) a ↔
      b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) a := by
  rw [coefficientBlock_mem_iff, coefficientBlock_mem_iff, ← perm_principal_eq basis hπ ha,
    sameCoefficientBlock_perm_iff basis ideal hk hπ, perm_principal_eq basis hπ ha]

theorem exists_galois_gen_eq_pow_coprime {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯) :
    ∃ k : ℕ, k.Coprime N ∧ (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k := by
  have : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := isCyclotomicExtension_adjoin_primitiveRoot hζ
  have : NumberField ℚ⟮ζ⟯ := IsCyclotomicExtension.numberField {N} ℚ ℚ⟮ζ⟯
  refine ⟨((IsCyclotomicExtension.Rat.galEquivZMod N ℚ⟮ζ⟯ σ : (ZMod N)ˣ) : ZMod N).val,
    ZMod.val_coe_unit_coprime _, ?_⟩
  rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N ℚ⟮ζ⟯ σ
    (isPrimitiveRoot_adjoinSimple_gen hζ).pow_eq_one]
  simp

theorem galois_block_stability (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    {N : ℕ} [NeZero N] (hGN : Nat.card G ∣ N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hk : k.Coprime N) {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯} (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) :
    ∃ π : Equiv.Perm basis.index,
      (∀ a g, (basis.representation (π a)).character g =
        (basis.representation a).character (g ^ k)) ∧
      (∀ a g, ∃ h : (basis.representation a).character g ∈ ℚ⟮ζ⟯,
        ((σ ⟨(basis.representation a).character g, h⟩ : ℚ⟮ζ⟯) : ℂ) =
          (basis.representation (π a)).character g) ∧
      (∀ a, Module.finrank ℂ (basis.representation (π a)).vector =
        Module.finrank ℂ (basis.representation a).vector) ∧
      (∀ a b, sameCoefficientBlock basis (localizedComplexIntegerRing ideal) (π a) (π b) ↔
        sameCoefficientBlock basis (localizedComplexIntegerRing ideal) a b) ∧
      (∀ a, (coefficientBlock basis (localizedComplexIntegerRing ideal) a).map π.toEmbedding =
        coefficientBlock basis (localizedComplexIntegerRing ideal) (π a)) ∧
      (∀ a, (basis.representation a).character = 1 → π a = a) ∧
      (∀ a b, (basis.representation a).character = 1 →
        (π b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) a ↔
          b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) a)) := by
  have hkG : (Nat.card G).Coprime k := (Nat.Coprime.coprime_dvd_right hGN hk).symm
  obtain ⟨π, hπ⟩ := exists_perm_character_pow basis hkG
  have hgN : ∀ g : G, g ^ N = 1 := fun g =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard g).trans hGN)
  refine ⟨π, hπ, fun a g => ⟨character_mem_adjoin hζ _ (hgN g), ?_⟩,
    finrank_perm_eq basis hπ, sameCoefficientBlock_perm_iff basis ideal hkG hπ,
    coefficientBlock_image_perm basis ideal hkG hπ, fun a ha => perm_principal_eq basis hπ ha,
    fun a b ha => perm_mem_principal_block_iff basis ideal hkG hπ ha b⟩
  rw [hπ]
  exact galois_character_eq hζ hσ (basis.representation a).representation (hgN g)

end Basis

end CFSG.LyonsUnitaryFour
