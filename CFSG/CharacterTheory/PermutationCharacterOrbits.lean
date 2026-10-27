module

public import CFSG.CharacterTheory.Blocks.IrreducibleCharacterBasis

public section

open scoped BigOperators Classical

namespace CFSG

open TwoRankLowerBound.Helpers

@[expose] noncomputable def permutationRepresentation (W I : Type*) [Group W] [MulAction W I] :
    Representation ℂ W (I → ℂ) where
  toFun w :=
    { toFun := fun f i => f (w⁻¹ • i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    refine LinearMap.ext fun f => funext fun i => ?_
    simp
  map_mul' w₁ w₂ := by
    refine LinearMap.ext fun f => funext fun i => ?_
    simp [mul_smul]

theorem permutationRepresentation_apply {W I : Type*} [Group W] [MulAction W I] (w : W)
    (f : I → ℂ) (i : I) : permutationRepresentation W I w f i = f (w⁻¹ • i) := rfl

@[expose] noncomputable def fixedPointCount (W I : Type*) [Group W] [MulAction W I] [Finite I]
    (w : W) : ℂ :=
  (Nat.card (MulAction.fixedBy I w) : ℂ)

theorem permutationRepresentation_character {W I : Type*} [Group W] [MulAction W I] [Fintype I]
    (w : W) : (permutationRepresentation W I).character w = fixedPointCount W I w := by
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ I),
    Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply,
    permutationRepresentation_apply, Pi.single_apply, inv_smul_eq_iff]
  rw [Finset.sum_boole, fixedPointCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 2
  ext i
  simp [MulAction.mem_fixedBy, eq_comm]

theorem fixedPointCount_inv {W I : Type*} [Group W] [MulAction W I] [Finite I] (w : W) :
    fixedPointCount W I w⁻¹ = fixedPointCount W I w := by
  rw [fixedPointCount, fixedPointCount, MulAction.fixedBy_inv]

theorem fixedPointCount_conj {W I : Type*} [Group W] [MulAction W I] [Finite I] (w : W) :
    starRingEnd ℂ (fixedPointCount W I w) = fixedPointCount W I w := by
  rw [fixedPointCount, Complex.conj_natCast]

theorem sum_fixedPointCount {W I : Type*} [Group W] [Fintype W] [MulAction W I] [Finite I] :
    (Nat.card W : ℂ)⁻¹ * ∑ w : W, fixedPointCount W I w =
      Nat.card (MulAction.orbitRel.Quotient W I) := by
  let _ : Fintype I := Fintype.ofFinite I
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group W I
  have hW : (Nat.card W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsum : ∑ w : W, fixedPointCount W I w =
      (Nat.card (MulAction.orbitRel.Quotient W I) * Nat.card W : ℕ) := by
    simp only [fixedPointCount, Nat.card_eq_fintype_card]
    rw [← Nat.cast_sum, h]
  rw [hsum]
  push_cast
  field_simp

theorem card_fixedBy_prod {W I : Type*} [Group W] [MulAction W I] [Finite I] (w : W) :
    Nat.card (MulAction.fixedBy (I × I) w) = Nat.card (MulAction.fixedBy I w) ^ 2 := by
  rw [sq, ← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun p => (⟨p.1.1, (Prod.ext_iff.mp p.2).1⟩, ⟨p.1.2, (Prod.ext_iff.mp p.2).2⟩)
      invFun := fun q => ⟨(q.1, q.2), Prod.ext q.1.2 q.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem blocksInnerProduct_fixedPointCount_one {W I : Type} [Group W] [Fintype W]
    [MulAction W I] [Finite I] :
    BlocksInnerProduct (fixedPointCount W I) 1 = Nat.card (MulAction.orbitRel.Quotient W I) := by
  rw [BlocksInnerProduct, ← sum_fixedPointCount]
  simp

theorem blocksInnerProduct_fixedPointCount_self {W I : Type} [Group W] [Fintype W]
    [MulAction W I] [Finite I] :
    BlocksInnerProduct (fixedPointCount W I) (fixedPointCount W I) =
      Nat.card (MulAction.orbitRel.Quotient W (I × I)) := by
  rw [BlocksInnerProduct, ← sum_fixedPointCount]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [fixedPointCount_conj, fixedPointCount, fixedPointCount, card_fixedBy_prod]
  push_cast
  ring

theorem card_orbits_prod_eq_two_iff {W I : Type*} [Group W] [MulAction W I] [Finite I]
    [MulAction.IsPretransitive W I] (hI : 2 ≤ Nat.card I) :
    Nat.card (MulAction.orbitRel.Quotient W (I × I)) = 2 ↔
      MulAction.IsMultiplyPretransitive W I 2 := by
  obtain ⟨a, b, hab⟩ : ∃ a b : I, a ≠ b := by
    by_contra h
    push Not at h
    have : Subsingleton I := ⟨h⟩
    have := Finite.card_le_one_iff_subsingleton.mpr this
    omega
  let q : I × I → MulAction.orbitRel.Quotient W (I × I) := Quotient.mk _
  have hdiag : ∀ x : I, q (x, x) = q (a, a) := by
    intro x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W a x
    exact Quotient.sound ⟨g, by show g • (a, a) = (x, x); rw [Prod.smul_mk, hg]⟩
  have hoff : ∀ x y : I, x ≠ y → q (x, y) ≠ q (a, a) := by
    intro x y hxy h
    obtain ⟨g, hg⟩ := Quotient.exact h
    change g • (a, a) = (x, y) at hg
    rw [Prod.smul_mk, Prod.mk.injEq] at hg
    exact hxy (by rw [← hg.1, ← hg.2])
  have hne : q (a, b) ≠ q (a, a) := hoff a b hab
  rw [MulAction.is_two_pretransitive_iff]
  constructor
  · intro h2 x y c d hxy hcd
    have hsurj : ∀ z : MulAction.orbitRel.Quotient W (I × I), z = q (a, a) ∨ z = q (a, b) := by
      by_contra hz
      push Not at hz
      obtain ⟨z, hz1, hz2⟩ := hz
      have h3 : 3 ≤ Nat.card (MulAction.orbitRel.Quotient W (I × I)) := by
        let _ : Fintype (MulAction.orbitRel.Quotient W (I × I)) := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
        have hsub : ({q (a, a), q (a, b), z} : Finset _) ⊆ Finset.univ := Finset.subset_univ _
        refine le_trans ?_ (Finset.card_le_card hsub)
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simpa using hz2.symm
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hne.symm, hz1.symm⟩
      omega
    have hxy' : q (x, y) = q (a, b) := (hsurj _).resolve_left (hoff x y hxy)
    have hcd' : q (c, d) = q (a, b) := (hsurj _).resolve_left (hoff c d hcd)
    obtain ⟨g, hg⟩ := Quotient.exact (hcd'.trans hxy'.symm)
    change g • (x, y) = (c, d) at hg
    rw [Prod.smul_mk, Prod.mk.injEq] at hg
    exact ⟨g, hg⟩
  · intro h2
    rw [Nat.card_eq_two_iff]
    refine ⟨q (a, a), q (a, b), hne.symm, Set.eq_univ_of_forall fun z => ?_⟩
    obtain ⟨⟨x, y⟩, rfl⟩ := Quotient.exists_rep z
    by_cases hxy : x = y
    · subst hxy
      exact Or.inl (hdiag x)
    · right
      obtain ⟨g, hg1, hg2⟩ := h2 hab hxy
      exact Quotient.sound ⟨g, by show g • (a, b) = (x, y); rw [Prod.smul_mk, hg1, hg2]⟩

theorem permutation_character_orbit_count (W I : Type) [Group W] [Fintype W] [MulAction W I]
    [Fintype I] [Nonempty I] :
    (permutationRepresentation W I).character = fixedPointCount W I ∧
    BlocksInnerProduct (fixedPointCount W I) 1 = Nat.card (MulAction.orbitRel.Quotient W I) ∧
    BlocksInnerProduct (fixedPointCount W I) (fixedPointCount W I) =
      Nat.card (MulAction.orbitRel.Quotient W (I × I)) ∧
    (MulAction.IsPretransitive W I → 2 ≤ Nat.card I →
      (MulAction.IsMultiplyPretransitive W I 2 ↔ fixedPointCount W I - 1 ∈ BlocksIrr W)) := by
  have hchar : (permutationRepresentation W I).character = fixedPointCount W I :=
    funext permutationRepresentation_character
  refine ⟨hchar, blocksInnerProduct_fixedPointCount_one,
    blocksInnerProduct_fixedPointCount_self, fun htrans hI => ?_⟩
  have h1 : Nat.card (MulAction.orbitRel.Quotient W I) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨Quotient.mk _ (Classical.arbitrary I)⟩⟩
    obtain ⟨i, rfl⟩ := Quotient.exists_rep x
    obtain ⟨j, rfl⟩ := Quotient.exists_rep y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W j i
    exact Quotient.sound ⟨g, hg⟩
  have hπ1 : BlocksInnerProduct (fixedPointCount W I) 1 = 1 := by
    rw [blocksInnerProduct_fixedPointCount_one, h1, Nat.cast_one]
  have h1π : BlocksInnerProduct 1 (fixedPointCount W I) = 1 := by
    rw [← hπ1, BlocksInnerProduct, BlocksInnerProduct]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [fixedPointCount_conj]
    simp
  have h11 : BlocksInnerProduct (1 : W → ℂ) 1 = 1 := by
    have hW : (Nat.card W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    simp [BlocksInnerProduct, Finset.card_univ, ← Nat.card_eq_fintype_card, hW]
  have hexpand : BlocksInnerProduct (fixedPointCount W I - 1) (fixedPointCount W I - 1) =
      BlocksInnerProduct (fixedPointCount W I) (fixedPointCount W I) - 1 := by
    have hlin : BlocksInnerProduct (fixedPointCount W I - 1) (fixedPointCount W I - 1) =
        BlocksInnerProduct (fixedPointCount W I) (fixedPointCount W I) -
          BlocksInnerProduct (fixedPointCount W I) 1 -
          BlocksInnerProduct 1 (fixedPointCount W I) + BlocksInnerProduct (1 : W → ℂ) 1 := by
      simp only [BlocksInnerProduct, Pi.sub_apply, map_sub]
      rw [← mul_sub, ← mul_sub, ← mul_add, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun w _ => ?_
      ring
    rw [hlin, hπ1, h1π, h11]
    ring
  rw [← card_orbits_prod_eq_two_iff hI]
  constructor
  ·
    intro h2
    have h2' : BlocksInnerProduct (fixedPointCount W I) (fixedPointCount W I) = 2 := by
      rw [blocksInnerProduct_fixedPointCount_self, h2]
      norm_num
    let data : FiniteComplexRepresentation W :=
      { vector := I → ℂ, representation := permutationRepresentation W I }
    obtain ⟨size, summand, hirr, hsum⟩ :=
      finiteComplexRepresentation_exists_irreducible_character_sum data
    let ψ : Fin size → W → ℂ := fun k => (summand k).character
    have hπ : fixedPointCount W I = fun w => ∑ k, (1 : ℂ) * ψ k w := by
      funext w
      simp only [one_mul, ψ]
      rw [← hsum w]
      exact (permutationRepresentation_character w).symm
    have hconv : ∀ f g : W → ℂ, (∀ w, g w⁻¹ = starRingEnd ℂ (g w)) →
        BlocksInnerProduct f g = characterPairing f g := by
      intro f g hg
      simp only [BlocksInnerProduct, characterPairing, hg]
    have hπinv : ∀ w, fixedPointCount W I w⁻¹ = starRingEnd ℂ (fixedPointCount W I w) := by
      intro w
      rw [fixedPointCount_inv, fixedPointCount_conj]
    have h1inv : ∀ w : W, (1 : W → ℂ) w⁻¹ = starRingEnd ℂ ((1 : W → ℂ) w) := by simp
    have hprin := principalFiniteComplexRepresentation_character W
    have hone : characterPairing (fixedPointCount W I) 1 =
        ((Finset.univ.filter fun k : Fin size => ψ k = 1).card : ℂ) := by
      rw [hπ, characterPairing_expansion_left, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [one_mul, ← hprin, characterPairing_irreducible _ _ (hirr k)
        (principalFiniteComplexRepresentation_isIrreducible W)]
      split_ifs <;> simp
    have hself : characterPairing (fixedPointCount W I) (fixedPointCount W I) =
        ((Finset.univ.filter fun p : Fin size × Fin size => ψ p.1 = ψ p.2).card : ℂ) := by
      rw [hπ, characterPairing_expansion_left, Finset.card_filter, Nat.cast_sum,
        ← Finset.univ_product_univ, Finset.sum_product]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [one_mul, characterPairing_expansion_right]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [one_mul, characterPairing_irreducible _ _ (hirr k) (hirr l)]
      split_ifs <;> simp
    have hcount1 : (Finset.univ.filter fun k : Fin size => ψ k = 1).card = 1 := by
      have h := hone
      rw [← hconv _ _ h1inv, hπ1] at h
      exact_mod_cast h.symm
    have hcount2 : (Finset.univ.filter fun p : Fin size × Fin size => ψ p.1 = ψ p.2).card =
        2 := by
      have h := hself
      rw [← hconv _ _ hπinv, h2'] at h
      exact_mod_cast h.symm
    have hsize : size ≤ 2 := by
      rw [← hcount2]
      have hsub : (Finset.univ.image fun k : Fin size => (k, k)) ⊆
          Finset.univ.filter fun p : Fin size × Fin size => ψ p.1 = ψ p.2 := by
        intro p hp
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp
        simp
      calc size = (Finset.univ.image fun k : Fin size => (k, k)).card := by
            rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1),
              Finset.card_univ, Fintype.card_fin]
        _ ≤ _ := Finset.card_le_card hsub
    obtain ⟨k₀, hk₀⟩ := Finset.card_eq_one.mp hcount1
    have hk₀1 : ψ k₀ = 1 := by
      have : k₀ ∈ Finset.univ.filter fun k : Fin size => ψ k = 1 := by
        rw [hk₀]
        exact Finset.mem_singleton_self k₀
      exact (Finset.mem_filter.mp this).2
    have hother : ∀ k, k ≠ k₀ → ψ k ≠ 1 := by
      intro k hk h
      have : k ∈ Finset.univ.filter fun k : Fin size => ψ k = 1 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [hk₀, Finset.mem_singleton] at this
      exact hk this
    have hπone : fixedPointCount W I 1 = Nat.card I := by
      rw [fixedPointCount, MulAction.fixedBy_one_eq_univ, Nat.card_univ]
    obtain ⟨k₁, hk₁⟩ : ∃ k₁, k₁ ≠ k₀ := by
      by_contra hall
      push Not at hall
      have huniv : (Finset.univ : Finset (Fin size)) = {k₀} :=
        Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun k _ => hall k⟩
      have hval := congrFun hπ 1
      rw [huniv, Finset.sum_singleton, one_mul, hk₀1, hπone, Pi.one_apply] at hval
      have : Nat.card I = 1 := by exact_mod_cast hval
      omega
    have huniv : (Finset.univ : Finset (Fin size)) = {k₀, k₁} := by
      symm
      refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
      rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hk₁.symm]
      exact hsize
    have hdecomp : fixedPointCount W I - 1 = ψ k₁ := by
      rw [hπ]
      funext w
      rw [Pi.sub_apply, huniv, Finset.sum_pair hk₁.symm, one_mul, one_mul, hk₀1]
      simp
    rw [hdecomp, blocksIrr_eq_irreducible_characters]
    exact ⟨summand k₁, hirr k₁, rfl⟩
  ·
    intro hirr
    have hnorm := ((irreducible_character_basis W).1 _ hirr _ hirr)
    rw [ite_eq_left rfl, hexpand] at hnorm
    have : BlocksInnerProduct (fixedPointCount W I) (fixedPointCount W I) = 2 := by
      linear_combination hnorm
    rw [blocksInnerProduct_fixedPointCount_self] at this
    exact_mod_cast this

end CFSG
