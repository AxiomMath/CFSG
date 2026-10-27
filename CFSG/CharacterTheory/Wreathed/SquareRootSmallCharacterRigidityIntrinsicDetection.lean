module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigiditySignedCore

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.ActualProjectiveLayer
open CFSG.Wreathed.AdaptedBaseFusion CFSG.Wreathed.ConditionalGeneralBase
open CFSG.BlockSectionOrthogonality.Helpers CFSG.Semidihedral.Principal
open scoped BigOperators Classical ComplexConjugate

variable {G : Type} [Group G] [Fintype G]

theorem actual_root_class_function_section_pairing
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (χ : G → ℂ) (hχ : BlocksIsClassFunction χ) (δ : ℂ)
    (hsection : ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
        χ (actualRoot S e ^ h * v) = δ) :
    BlocksInnerProduct χ (rootPrincipalAverageColumn n ideal (actualRoot S e)) = δ := by
  have hi := actual_root_intrinsic_integral_column n hn S e ideal
  rw [innerProduct_of_constant_on_support (squareRootSection (actualRoot S e)) χ _ δ
    hi.2.1 ((classFunction_section_value_iff hχ).mp hsection), hi.2.2.2.1, mul_one]

theorem irreducible_actual_finite_representation (χ : BlocksIrr G) :
    ∃ θ : FiniteComplexRepresentation.{0, 0} G,
      θ.character = (χ : G → ℂ) ∧ Module.finrank ℂ θ.vector = irreducibleDegree χ := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨label, hlabel⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basis χ.property
  refine ⟨basis.representation label, hlabel, ?_⟩
  have h := congrFun hlabel 1
  change (basis.representation label).representation.character 1 = (χ : G → ℂ) 1 at h
  rw [Representation.char_one, irreducibleDegree_cast] at h
  exact_mod_cast h

@[expose] def originalSectionPassingIrreducibles (y : G) : Set (BlocksIrr G) :=
  {χ | ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
    v ∈ Subgroup.centralizer ({y} : Set G) → (χ : G → ℂ) (y ^ h * v) = -1}

@[expose] def originalSectionLeastDegree (y : G) : ℕ :=
  sInf (irreducibleDegree '' originalSectionPassingIrreducibles y)

variable [IsSimpleGroup G]

theorem actual_root_intrinsic_irreducible_passing_characters
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    ∃ (A B D : BlocksIrr G) (σ τ₀ κ : ℤ),
      A ≠ B ∧ A ≠ D ∧ B ≠ D ∧
      (∀ χ ∈ ({A, B, D} : Finset (BlocksIrr G)),
        (χ : G → ℂ) ∈ BlocksPrincipalBlock ideal G ∧ (χ : G → ℂ) ≠ 1) ∧
      (σ = 1 ∨ σ = -1) ∧ (τ₀ = 1 ∨ τ₀ = -1) ∧ (κ = 1 ∨ κ = -1) ∧
      rootPrincipalAverageColumn n ideal (actualRoot S e) =
        1 + (σ : ℂ) • (A : G → ℂ) - (τ₀ : ℂ) • (B : G → ℂ) +
          (κ : ℂ) • (D : G → ℂ) ∧
      ∀ χ : BlocksIrr G,
        (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
          v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
            (χ : G → ℂ) (actualRoot S e ^ h * v) = -1) ↔
        (χ = A ∧ σ = -1) ∨ (χ = B ∧ τ₀ = 1) ∨ (χ = D ∧ κ = -1) := by
  obtain ⟨A, B, D, σ, τ₀, κ, hAB, hAD, hBD, hblock, hσ, hτ₀, hκ, hcolumn,
    hvirtual, hindicator, hsection, hdegree⟩ := actual_root_intrinsic_signed_core hnonab n hn S e
      hfour p f hp hpodd hf hmodel ideal
  refine ⟨A, B, D, σ, τ₀, κ, hAB, hAD, hBD, hblock, hσ, hτ₀, hκ, hcolumn, ?_⟩
  intro χ
  constructor
  · intro hχsection
    have hpair := actual_root_class_function_section_pairing n hn S e ideal (χ : G → ℂ)
      (irreducible_isClassFunction χ.property) (-1) hχsection
    have hχcases : χ = A ∨ χ = B ∨ χ = D := by
      by_contra hnone
      have hχA : χ ≠ A := fun h => hnone (Or.inl h)
      have hχB : χ ≠ B := fun h => hnone (Or.inr (Or.inl h))
      have hχD : χ ≠ D := fun h => hnone (Or.inr (Or.inr h))
      let P : BlocksIrr G := ⟨1, principal_mem_blocksIrr G⟩
      have hχP : χ ≠ P := by
        intro hχeq
        have heq : (χ : G → ℂ) = 1 := congrArg Subtype.val hχeq
        have hv := hχsection (1 : ℤ) 1 (by simp) (by simp) (Subgroup.one_mem _)
        rw [heq, Pi.one_apply] at hv
        norm_num at hv
      rw [hcolumn, Int.cast_smul_eq_zsmul ℂ σ, Int.cast_smul_eq_zsmul ℂ τ₀,
        Int.cast_smul_eq_zsmul ℂ κ] at hpair
      simp only [innerProduct_add_right, innerProduct_sub_right, innerProduct_zsmul_right]
        at hpair
      change BlocksInnerProduct (χ : G → ℂ) (P : G → ℂ) +
        (σ : ℂ) * BlocksInnerProduct (χ : G → ℂ) (A : G → ℂ) -
        (τ₀ : ℂ) * BlocksInnerProduct (χ : G → ℂ) (B : G → ℂ) +
        (κ : ℂ) * BlocksInnerProduct (χ : G → ℂ) (D : G → ℂ) = -1 at hpair
      simp only [blocksInnerProduct_irreducible, hχP, hχA, hχB, hχD, ite_false,
        mul_zero, add_zero, sub_zero] at hpair
      norm_num at hpair
    rcases hχcases with hχA | hχB | hχD
    · have ha := (hsection (1 : ℤ) 1 (by simp) (by simp) (Subgroup.one_mem _)).1
      rw [hχA] at hχsection
      have hv := hχsection (1 : ℤ) 1 (by simp) (by simp) (Subgroup.one_mem _)
      have hs : σ = -1 := by exact_mod_cast ha.symm.trans hv
      exact Or.inl ⟨hχA, hs⟩
    · have hb := (hsection (1 : ℤ) 1 (by simp) (by simp) (Subgroup.one_mem _)).2.1
      rw [hχB] at hχsection
      have hv := hχsection (1 : ℤ) 1 (by simp) (by simp) (Subgroup.one_mem _)
      have hs : τ₀ = 1 := by
        have ht : (-τ₀ : ℂ) = -1 := hb.symm.trans hv
        exact_mod_cast (neg_inj.mp ht)
      exact Or.inr (Or.inl ⟨hχB, hs⟩)
    · have hd := (hsection (1 : ℤ) 1 (by simp) (by simp) (Subgroup.one_mem _)).2.2
      rw [hχD] at hχsection
      have hv := hχsection (1 : ℤ) 1 (by simp) (by simp) (Subgroup.one_mem _)
      have hs : κ = -1 := by exact_mod_cast hd.symm.trans hv
      exact Or.inr (Or.inr ⟨hχD, hs⟩)
  · rintro (⟨hχA, hσneg⟩ | ⟨hχB, hτpos⟩ | ⟨hχD, hκneg⟩) h v hh hv hc
    · simpa only [hχA, hσneg, Int.cast_neg, Int.cast_one] using (hsection h v hh hv hc).1
    · simpa only [hχB, hτpos, Int.cast_one] using (hsection h v hh hv hc).2.1
    · simpa only [hχD, hκneg, Int.cast_neg, Int.cast_one] using (hsection h v hh hv hc).2.2

theorem actual_root_canonical_least_passing_character
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    0 < originalSectionLeastDegree (actualRoot S e) ∧
      (∃ β : BlocksIrr G, β ∈ originalSectionPassingIrreducibles (actualRoot S e) ∧
        (β : G → ℂ) ∈ BlocksPrincipalBlock ideal G ∧ (β : G → ℂ) ≠ 1 ∧
        irreducibleDegree β = originalSectionLeastDegree (actualRoot S e)) ∧
      (∀ χ : BlocksIrr G, χ ∈ originalSectionPassingIrreducibles (actualRoot S e) →
        originalSectionLeastDegree (actualRoot S e) ≤ irreducibleDegree χ) ∧
      ∀ θ : FiniteComplexRepresentation.{0, 0} G,
        (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
          v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
            θ.character (actualRoot S e ^ h * v) = -1) →
        originalSectionLeastDegree (actualRoot S e) ≤ Module.finrank ℂ θ.vector ∧
          (Module.finrank ℂ θ.vector ≤ originalSectionLeastDegree (actualRoot S e) →
            θ.character ∈ BlocksIrr G ∧ θ.character ∈ BlocksPrincipalBlock ideal G ∧
              θ.character ≠ 1 ∧
              Module.finrank ℂ θ.vector = originalSectionLeastDegree (actualRoot S e)) := by
  obtain ⟨d, β, hd, hβdegree, hβblock, hβnontrivial, hβsection, hfloor, htest⟩ :=
    actual_root_intrinsic_least_passing_character hnonab n hn S e hfour p f hp hpodd hf hmodel
      ideal
  obtain ⟨A, B, D, σ, τ₀, κ, hAB, hAD, hBD, hblock, hσ, hτ₀, hκ, hcolumn, hpassing⟩ :=
    actual_root_intrinsic_irreducible_passing_characters hnonab n hn S e hfour p f hp hpodd hf
      hmodel ideal
  have hβmem : β ∈ originalSectionPassingIrreducibles (actualRoot S e) := hβsection
  have hdegree_nonempty :
      (irreducibleDegree '' originalSectionPassingIrreducibles (actualRoot S e)).Nonempty :=
    ⟨irreducibleDegree β, β, hβmem, rfl⟩
  have hminmem := Nat.sInf_mem hdegree_nonempty
  change originalSectionLeastDegree (actualRoot S e) ∈
    irreducibleDegree '' originalSectionPassingIrreducibles (actualRoot S e) at hminmem
  obtain ⟨χ, hχmem, hχdegree⟩ := hminmem
  have hχblock : (χ : G → ℂ) ∈ BlocksPrincipalBlock ideal G := by
    rcases (hpassing χ).mp hχmem with ⟨hχA, hs⟩ | ⟨hχB, ht⟩ | ⟨hχD, hk⟩
    · rw [hχA]; exact (hblock A (by simp)).1
    · rw [hχB]; exact (hblock B (by simp)).1
    · rw [hχD]; exact (hblock D (by simp)).1
  have hχavg := root_character_average_of_constant_section n S e (χ : G → ℂ) (-1) hχmem
  have hmin_ge := hfloor χ hχblock ⟨-1, by omega, by simpa using hχavg⟩
  rw [hχdegree] at hmin_ge
  have hmin_le : originalSectionLeastDegree (actualRoot S e) ≤ d := by
    rw [← hβdegree]
    exact Nat.sInf_le ⟨β, hβmem, rfl⟩
  have hminimum : originalSectionLeastDegree (actualRoot S e) = d :=
    Nat.le_antisymm hmin_le hmin_ge
  refine ⟨by rwa [hminimum], ⟨β, hβmem, hβblock, hβnontrivial, by rw [hminimum, hβdegree]⟩,
    fun χ hχ => Nat.sInf_le ⟨χ, hχ, rfl⟩, ?_⟩
  intro θ hθsection
  have hθfloor : d ≤ Module.finrank ℂ θ.vector := by
    by_contra h
    have hθ := htest θ (by omega) hθsection
    omega
  refine ⟨by rwa [hminimum], ?_⟩
  intro hθdegree
  rw [hminimum] at hθdegree ⊢
  exact htest θ hθdegree hθsection

theorem actual_root_passing_irreducible_in_every_principal_block
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (χ : BlocksIrr G) (hχ : χ ∈ originalSectionPassingIrreducibles (actualRoot S e))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    (χ : G → ℂ) ∈ BlocksPrincipalBlock ideal G ∧ (χ : G → ℂ) ≠ 1 := by
  obtain ⟨A, B, D, σ, τ₀, κ, hAB, hAD, hBD, hblock, hσ, hτ₀, hκ, hcolumn, hpassing⟩ :=
    actual_root_intrinsic_irreducible_passing_characters hnonab n hn S e hfour p f hp hpodd hf
      hmodel ideal
  rcases (hpassing χ).mp hχ with ⟨hχA, hs⟩ | ⟨hχB, ht⟩ | ⟨hχD, hk⟩
  · rw [hχA]; exact hblock A (by simp)
  · rw [hχB]; exact hblock B (by simp)
  · rw [hχD]; exact hblock D (by simp)

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
