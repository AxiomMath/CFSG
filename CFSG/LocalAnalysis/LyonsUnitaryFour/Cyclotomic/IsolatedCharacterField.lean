module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.GaloisBlockStability

public section

namespace CFSG.LyonsUnitaryFour

open IntermediateField CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)

theorem character_mem_of_isolated_principal_block (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] {N : ℕ} [NeZero N] (hGN : Nat.card G ∣ N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (F : IntermediateField ℚ ℂ) (hF : F ≤ ℚ⟮ζ⟯)
    {principal a : basis.index} (hprincipal : (basis.representation principal).character = 1)
    (ha : a ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) (X : Set G)
    (hX : ∀ x ∈ X, (basis.representation a).character x ∈ F)
    (hiso : ∀ b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (∀ x ∈ X, (basis.representation b).character x = (basis.representation a).character x) →
        b = a)
    (g : G) : (basis.representation a).character g ∈ F := by
  have : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := isCyclotomicExtension_adjoin_primitiveRoot hζ
  have : NumberField ℚ⟮ζ⟯ := IsCyclotomicExtension.numberField {N} ℚ ℚ⟮ζ⟯
  have : IsGalois ℚ ℚ⟮ζ⟯ := IsCyclotomicExtension.isGalois {N} ℚ ℚ⟮ζ⟯
  have hgN : ∀ g : G, g ^ N = 1 := fun g =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard g).trans hGN)
  set F' : IntermediateField ℚ ℚ⟮ζ⟯ := IntermediateField.restrict hF
  suffices hmem : (⟨(basis.representation a).character g,
      character_mem_adjoin hζ _ (hgN g)⟩ : ℚ⟮ζ⟯) ∈ F' from
    (IntermediateField.mem_restrict hF _).mp hmem
  rw [← IsGalois.fixedField_fixingSubgroup F', IntermediateField.mem_fixedField_iff]
  intro σ hσF
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσF
  obtain ⟨k, hk, hσ⟩ := exists_galois_gen_eq_pow_coprime hζ σ
  obtain ⟨π, -, hσπ, -, -, -, -, hprinBlock⟩ := galois_block_stability basis ideal hGN hζ hk hσ
  have hπa : π a = a := by
    apply hiso (π a) ((hprinBlock principal a hprincipal).mpr ha)
    intro x hx
    obtain ⟨h, hval⟩ := hσπ a x
    rw [← hval]
    have hxF' : (⟨(basis.representation a).character x, h⟩ : ℚ⟮ζ⟯) ∈ F' :=
      (IntermediateField.mem_restrict hF _).mpr (hX x hx)
    rw [hσF _ hxF']
  obtain ⟨h, hval⟩ := hσπ a g
  rw [hπa] at hval
  exact Subtype.ext hval

theorem character_rat_of_isolated_principal_block (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] {principal a : basis.index}
    (hprincipal : (basis.representation principal).character = 1)
    (ha : a ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) (X : Set G)
    (hX : ∀ x ∈ X, ∃ q : ℚ, (basis.representation a).character x = q)
    (hiso : ∀ b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (∀ x ∈ X, (basis.representation b).character x = (basis.representation a).character x) →
        b = a)
    (g : G) : ∃ q : ℚ, (basis.representation a).character g = q := by
  have hN : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card G) Nat.card_pos.ne'
  have hmem := character_mem_of_isolated_principal_block basis ideal (dvd_refl _) hζ ⊥ bot_le
    hprincipal ha X (fun x hx => by
      obtain ⟨q, hq⟩ := hX x hx
      rw [hq]
      exact IntermediateField.algebraMap_mem _ q) hiso g
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hmem
  exact ⟨q, hq.symm⟩

theorem character_mem_adjoin_of_isolated_principal_block (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] {N : ℕ} (hN : 0 < N) (hGN : Nat.card G ∣ N) {ξ : ℂ} (hξ : ξ ^ N = 1)
    {principal a : basis.index} (hprincipal : (basis.representation principal).character = 1)
    (ha : a ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) (X : Set G)
    (hX : ∀ x ∈ X, (basis.representation a).character x ∈ ℚ⟮ξ⟯)
    (hiso : ∀ b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (∀ x ∈ X, (basis.representation b).character x = (basis.representation a).character x) →
        b = a)
    (g : G) : (basis.representation a).character g ∈ ℚ⟮ξ⟯ := by
  have : NeZero N := ⟨hN.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp N hN.ne'
  have hle : ℚ⟮ξ⟯ ≤ ℚ⟮Complex.exp (2 * Real.pi * Complex.I / N)⟯ :=
    IntermediateField.adjoin_simple_le_iff.mpr (mem_adjoin_of_pow_eq_one hζ hξ)
  exact character_mem_of_isolated_principal_block basis ideal hGN hζ ℚ⟮ξ⟯ hle hprincipal ha X hX
    hiso g

end CFSG.LyonsUnitaryFour
