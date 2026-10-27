module

public import CFSG.CharacterTheory.BlockBasics.LocalRing
public import CFSG.CharacterTheory.Blocks.CharacterCriterion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.DefectDefinitions
public import CFSG.CharacterTheory.TwoRankLowerBound.BlockDefectExistence
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock

public section

open scoped Classical

namespace CFSG.BlockBasics

open CFSG CFSG.TwoRankLowerBound.Helpers

section LocalRing

variable (m : Ideal BlocksAlgInt) [hm : m.IsMaximal]

theorem mem_localizedComplexIntegerRing_iff (x : ℂ) :
    x ∈ localizedComplexIntegerRing m ↔ x ∈ BlocksLocalRing m := by
  rw [← localCoefficientSubring_eq_localized]
  rfl

theorem localizedComplexIntegerResidue_eq_zero_iff (x : localizedComplexIntegerRing m) :
    localizedComplexIntegerResidue m x = 0 ↔ (x : ℂ) ∈ BlocksLocalMaxIdeal m := by
  obtain ⟨a, b, hb, hx⟩ := (localizedComplexIntegerRing_mem_iff_fraction m x).mp x.property
  have hsymm : (localizedComplexIntegerEquiv m).symm x =
      IsLocalization.mk' (Localization.AtPrime m) a (⟨b, hb⟩ : m.primeCompl) := by
    rw [RingEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [hx]
    exact (localizedAlgebraicIntegerEmbedding_fraction m a ⟨b, hb⟩).symm
  change localizedAlgebraicIntegerResidue m ((localizedComplexIntegerEquiv m).symm x) = 0 ↔ _
  rw [hsymm, localizedAlgebraicIntegerResidue_fraction_zero_iff, hx]
  exact (CFSG.BlockBasics.fraction_mem_localMaxIdeal_iff m hm a b hb).symm

end LocalRing

section Blocks

variable {G : Type} [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)

theorem basis_character_mem_irr (l : basis.index) :
    (basis.representation l).character ∈ BlocksIrr G := by
  rw [blocksIrr_eq_irreducible_characters]
  exact ⟨basis.representation l, basis.irreducible l, rfl⟩

theorem exists_label_of_mem_irr {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    ∃ l : basis.index, (basis.representation l).character = χ := by
  rw [blocksIrr_eq_irreducible_characters] at hχ
  obtain ⟨data, hirr, rfl⟩ := hχ
  exact finiteIrreducibleCharacterBasis_contains_irreducible basis data hirr

theorem irr_eq_range_basis :
    BlocksIrr G = Set.range fun l : basis.index => (basis.representation l).character := by
  ext χ
  constructor
  · intro hχ
    exact exists_label_of_mem_irr basis hχ
  · rintro ⟨l, rfl⟩
    exact basis_character_mem_irr basis l

theorem characterSubsetIdempotent_coeff (S : Finset basis.index) (g : G) :
    (characterSubsetIdempotent basis S).coeff g =
      BlocksIdempotentCoeff G ((fun l => (basis.representation l).character) '' (S : Set _)) g := by
  have hinj : Set.InjOn (fun l => (basis.representation l).character) (S : Set basis.index) :=
    fun _ _ _ _ h => basis.distinct h
  unfold BlocksIdempotentCoeff
  rw [finsum_mem_image hinj, finsum_mem_coe_finset]
  simp only [characterSubsetIdempotent, characterIdempotentExpansion, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    complexCharacterIdempotent_coeff, smul_eq_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem characterSubsetAdmissible_iff (m : Ideal BlocksAlgInt) [m.IsMaximal]
    (S : Finset basis.index) :
    characterSubsetAdmissible basis (localizedComplexIntegerRing m) S ↔
      BlocksAdmissible m G ((fun l => (basis.representation l).character) '' (S : Set _)) := by
  have hsub : (fun l => (basis.representation l).character) '' (S : Set basis.index) ⊆
      BlocksIrr G := by
    rintro _ ⟨l, -, rfl⟩
    exact basis_character_mem_irr basis l
  change (∀ g, (characterSubsetIdempotent basis S).coeff g ∈ localizedComplexIntegerRing m) ↔ _
  simp only [characterSubsetIdempotent_coeff, mem_localizedComplexIntegerRing_iff]
  exact ⟨fun h => ⟨hsub, h⟩, fun h => h.2⟩

theorem image_filter_eq {A : Set (G → ℂ)} (hA : A ⊆ BlocksIrr G) :
    (fun l => (basis.representation l).character) ''
      ((Finset.univ.filter fun l => (basis.representation l).character ∈ A : Finset _) : Set _) =
      A := by
  ext χ
  constructor
  · rintro ⟨l, hl, rfl⟩
    simpa using hl
  · intro hχ
    obtain ⟨l, rfl⟩ := exists_label_of_mem_irr basis (hA hχ)
    exact ⟨l, by simpa using hχ, rfl⟩

theorem sameCoefficientBlock_iff (m : Ideal BlocksAlgInt) [m.IsMaximal] (l l' : basis.index) :
    sameCoefficientBlock basis (localizedComplexIntegerRing m) l l' ↔
      (basis.representation l').character ∈
        BlocksBlockOf m G (basis.representation l).character := by
  constructor
  · intro h
    refine ⟨basis_character_mem_irr basis l', fun A hA => ?_⟩
    have hS := (characterSubsetAdmissible_iff basis m
      (Finset.univ.filter fun l => (basis.representation l).character ∈ A)).mpr
      (by rw [image_filter_eq basis hA.1]; exact hA)
    have := h _ hS
    simpa using this
  · intro h S hS
    have hA := (characterSubsetAdmissible_iff basis m S).mp hS
    have hiff := h.2 _ hA
    constructor
    · intro hl
      obtain ⟨l'', hl'', heq⟩ := hiff.mp ⟨l, hl, rfl⟩
      rwa [basis.distinct heq] at hl''
    · intro hl'
      obtain ⟨l'', hl'', heq⟩ := hiff.mpr ⟨l', hl', rfl⟩
      rwa [basis.distinct heq] at hl''

theorem coefficientBlock_image (m : Ideal BlocksAlgInt) [m.IsMaximal] (l : basis.index) :
    (fun l => (basis.representation l).character) ''
        ((coefficientBlock basis (localizedComplexIntegerRing m) l : Finset _) : Set _) =
      BlocksBlockOf m G (basis.representation l).character := by
  ext χ
  constructor
  · rintro ⟨l', hl', rfl⟩
    exact (sameCoefficientBlock_iff basis m l l').mp
      ((coefficientBlock_mem_iff basis _ l l').mp hl')
  · intro hχ
    obtain ⟨l', rfl⟩ := exists_label_of_mem_irr basis hχ.1
    exact ⟨l', (coefficientBlock_mem_iff basis _ l l').mpr
      ((sameCoefficientBlock_iff basis m l l').mpr hχ), rfl⟩

theorem centralCharacterScalar_eq (z : MonoidAlgebra ℂ G) (l : basis.index) :
    centralCharacterScalar basis z l =
      BlocksCentralChar (basis.representation l).character (fun g => z.coeff g) := by
  have hcard : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold centralCharacterScalar characterPairing BlocksCentralChar
  rw [finsum_eq_sum_of_fintype, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => by simp

theorem centralCharacterResidueHom_eq_zero_iff (m : Ideal BlocksAlgInt) [m.IsMaximal]
    (z : centralCoefficientSubring (G := G) (localizedComplexIntegerRing m)) (l : basis.index) :
    centralCharacterResidueHom basis m l z = 0 ↔
      BlocksCentralChar (basis.representation l).character (fun g => z.val.coeff g) ∈
        BlocksLocalMaxIdeal m := by
  change localizedComplexIntegerResidue m (localCentralCharacterHom basis m l z) = 0 ↔ _
  rw [localizedComplexIntegerResidue_eq_zero_iff, localCentralCharacterHom_coe,
    centralCharacterScalar_eq]

theorem centralCharacterResidueHom_eq_iff (m : Ideal BlocksAlgInt) [m.IsMaximal]
    (l l' : basis.index) :
    centralCharacterResidueHom basis m l = centralCharacterResidueHom basis m l' ↔
      (basis.representation l').character ∈
        BlocksBlockOf m G (basis.representation l).character := by
  rw [← sameCoefficientBlock_iff_centralCharacterResidueHom_eq, sameCoefficientBlock_iff]

end Blocks

section Defects

variable {G : Type} [Group G]

theorem classDefect_iff (p : ℕ) (C : ConjClasses G) (D : Subgroup G) :
    CFSG.TwoRankLowerBound.Helpers.classDefect p C D ↔
      CFSG.BrauerThirdMainTheorem.Helpers.classDefect p C D := by
  constructor
  · rintro ⟨x, hx, P, hP⟩
    exact ⟨x, hx, P, hP.symm⟩
  · rintro ⟨x, hx, P, hP⟩
    exact ⟨x, hx, P, hP.symm⟩

theorem subgroupSubconjugate_iff (D E : Subgroup G) :
    CFSG.TwoRankLowerBound.Helpers.subgroupSubconjugate D E ↔
      CFSG.BrauerThirdMainTheorem.Helpers.subgroupSubconjugate D E :=
  Iff.rfl

variable [Fintype G]

theorem centralConjugacyClassSum_coeff (ring : Subring ℂ) (C : ConjClasses G) (g : G) :
    (centralConjugacyClassSum ring C).val.coeff g =
      CFSG.BrauerThirdMainTheorem.Helpers.classCoefficients C g := by
  change (conjugacyClassSum C).coeff g = _
  rw [conjugacyClassSum_coeff]
  simp only [CFSG.BrauerThirdMainTheorem.Helpers.classCoefficients]
  by_cases h : ConjClasses.mk g = C <;> simp [h]

theorem coefficientBlockDefect_iff (basis : FiniteIrreducibleCharacterBasis G)
    (m : Ideal BlocksAlgInt) [m.IsMaximal] (p : ℕ) (l : basis.index) (D : Subgroup G) :
    coefficientBlockDefect basis m p l D ↔
      CFSG.BrauerThirdMainTheorem.Helpers.blockDefect p m (basis.representation l).character D := by
  have hres : ∀ C : ConjClasses G,
      centralCharacterResidueHom basis m l (centralConjugacyClassSum _ C) ≠ 0 ↔
        BlocksCentralChar (basis.representation l).character
            (CFSG.BrauerThirdMainTheorem.Helpers.classCoefficients C) ∉ BlocksLocalMaxIdeal m := by
    intro C
    rw [Ne, centralCharacterResidueHom_eq_zero_iff]
    have hcoeff :
        (fun g => (centralConjugacyClassSum (localizedComplexIntegerRing m) C).val.coeff g) =
          CFSG.BrauerThirdMainTheorem.Helpers.classCoefficients C := by
      funext g
      exact centralConjugacyClassSum_coeff _ C g
    rw [hcoeff]
  constructor
  · rintro ⟨⟨C, hC, hCres⟩, huniv⟩
    refine ⟨⟨C, (classDefect_iff p C D).mp hC, (hres C).mp hCres⟩, fun E hE Q hQ => ?_⟩
    exact huniv E Q ((classDefect_iff p E Q).mpr hQ) ((hres E).mpr hE)
  · rintro ⟨⟨C, hC, hCres⟩, huniv⟩
    refine ⟨⟨C, (classDefect_iff p C D).mpr hC, (hres C).mpr hCres⟩, fun E Q hQ hE => ?_⟩
    exact huniv E ((hres E).mp hE) Q ((classDefect_iff p E Q).mp hQ)

end Defects

end CFSG.BlockBasics
