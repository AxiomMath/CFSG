module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PolynomialCoefficients
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PolynomialProjectors
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Blocks
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralIntegrality
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Spectral

public section

open CFSG
open scoped Classical

namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem residueFiber_admissible (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] (coefficients : G → ℂ)
    (hcoefficients : BlocksIsCentralR m coefficients) (base : ℂ) :
    BlocksAdmissible m G {character | character ∈ BlocksIrr G ∧
      BlocksCentralChar character coefficients - base ∈ BlocksLocalMaxIdeal m} := by
  classical
  let : Finite (BlocksIrr G) := (irr_linearIndependent G).finite
  let : Fintype (BlocksIrr G) := Fintype.ofFinite (BlocksIrr G)
  let eigenvalues : BlocksIrr G → localCoefficientSubring m hm := fun character =>
    ⟨BlocksCentralChar character.val coefficients,
      centralChar_localRing m hm character.property hcoefficients⟩
  let selected : Set (BlocksIrr G) := {character |
    BlocksCentralChar character.val coefficients - base ∈ BlocksLocalMaxIdeal m}
  have hseparated : ∀ left ∈ selected, ∀ right ∉ selected,
      IsUnit (eigenvalues left - eigenvalues right) := by
    intro left hleft right hright
    apply localRing_isUnit_of_not_mem m hm
    intro hdifference
    have hnegative : BlocksCentralChar right.val coefficients -
        BlocksCentralChar left.val coefficients ∈ BlocksLocalMaxIdeal m := by
      convert localMaxIdeal_neg m hdifference using 1
      change BlocksCentralChar right.val coefficients - BlocksCentralChar left.val coefficients =
        -(BlocksCentralChar left.val coefficients - BlocksCentralChar right.val coefficients)
      ring
    exact hright (localMaxIdeal_trans m hm hnegative hleft)
  obtain ⟨projector, hprojector⟩ := exists_polynomial_projector eigenvalues selected hseparated
  let fiber : Set (G → ℂ) := {character | character ∈ BlocksIrr G ∧
    BlocksCentralChar character coefficients - base ∈ BlocksLocalMaxIdeal m}
  have hfiber : fiber ⊆ BlocksIrr G := fun _ hmember => hmember.1
  have hscalar (character : G → ℂ) (hcharacter : character ∈ BlocksIrr G) :
      BlocksCentralChar character (polynomialCoefficients m hm coefficients projector) =
        if character ∈ fiber then 1 else 0 := by
    rw [centralChar_polynomialCoefficients m hm hcharacter hcoefficients]
    change Polynomial.eval₂ (localCoefficientSubring m hm).subtype
      ((localCoefficientSubring m hm).subtype (eigenvalues ⟨character, hcharacter⟩)) projector = _
    rw [Polynomial.eval₂_at_apply, hprojector]
    by_cases hmember : BlocksCentralChar character coefficients - base ∈ BlocksLocalMaxIdeal m
    · simp only [selected, fiber, Set.mem_ofPred_eq, hmember, hcharacter, and_self,
        ↓reduceIte, map_one]
    · simp only [selected, fiber, Set.mem_ofPred_eq, hmember, hcharacter, and_false,
        ↓reduceIte, map_zero]
  have hidentity : polynomialCoefficients m hm coefficients projector =
      BlocksIdempotentCoeff G fiber := by
    apply sub_eq_zero.mp
    apply centralChar_separates G
    · intro element conjugator
      simp only [Pi.sub_apply,
        (polynomialCoefficients_central m hm hcoefficients projector).2 element conjugator,
        idempotentCoeff_conj hfiber]
    · intro character hcharacter
      rw [centralChar_sub, hscalar character hcharacter,
        centralChar_idempotentCoeff hfiber hcharacter]
      by_cases hmember : character ∈ fiber <;> simp only [hmember, ↓reduceIte, sub_self]
  refine ⟨hfiber, ?_⟩
  intro element
  rw [← hidentity]
  exact (polynomialCoefficients_central m hm hcoefficients projector).1 element

theorem sameBlock_centralChar_congr (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] {left right : G → ℂ}
    (hleft : left ∈ BlocksIrr G) (hright : right ∈ BlocksBlockOf m G left)
    {coefficients : G → ℂ} (hcoefficients : BlocksIsCentralR m coefficients) :
    BlocksCentralChar right coefficients - BlocksCentralChar left coefficients ∈
      BlocksLocalMaxIdeal m := by
  let fiber : Set (G → ℂ) := {character | character ∈ BlocksIrr G ∧
    BlocksCentralChar character coefficients - BlocksCentralChar left coefficients ∈
      BlocksLocalMaxIdeal m}
  have hfiber : BlocksAdmissible m G fiber :=
    residueFiber_admissible m hm G coefficients hcoefficients _
  have hleftMember : left ∈ fiber :=
    ⟨hleft, by simpa only [sub_self] using localMaxIdeal_zero m hm⟩
  exact ((hright.2 fiber hfiber).mp hleftMember).2

theorem principal_centralChar_congr (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] {character : G → ℂ}
    (hcharacter : character ∈ BlocksPrincipalBlock m G)
    {coefficients : G → ℂ} (hcoefficients : BlocksIsCentralR m coefficients) :
    BlocksCentralChar character coefficients - BlocksCentralChar (fun _ => 1) coefficients ∈
      BlocksLocalMaxIdeal m := by
  exact sameBlock_centralChar_congr m hm G (trivial_mem_irr G) hcharacter hcoefficients

theorem block_centralChar_congr (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] {block : Set (G → ℂ)}
    (hblock : BlocksIsBlock m G block) {left right : G → ℂ}
    (hleft : left ∈ block) (hright : right ∈ block)
    {coefficients : G → ℂ} (hcoefficients : BlocksIsCentralR m coefficients) :
    BlocksCentralChar right coefficients - BlocksCentralChar left coefficients ∈
      BlocksLocalMaxIdeal m := by
  rw [block_eq_blockOf_member m hblock hleft] at hright
  exact sameBlock_centralChar_congr m hm G (block_subset_irr m hblock hleft) hright hcoefficients

theorem mem_blockOf_of_centralChar_congr (m : Ideal BlocksAlgInt) (_hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] {left right : G → ℂ}
    (hleft : left ∈ BlocksIrr G) (hright : right ∈ BlocksIrr G)
    (hcongr : ∀ coefficients : G → ℂ, BlocksIsCentralR m coefficients →
      BlocksCentralChar right coefficients - BlocksCentralChar left coefficients ∈
        BlocksLocalMaxIdeal m) : right ∈ BlocksBlockOf m G left := by
  classical
  refine ⟨hright, ?_⟩
  intro admissible hadmissible
  have hcentral : BlocksIsCentralR m (BlocksIdempotentCoeff G admissible) :=
    ⟨hadmissible.2, idempotentCoeff_conj hadmissible.1⟩
  have hscalar := hcongr (BlocksIdempotentCoeff G admissible) hcentral
  rw [centralChar_idempotentCoeff hadmissible.1 hright,
    centralChar_idempotentCoeff hadmissible.1 hleft] at hscalar
  by_cases hleftMember : left ∈ admissible <;>
    by_cases hrightMember : right ∈ admissible
  · exact iff_of_true hleftMember hrightMember
  · have hnegative : (-1 : ℂ) ∈ BlocksLocalMaxIdeal m := by
      simpa only [hleftMember, hrightMember, ↓reduceIte, zero_sub] using hscalar
    have hone := localMaxIdeal_neg m hnegative
    simp only [neg_neg] at hone
    exact (localMaxIdeal_one_not m hone).elim
  · have hone : (1 : ℂ) ∈ BlocksLocalMaxIdeal m := by
      simpa only [hleftMember, hrightMember, ↓reduceIte, sub_zero] using hscalar
    exact (localMaxIdeal_one_not m hone).elim
  · exact iff_of_false hleftMember hrightMember

end CFSG.BrauerThirdMainTheorem.Helpers
