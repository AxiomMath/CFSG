module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.ColumnHelpers

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.RankTwoShapes

variable {G : Type} [Group G] [Fintype G]

@[expose] noncomputable def lyonsZeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

theorem lyonsZeta_isPrimitiveRoot : IsPrimitiveRoot lyonsZeta 5 :=
  Complex.isPrimitiveRoot_exp 5 (by norm_num)

@[expose] noncomputable def labelDegree (basis : FiniteIrreducibleCharacterBasis G)
    (χ : basis.index) : ℤ :=
  Module.finrank ℂ (basis.representation χ).vector

theorem labelDegree_cast (basis : FiniteIrreducibleCharacterBasis G) (χ : basis.index) :
    ((labelDegree basis χ : ℤ) : ℂ) = (basis.representation χ).character 1 := by
  rw [labelDegree, FiniteComplexRepresentation.character, Representation.char_one]
  push_cast; rfl

theorem labelDegree_pos (basis : FiniteIrreducibleCharacterBasis G) (χ : basis.index) :
    0 < labelDegree basis χ := by
  have h := irreducible_character_degree_ne_zero (basis.representation χ) (basis.irreducible χ)
  rw [← labelDegree_cast] at h
  have h' : labelDegree basis χ ≠ 0 := by exact_mod_cast h
  have : 0 ≤ labelDegree basis χ := by unfold labelDegree; positivity
  omega

@[expose] noncomputable def actualDt (basis : FiniteIrreducibleCharacterBasis G) (t : G)
    (χ : basis.index) : ℤ :=
  intPart ((basis.representation χ).character t)

@[expose] noncomputable def actualD (basis : FiniteIrreducibleCharacterBasis G) (z y : G)
    (i : Fin 5) (χ : basis.index) : ℤ :=
  intPart (fiveFourier (basis.representation χ).character lyonsZeta z y i)

theorem actualDt_spec (basis : FiniteIrreducibleCharacterBasis G) (t : G) (χ : basis.index)
    (h : ∃ n : ℤ, (basis.representation χ).character t = n) :
    ((actualDt basis t χ : ℤ) : ℂ) = (basis.representation χ).character t :=
  (intPart_spec h).symm

theorem actualD_spec (basis : FiniteIrreducibleCharacterBasis G) (z y : G) (i : Fin 5)
    (χ : basis.index)
    (h : ∃ n : ℤ, fiveFourier (basis.representation χ).character lyonsZeta z y i = n) :
    ((actualD basis z y i χ : ℤ) : ℂ) =
      fiveFourier (basis.representation χ).character lyonsZeta z y i :=
  (intPart_spec h).symm

end CFSG.LyonsUnitaryFour
