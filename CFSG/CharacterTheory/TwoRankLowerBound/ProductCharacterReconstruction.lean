module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterInflation
public import CFSG.CharacterTheory.TwoRankLowerBound.ProductCharacterSlice
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasis

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem virtualCharacter_conjugation_invariant {G : Type*} [Group G]
    (function : G → ℂ) (hvirtual : function ∈ virtualCharacters G) (element conjugator : G) :
    function (conjugator * element * conjugator⁻¹) = function element := by
  induction hvirtual using Submodule.span_induction with
  | mem character hmember =>
    obtain ⟨data, rfl⟩ := hmember
    exact Representation.char_conj data.representation element conjugator
  | zero => rfl
  | add left right _ _ hleft hright =>
    simp only [Pi.add_apply, hleft, hright]
  | smul scalar function _ hequal =>
    simp only [Pi.smul_apply, hequal]

theorem virtualCharacters_mul {G : Type*} [Group G]
    (left right : G → ℂ) (hleft : left ∈ virtualCharacters G) (hright : right ∈ virtualCharacters G) :
    left * right ∈ virtualCharacters G := by
  induction hleft using Submodule.span_induction with
  | mem character hmember =>
    obtain ⟨data, rfl⟩ := hmember
    induction hright using Submodule.span_induction with
    | mem otherCharacter hother =>
      obtain ⟨other, rfl⟩ := hother
      have hcharacter : data.character * other.character =
          (data.representation.tprod other.representation).character :=
        (Representation.char_tensor _ _).symm
      rw [hcharacter]
      exact character_mem_virtualCharacters
        { vector := TensorProduct ℂ data.vector other.vector
          representation := data.representation.tprod other.representation }
    | zero => simpa only [mul_zero] using (virtualCharacters G).zero_mem
    | add first second _ _ hfirst hsecond =>
      rw [mul_add]
      exact (virtualCharacters G).add_mem hfirst hsecond
    | smul scalar function _ hfunction =>
      rw [mul_smul_comm]
      exact (virtualCharacters G).smul_mem scalar hfunction
  | zero => simpa only [zero_mul] using (virtualCharacters G).zero_mem
  | add first second _ _ hfirst hsecond =>
    rw [add_mul]
    exact (virtualCharacters G).add_mem hfirst hsecond
  | smul scalar function _ hfunction =>
    rw [smul_mul_assoc]
    exact (virtualCharacters G).smul_mem scalar hfunction

theorem externalProduct_virtual {left right : Type} [Group left] [Group right]
    (leftFunction : left → ℂ) (rightFunction : right → ℂ)
    (hleft : leftFunction ∈ virtualCharacters left) (hright : rightFunction ∈ virtualCharacters right) :
    (fun element : left × right => leftFunction element.1 * rightFunction element.2) ∈
      virtualCharacters (left × right) := by
  exact virtualCharacters_mul (leftFunction ∘ MonoidHom.fst left right)
    (rightFunction ∘ MonoidHom.snd left right)
    (inflation_mem_virtualCharacters _ hleft) (inflation_mem_virtualCharacters _ hright)

theorem productCharacterSlice_reconstruction {left right : Type} [Group left] [Group right]
    [Fintype right] (basis : FiniteIrreducibleCharacterBasis right)
    (function : left × right → ℂ)
    (hclass : ∀ element conjugator : left × right,
      function (conjugator * element * conjugator⁻¹) = function element)
    (leftElement : left) (rightElement : right) :
    function (leftElement, rightElement) =
      ∑ label, productCharacterSlice (basis.representation label).character function leftElement *
        (basis.representation label).character rightElement := by
  apply finiteIrreducibleCharacterBasis_reconstruction basis (fun member => function (leftElement, member))
  intro member conjugator
  have hequal := hclass (leftElement, member) (1, conjugator)
  simpa only [Prod.mul_def, Prod.inv_mk, inv_one, one_mul, mul_one] using hequal

theorem productCharacterSlice_virtual_reconstruction {left right : Type} [Group left] [Group right]
    [Fintype right] (basis : FiniteIrreducibleCharacterBasis right)
    (function : left × right → ℂ) (hvirtual : function ∈ virtualCharacters (left × right))
    (leftElement : left) (rightElement : right) :
    function (leftElement, rightElement) =
      ∑ label, productCharacterSlice (basis.representation label).character function leftElement *
        (basis.representation label).character rightElement :=
  productCharacterSlice_reconstruction basis function
    (virtualCharacter_conjugation_invariant function hvirtual) leftElement rightElement

theorem virtual_of_virtual_product_slices {left right : Type} [Group left] [Group right]
    [Fintype right] (basis : FiniteIrreducibleCharacterBasis right)
    (function : left × right → ℂ)
    (hclass : ∀ element conjugator : left × right,
      function (conjugator * element * conjugator⁻¹) = function element)
    (hslices : ∀ label, productCharacterSlice (basis.representation label).character function ∈
      virtualCharacters left) : function ∈ virtualCharacters (left × right) := by
  have hequal : function = fun element =>
      ∑ label, productCharacterSlice (basis.representation label).character function element.1 *
        (basis.representation label).character element.2 := by
    funext element
    exact productCharacterSlice_reconstruction basis function hclass element.1 element.2
  rw [hequal]
  have hsum : (fun element : left × right =>
      ∑ label, productCharacterSlice (basis.representation label).character function element.1 *
        (basis.representation label).character element.2) =
      ∑ label, fun element : left × right =>
        productCharacterSlice (basis.representation label).character function element.1 *
          (basis.representation label).character element.2 := by
    funext element
    simp only [Finset.sum_apply]
  rw [hsum]
  apply Submodule.sum_mem
  intro label _
  exact externalProduct_virtual _ _ (hslices label) (character_mem_virtualCharacters _)

end CFSG.TwoRankLowerBound.Helpers
