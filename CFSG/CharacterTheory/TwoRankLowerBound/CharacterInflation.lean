module

public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualCharacters

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem sum_comp_surjective_group_hom {source target : Type*} [Group source] [Group target]
    [Fintype source] [Fintype target] (homomorphism : source →* target)
    (hsurjective : Function.Surjective homomorphism) (function : target → ℂ) :
    (∑ element : source, function (homomorphism element)) =
      (Nat.card homomorphism.ker : ℂ) * ∑ element : target, function element := by
  have hcard : ∀ element : target,
      (Finset.univ.filter (fun member : source => homomorphism member = element)).card =
        Nat.card homomorphism.ker := by
    intro element
    have hequal := MonoidHom.card_fiber_eq_of_mem_range homomorphism
      (hsurjective element) (show (1 : target) ∈ Set.range homomorphism from ⟨1, map_one _⟩)
    have hkernel : Finset.univ.filter (fun member : source => homomorphism member = 1) =
        Finset.univ.filter (fun member : source => member ∈ homomorphism.ker) := by
      ext member
      simp
    rw [hequal, hkernel]
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rw [← Finset.sum_fiberwise' Finset.univ homomorphism function]
  simp only [Finset.sum_const, hcard, nsmul_eq_mul]
  rw [Finset.mul_sum]

theorem card_surjective_group_hom {source target : Type*} [Group source] [Group target]
    [Fintype source] [Fintype target] (homomorphism : source →* target)
    (hsurjective : Function.Surjective homomorphism) :
    Nat.card source = Nat.card homomorphism.ker * Nat.card target := by
  have hsum := sum_comp_surjective_group_hom homomorphism hsurjective (fun _element => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Nat.card_eq_fintype_card] at hsum
  exact_mod_cast hsum

theorem characterPairing_inflation {source target : Type*} [Group source] [Group target]
    [Fintype source] [Fintype target] (homomorphism : source →* target)
    (hsurjective : Function.Surjective homomorphism) (left right : target → ℂ) :
    characterPairing (left ∘ homomorphism) (right ∘ homomorphism) = characterPairing left right := by
  unfold characterPairing
  simp only [Function.comp_apply, map_inv]
  rw [sum_comp_surjective_group_hom homomorphism hsurjective
    (fun element => left element * right element⁻¹), card_surjective_group_hom homomorphism hsurjective]
  have hkernel : (Nat.card homomorphism.ker : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  push_cast
  field_simp

universe groupUniverse vectorUniverse

@[expose] noncomputable def inflatedFiniteComplexRepresentation {source target : Type groupUniverse}
    [Group source] [Group target] (homomorphism : source →* target)
    (data : FiniteComplexRepresentation.{groupUniverse, vectorUniverse} target) :
    FiniteComplexRepresentation.{groupUniverse, vectorUniverse} source :=
  { vector := data.vector
    representation := data.representation.comp homomorphism }

theorem inflatedFiniteComplexRepresentation_character {source target : Type groupUniverse}
    [Group source] [Group target] (homomorphism : source →* target)
    (data : FiniteComplexRepresentation.{groupUniverse, vectorUniverse} target) :
    (inflatedFiniteComplexRepresentation homomorphism data).character = data.character ∘ homomorphism := rfl

@[expose] noncomputable def inflationLinearMap {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) : (target → ℂ) →ₗ[ℤ] (source → ℂ) :=
  LinearMap.funLeft ℤ ℂ homomorphism

theorem inflation_mem_virtualCharacters {source target : Type groupUniverse}
    [Group source] [Group target] (homomorphism : source →* target) {function : target → ℂ}
    (hvirtual : function ∈ virtualCharacters target) :
    function ∘ homomorphism ∈ virtualCharacters source := by
  have hmap : virtualCharacters target ≤
      (virtualCharacters source).comap (inflationLinearMap homomorphism) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨data, rfl⟩
    exact character_mem_virtualCharacters (inflatedFiniteComplexRepresentation homomorphism data)
  exact hmap hvirtual

end CFSG.TwoRankLowerBound.Helpers
