module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterInflation
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasisDegreeSum
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalAverageCharacterKernel
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NormalComplementPrincipal

public section

open scoped BigOperators Classical

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers

universe u

theorem inflated_isIrreducible {C L : Type u} [Group C] [Group L] (π : C →* L)
    (hπ : Function.Surjective π) (data : FiniteComplexRepresentation L)
    (hdata : data.IsIrreducible) : (inflatedFiniteComplexRepresentation π data).IsIrreducible := by
  let : data.representation.IsIrreducible := hdata
  exact (subrepresentationInflation π hπ data.representation).isSimpleOrder

theorem normalSubgroupCharacterSupport_degree_sq_sum {C : Type*} [Group C] [Fintype C]
    (basis : FiniteIrreducibleCharacterBasis C) (K : Subgroup C) [K.Normal] [Fintype K] :
    (∑ label ∈ normalSubgroupCharacterSupport basis K,
        (basis.representation label).character 1 ^ 2) * (Nat.card K : ℂ) = Nat.card C := by
  let complexUnit : ℂˣ := Units.mk0 (Nat.card K) (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hidem := normalSubgroupAverage_eq_characterSubsetIdempotent basis K complexUnit rfl
  have hcoeff := congrArg (fun value : MonoidAlgebra ℂ C => value.coeff 1) hidem
  rw [characterSubsetIdempotent_coeff] at hcoeff
  have hleft : (normalSubgroupAverage K complexUnit).coeff 1 = ((Nat.card K : ℂ))⁻¹ := by
    simp only [normalSubgroupAverage, Units.smul_def, MonoidAlgebra.coeff_smul,
      MonoidAlgebra.coeff_sum, Finsupp.smul_apply, Finsupp.finsetSum_apply,
      MonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (1 : K)]
    · simp [complexUnit]
    · intro k _ hk
      have hk' : (k : C) ≠ 1 := fun h => hk (Subtype.ext h)
      rw [ite_eq_right hk']
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hleft] at hcoeff
  have hsum : ∑ label ∈ normalSubgroupCharacterSupport basis K,
      (basis.representation label).character 1 / (Nat.card C : ℂ) *
        (basis.representation label).character 1⁻¹ =
      (∑ label ∈ normalSubgroupCharacterSupport basis K,
        (basis.representation label).character 1 ^ 2) / (Nat.card C : ℂ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro label _
    rw [inv_one]
    ring
  rw [hsum] at hcoeff
  have hKne : (Nat.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hCne : (Nat.card C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp at hcoeff
  rw [hcoeff]
  ring

theorem exists_inflation_labels {C L : Type u} [Group C] [Fintype C] [Group L] [Fintype L]
    (basis : FiniteIrreducibleCharacterBasis C) (localBasis : FiniteIrreducibleCharacterBasis L)
    (π : C →* L) (hπ : Function.Surjective π) [Fintype π.ker] :
    ∃ ι : localBasis.index → basis.index, Function.Injective ι ∧
      (∀ θ, (basis.representation (ι θ)).character =
        (localBasis.representation θ).character ∘ π) ∧
      Finset.univ.image ι = normalSubgroupCharacterSupport basis π.ker := by
  have hlabel : ∀ θ : localBasis.index, ∃ label : basis.index,
      (basis.representation label).character = (localBasis.representation θ).character ∘ π :=
    fun θ => finiteIrreducibleCharacterBasis_contains_irreducible basis
      (inflatedFiniteComplexRepresentation π (localBasis.representation θ))
      (inflated_isIrreducible π hπ _ (localBasis.irreducible θ))
  choose ι hι using hlabel
  have hinj : Function.Injective ι := by
    intro θ θ' h
    apply localBasis.distinct
    funext l
    obtain ⟨c, rfl⟩ := hπ l
    have h2 : (localBasis.representation θ).character ∘ π =
        (localBasis.representation θ').character ∘ π := by
      rw [← hι θ, ← hι θ', h]
    exact congrFun h2 c
  refine ⟨ι, hinj, hι, ?_⟩
  have hsub : Finset.univ.image ι ⊆ normalSubgroupCharacterSupport basis π.ker := by
    intro a ha
    obtain ⟨θ, -, rfl⟩ := Finset.mem_image.mp ha
    have hconst : ∀ k : π.ker, (basis.representation (ι θ)).character k.val =
        (basis.representation (ι θ)).character 1 := by
      intro k
      rw [hι θ, Function.comp_apply, Function.comp_apply, MonoidHom.mem_ker.mp k.2, map_one]
    have htriv := normalSubgroup_character_constant_degree_trivial basis π.ker (ι θ) hconst
    simp only [normalSubgroupCharacterSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact htriv
  have hdeg : ∀ a : basis.index, (basis.representation a).character 1 =
      (Module.finrank ℂ (basis.representation a).vector : ℂ) := by
    intro a
    rw [FiniteComplexRepresentation.character, Representation.char_one]
  have himage : ∑ a ∈ Finset.univ.image ι, (basis.representation a).character 1 ^ 2 =
      (Nat.card L : ℂ) := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h), ← finiteIrreducibleCharacterBasis_sum_degree_sq]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [hι θ, Function.comp_apply, map_one]
  have hA := normalSubgroupCharacterSupport_degree_sq_sum basis π.ker
  have hcard := card_surjective_group_hom π hπ
  have hAsum : ∑ a ∈ normalSubgroupCharacterSupport basis π.ker,
      (basis.representation a).character 1 ^ 2 = (Nat.card L : ℂ) := by
    have hKne : (Nat.card π.ker : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    apply mul_right_cancel₀ hKne
    rw [hA, hcard]
    push_cast
    ring
  have hdiff : ∑ a ∈ normalSubgroupCharacterSupport basis π.ker \ Finset.univ.image ι,
      (Module.finrank ℂ (basis.representation a).vector ^ 2 : ℕ) = 0 := by
    have hsplit := Finset.sum_sdiff hsub
      (f := fun a => (basis.representation a).character 1 ^ 2)
    rw [himage, hAsum, add_eq_right] at hsplit
    have hcast : ((∑ a ∈ normalSubgroupCharacterSupport basis π.ker \ Finset.univ.image ι,
        (Module.finrank ℂ (basis.representation a).vector ^ 2 : ℕ) : ℕ) : ℂ) = 0 := by
      push_cast
      rw [← hsplit]
      exact Finset.sum_congr rfl fun a _ => by rw [hdeg]
    exact_mod_cast hcast
  apply Finset.Subset.antisymm hsub
  intro a ha
  by_contra hnot
  have hzero := (Finset.sum_eq_zero_iff.mp hdiff) a (Finset.mem_sdiff.mpr ⟨ha, hnot⟩)
  have hfin : Module.finrank ℂ (basis.representation a).vector = 0 :=
    (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hzero
  apply irreducible_character_degree_ne_zero (basis.representation a) (basis.irreducible a)
  rw [hdeg, hfin, Nat.cast_zero]

theorem sum_normalSubgroupCharacterSupport_eq {C L : Type u} [Group C] [Fintype C] [Group L]
    [Fintype L] (basis : FiniteIrreducibleCharacterBasis C)
    (localBasis : FiniteIrreducibleCharacterBasis L) (π : C →* L) (hπ : Function.Surjective π)
    [Fintype π.ker] (F : (C → ℂ) → ℂ) :
    ∑ a ∈ normalSubgroupCharacterSupport basis π.ker, F (basis.representation a).character =
      ∑ θ, F ((localBasis.representation θ).character ∘ π) := by
  obtain ⟨ι, hinj, hι, himage⟩ := exists_inflation_labels basis localBasis π hπ
  rw [← himage, Finset.sum_image (fun x _ y _ h => hinj h)]
  exact Finset.sum_congr rfl fun θ _ => by rw [hι θ]

end CFSG.LyonsUnitaryFour
