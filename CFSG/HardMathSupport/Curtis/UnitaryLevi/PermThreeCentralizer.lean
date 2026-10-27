module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Equiv Equiv.Perm
open scoped commutatorElement

theorem exists_perfect_of_five_le_fixed {α : Type*} [Fintype α] [DecidableEq α] (π : Perm α)
    (h : 5 ≤ Fintype.card {x // π x = x}) :
    ∃ W : Subgroup (Perm α), ⁅W, W⁆ = W ∧ W ≠ ⊥ ∧ ∀ w ∈ W, Commute w π := by
  classical
  let p : α → Prop := fun x => π x = x
  have h5 : 5 ≤ Nat.card (Subtype p) := by simpa [Nat.card_eq_fintype_card] using h
  refine ⟨(alternatingGroup (Subtype p)).map
    (Equiv.Perm.ofSubtype : Perm (Subtype p) →* Perm α), ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, commutator_alternatingGroup_eq_self h5]
  · intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ Equiv.Perm.ofSubtype_injective] at hbot
    have : IsSimpleGroup (alternatingGroup (Subtype p)) := alternatingGroup.isSimpleGroup h5
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance hbot
  · rintro _ ⟨σ, -, rfl⟩
    ext x
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    by_cases hx : π x = x
    · have h1 : Equiv.Perm.ofSubtype σ x = σ ⟨x, hx⟩ := Equiv.Perm.ofSubtype_apply_of_mem σ hx
      rw [hx, h1]
      exact (σ ⟨x, hx⟩).2.symm
    · have hπx : ¬ p (π x) := fun h' => hx (π.injective h')
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem σ hx, Equiv.Perm.ofSubtype_apply_of_not_mem σ hπx]

def diagModelEquiv : (Fin 6 × Fin 3) ⊕ Fin 2 ≃ Fin 20 :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 2))).trans finSumFinEquiv

def diagModelThree : Perm ((Fin 6 × Fin 3) ⊕ Fin 2) :=
  Equiv.sumCongr (Equiv.prodCongr (Equiv.refl (Fin 6)) (finRotate 3)) (Equiv.refl (Fin 2))

def diagModelHom : Perm (Fin 6) →* Perm ((Fin 6 × Fin 3) ⊕ Fin 2) :=
  MonoidHom.mk' (fun σ => Equiv.sumCongr (Equiv.prodCongr σ (Equiv.refl (Fin 3)))
    (Equiv.refl (Fin 2))) (by
      intro a b
      ext x
      rcases x with ⟨i, j⟩ | k <;> rfl)

theorem diagModelHom_injective : Function.Injective diagModelHom := by
  intro a b h
  refine Equiv.ext fun i => ?_
  have := congrArg (fun f : Perm ((Fin 6 × Fin 3) ⊕ Fin 2) => f (Sum.inl (i, 0))) h
  simpa [diagModelHom] using this

theorem diagModelHom_commute (σ : Perm (Fin 6)) :
    Commute (diagModelHom σ) diagModelThree := by
  ext x
  rcases x with ⟨i, j⟩ | k <;> rfl

theorem diagModelThree_pow : diagModelThree ^ 3 = 1 := by
  ext x; revert x; decide

theorem card_support_diag : (diagModelEquiv.permCongrHom diagModelThree).support.card = 18 := by
  decide

theorem exists_perfect_of_cycleType_card_six (π : Perm (Fin 20)) (h3 : π ^ 3 = 1)
    (hc : π.cycleType.card = 6) :
    ∃ W : Subgroup (Perm (Fin 20)), ⁅W, W⁆ = W ∧ W ≠ ⊥ ∧ ∀ w ∈ W, Commute w π := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π₀ : Perm (Fin 20) := diagModelEquiv.permCongrHom diagModelThree with hπ₀
  have hπ₀3 : π₀ ^ 3 = 1 := by
    rw [hπ₀, ← map_pow, diagModelThree_pow, map_one]
  have hct₀ := cycleType_of_pow_prime_eq_one hπ₀3
  have hct := cycleType_of_pow_prime_eq_one h3
  have hc₀ : π₀.cycleType.card = 6 := by
    have h18 : π₀.cycleType.sum = 18 := by rw [sum_cycleType]; exact card_support_diag
    rw [hct₀] at h18
    simp at h18
    omega
  have hconj : IsConj π π₀ := by
    rw [isConj_iff_cycleType_eq, hct, hct₀, hc, hc₀]
  obtain ⟨c, hcπ⟩ := isConj_iff.mp hconj
  let ι : Perm (Fin 6) →* Perm (Fin 20) :=
    (diagModelEquiv.permCongrHom : Perm _ ≃* _).toMonoidHom.comp diagModelHom
  have hι : Function.Injective ι :=
    diagModelEquiv.permCongrHom.injective.comp diagModelHom_injective
  have h5 : 5 ≤ Nat.card (Fin 6) := by simp
  let W₀ : Subgroup (Perm (Fin 20)) := (alternatingGroup (Fin 6)).map ι
  let φ : Perm (Fin 20) →* Perm (Fin 20) := (MulAut.conj c⁻¹).toMonoidHom
  have hφ : Function.Injective φ := (MulAut.conj c⁻¹).injective
  refine ⟨W₀.map φ, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator,
      commutator_alternatingGroup_eq_self h5]
  · intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ hφ, Subgroup.map_eq_bot_iff_of_injective _ hι] at hbot
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup h5
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance hbot
  · rintro _ ⟨_, ⟨σ, -, rfl⟩, rfl⟩
    have hcomm : Commute (ι σ) π₀ := by
      show Commute (diagModelEquiv.permCongrHom (diagModelHom σ))
        (diagModelEquiv.permCongrHom diagModelThree)
      exact (diagModelHom_commute σ).map diagModelEquiv.permCongrHom
    have h1 : ι σ * π₀ = π₀ * ι σ := hcomm.eq
    rw [← hcπ] at h1
    show c⁻¹ * ι σ * c⁻¹⁻¹ * π = π * (c⁻¹ * ι σ * c⁻¹⁻¹)
    have h2 : c⁻¹ * (ι σ * (c * π * c⁻¹) * c) = c⁻¹ * ((c * π * c⁻¹) * ι σ * c) := by rw [h1]
    simpa [mul_assoc] using h2

theorem exists_perfect_le_centralizer_of_pow_three (π : Perm (Fin 20)) (h3 : π ^ 3 = 1)
    (h1 : π ≠ 1) :
    ∃ W : Subgroup (Perm (Fin 20)), ⁅W, W⁆ = W ∧ W ≠ ⊥ ∧ ∀ w ∈ W, Commute w π := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hct := cycleType_of_pow_prime_eq_one h3
  have hsup : π.support.card = 3 * π.cycleType.card := by
    rw [← sum_cycleType]
    conv_lhs => rw [hct]
    simp [mul_comm]
  have hpos : 1 ≤ π.cycleType.card := by
    rw [Nat.one_le_iff_ne_zero, Ne, Multiset.card_eq_zero, Equiv.Perm.cycleType_eq_zero]
    exact h1
  have hle : π.support.card ≤ 20 := by simpa using Finset.card_le_univ π.support
  by_cases hc : π.cycleType.card = 6
  · exact exists_perfect_of_cycleType_card_six π h3 hc
  · apply exists_perfect_of_five_le_fixed
    have hfix : Fintype.card {x // π x = x} = 20 - π.support.card := by
      rw [Fintype.card_subtype]
      have : (Finset.univ.filter fun x => π x = x) = π.supportᶜ := by
        ext x; simp [Equiv.Perm.mem_support]
      rw [this, Finset.card_compl]
      simp
    rw [hfix]
    omega

end CFSG.HardMathSupport.Curtis.UnitaryLevi
