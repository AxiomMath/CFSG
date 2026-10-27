module

public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianGeneratorRank

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse indexUniverse

def piPowerKernelEquiv {Index : Type indexUniverse} (Factors : Index → Type groupUniverse)
    [∀ index, CommGroup (Factors index)] (prime : ℕ) :
    (powMonoidHom prime : ((index : Index) → Factors index) →* _).ker ≃*
      ((index : Index) → (powMonoidHom prime : Factors index →* _).ker) := {
  toFun := fun element index => ⟨element.val index, by
    change element.val index ^ prime = 1
    exact congrArg (fun entry : (index : Index) → Factors index => entry index)
      (show element.val ^ prime = 1 from element.property)⟩
  invFun := fun element => ⟨fun index => (element index).val, by
    change (fun index => (element index).val) ^ prime = 1
    exact funext (fun index => (element index).property)⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl }

theorem prime_power_cyclic_product_generator_rank {Index : Type indexUniverse} [Fintype Index]
    {prime : ℕ} (hprime : prime.Prime) (exponent : Index → ℕ)
    (hpositive : ∀ index, 0 < exponent index) :
    pGeneratorRank prime ((index : Index) → Multiplicative (ZMod (prime ^ exponent index))) =
      Fintype.card Index := by
  let : ∀ index, NeZero (prime ^ exponent index) := fun index =>
    ⟨pow_ne_zero _ hprime.ne_zero⟩
  let Factors := fun index => Multiplicative (ZMod (prime ^ exponent index))
  have hfactorCard : ∀ index, Nat.card (Factors index) = prime ^ exponent index := by
    intro index
    rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_eq_fintype_card]
    exact ZMod.card _
  have hpgroup : IsPGroup prime ((index : Index) → Factors index) := by
    apply IsPGroup.of_card (n := ∑ index, exponent index)
    rw [Nat.card_pi]
    simp only [hfactorCard]
    exact Finset.prod_pow_eq_pow_sum Finset.univ exponent prime
  have hkernelCard : ∀ index,
      Nat.card (powMonoidHom prime : Factors index →* Factors index).ker = prime := by
    intro index
    rw [IsCyclic.card_powMonoidHom_ker, hfactorCard]
    exact Nat.gcd_eq_right (dvd_pow_self _ (Nat.ne_zero_of_lt (hpositive index)))
  unfold pGeneratorRank
  rw [commutative_frattini_card_eq_power_kernel hprime hpgroup,
    Nat.card_congr (piPowerKernelEquiv Factors prime).toEquiv, Nat.card_pi]
  simp only [hkernelCard, Finset.prod_const, Finset.card_univ]
  exact Nat.log_pow hprime.one_lt _

theorem commutative_pGroup_coordinates {Ambient : Type groupUniverse} [CommGroup Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient) :
    ∃ (Index : Type) (_ : Fintype Index) (exponent : Index → ℕ),
      (∀ index, 0 < exponent index) ∧
      Nonempty (Ambient ≃* ((index : Index) → Multiplicative (ZMod (prime ^ exponent index)))) ∧
      Fintype.card Index = pGeneratorRank prime Ambient := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨Index, finiteIndex, orders, horders, ⟨equivalence⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite Ambient
  let := finiteIndex
  let Factors := fun index => Multiplicative (ZMod (orders index))
  let : ∀ index, NeZero (orders index) := fun index => ⟨by have := horders index; omega⟩
  have hproductGroup := hpgroup.of_surjective equivalence.toMonoidHom equivalence.surjective
  have hfactorGroup : ∀ index, IsPGroup prime (Factors index) := by
    intro index
    apply hproductGroup.of_surjective (Pi.evalMonoidHom Factors index)
    intro element
    exact ⟨Function.update (fun index => (1 : Factors index)) index element, by simp⟩
  have hfactorCard : ∀ index, Nat.card (Factors index) = orders index := by
    intro index
    rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_eq_fintype_card]
    exact ZMod.card _
  obtain ⟨exponent, hexponent⟩ := Classical.axiomOfChoice (fun index =>
    (hfactorGroup index).exists_card_eq)
  have hordersPower : ∀ index, orders index = prime ^ exponent index := by
    intro index
    exact (hfactorCard index).symm.trans (hexponent index)
  have hpositive : ∀ index, 0 < exponent index := by
    intro index
    by_contra hzero
    have heq : exponent index = 0 := by omega
    have hlarge := horders index
    rw [hordersPower index, heq, pow_zero] at hlarge
    omega
  let factorEquivalence : ∀ index, Factors index ≃*
      Multiplicative (ZMod (prime ^ exponent index)) := fun index => by
    rw [← hordersPower index]
  let coordinates := equivalence.trans (MulEquiv.piCongrRight factorEquivalence)
  refine ⟨Index, finiteIndex, exponent, hpositive, ⟨coordinates⟩, ?_⟩
  rw [pGeneratorRank_mulEquiv hprime hpgroup coordinates,
    prime_power_cyclic_product_generator_rank hprime exponent hpositive]

def dependentPiReindex {Index : Type indexUniverse} {NewIndex : Type}
    (Factors : Index → Type groupUniverse) [∀ index, Mul (Factors index)]
    (equivalence : Index ≃ NewIndex) :
    ((index : Index) → Factors index) ≃* ((index : NewIndex) → Factors (equivalence.symm index)) := {
  toEquiv := Equiv.piCongrLeft' Factors equivalence
  map_mul' := fun _ _ => rfl }

def dependentPiPair (Factors : Fin 2 → Type groupUniverse) [∀ index, Mul (Factors index)] :
    ((index : Fin 2) → Factors index) ≃* Factors 0 × Factors 1 := {
  toEquiv := piFinTwoEquiv Factors
  map_mul' := fun _ _ => rfl }

theorem commutative_pGroup_rank_two_coordinates {Ambient : Type groupUniverse} [CommGroup Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (hrank : pGeneratorRank prime Ambient ≤ 2) :
    IsCyclic Ambient ∨ ∃ upper lower : ℕ, 0 < lower ∧ lower ≤ upper ∧
      Nonempty (Ambient ≃* Multiplicative (ZMod (prime ^ upper)) ×
        Multiplicative (ZMod (prime ^ lower))) := by
  classical
  obtain ⟨Index, finiteIndex, exponent, hpositive, ⟨coordinates⟩, hcard⟩ :=
    commutative_pGroup_coordinates hprime hpgroup
  let := finiteIndex
  let : ∀ index, NeZero (prime ^ exponent index) := fun index =>
    ⟨pow_ne_zero _ hprime.ne_zero⟩
  let Factors := fun index => Multiplicative (ZMod (prime ^ exponent index))
  have hcardBound : Fintype.card Index ≤ 2 := hcard.trans_le hrank
  by_cases hsmall : Fintype.card Index ≤ 1
  · left
    have hcases : Fintype.card Index = 0 ∨ Fintype.card Index = 1 := by omega
    rcases hcases with hzero | hone
    · let : IsEmpty Index := Fintype.card_eq_zero_iff.mp hzero
      exact isCyclic_of_injective coordinates.toMonoidHom coordinates.injective
    · let : Unique Index := Classical.choice (Fintype.card_eq_one_iff_nonempty_unique.mp hone)
      let evaluation := MulEquiv.piUnique Factors
      exact isCyclic_of_injective (evaluation.toMonoidHom.comp coordinates.toMonoidHom)
        (evaluation.injective.comp coordinates.injective)
  · right
    have htwo : Fintype.card Index = 2 := by omega
    let indexing := Fintype.equivFinOfCardEq htwo
    let first := exponent (indexing.symm 0)
    let second := exponent (indexing.symm 1)
    let pairCoordinates : Ambient ≃* Multiplicative (ZMod (prime ^ first)) ×
        Multiplicative (ZMod (prime ^ second)) :=
      coordinates.trans ((dependentPiReindex Factors indexing).trans
        (dependentPiPair (fun index => Factors (indexing.symm index))))
    rcases le_total second first with hordered | hordered
    · exact ⟨first, second, hpositive _, hordered, ⟨pairCoordinates⟩⟩
    · exact ⟨second, first, hpositive _, hordered, ⟨pairCoordinates.trans MulEquiv.prodComm⟩⟩

end CFSG.LargeEvenClassification.Helpers
