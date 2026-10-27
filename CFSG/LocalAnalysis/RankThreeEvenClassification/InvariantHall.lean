module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.HallConjugacy
public import CFSG.LocalAnalysis.RankThreeEvenClassification.HallContainment
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SemidirectHall

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem exists_invariant_hall_containing {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [Finite actor] [Finite acted] [Group.IsSolvable acted]
    [MulDistribMulAction actor acted]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime actor)
    (hcomplement : ¬prime ∣ Nat.card acted) (primes : Set ℕ)
    (subgroup : Subgroup acted) (horder : PrimeSetOrder primes (Nat.card subgroup))
    (hinvariant : ∀ member : actor,
      subgroup.map (MulDistribMulAction.toMonoidHom acted member) = subgroup) :
    ∃ hall : Subgroup acted, HallFor primes hall ∧ subgroup ≤ hall ∧
      ∀ member : actor, hall.map (MulDistribMulAction.toMonoidHom acted member) = hall := by
  have : Fact prime.Prime := ⟨hprime⟩
  have : Group.IsNilpotent actor := hpgroup.isNilpotent
  let action := MulDistribMulAction.toMulAut actor acted
  let extension := SemidirectProduct acted actor action
  have : Finite extension := Finite.of_equiv (acted × actor) SemidirectProduct.equivProd.symm
  have : Group.IsSolvable extension := Group.isSolvable_of_ker_le_range
    (SemidirectProduct.inl : acted →* extension) (SemidirectProduct.rightHom : extension →* actor)
    (le_of_eq SemidirectProduct.range_inl_eq_ker_rightHom.symm)
  let extendedPrimes := primes ∪ {prime}
  let initial := invariantSemidirectSubgroup action subgroup hinvariant
  have hinitialOrder : PrimeSetOrder extendedPrimes (Nat.card initial) := by
    rw [invariant_semidirect_subgroup_card action subgroup hinvariant]
    apply PrimeSetOrder.mul
    · intro divisor hdivisor hdiv
      exact Or.inl (horder divisor hdivisor hdiv)
    · obtain ⟨dimension, hcard⟩ := hpgroup.exists_card_eq
      rw [hcard]
      exact PrimeSetOrder.prime_pow extendedPrimes prime hprime (Or.inr rfl) dimension
  obtain ⟨extensionHall, hextensionHall, hinitialLe⟩ :=
    hall_containment_of_solvable extendedPrimes initial hinitialOrder
  have hactorLe : ∀ member : actor, (SemidirectProduct.inr member : extension) ∈ extensionHall := by
    intro member
    apply hinitialLe
    change (SemidirectProduct.inr member : extension).left ∈ subgroup
    simp
  let hall := extensionHall.comap (SemidirectProduct.inl : acted →* extension)
  have hhall : HallFor primes hall := by
    constructor
    · have hcardDiv : Nat.card hall ∣ Nat.card extensionHall := by
        have hle : hall.map (SemidirectProduct.inl : acted →* extension) ≤ extensionHall :=
          Subgroup.map_le_iff_le_comap.mpr le_rfl
        have hdiv := Subgroup.card_dvd_of_le hle
        rw [Subgroup.card_map_of_injective SemidirectProduct.inl_injective] at hdiv
        exact hdiv
      intro divisor hdivisor hdiv
      obtain hmem | heq := hextensionHall.1 divisor hdivisor (hdiv.trans hcardDiv)
      · exact hmem
      · have hequal : divisor = prime := heq
        exact False.elim (hcomplement (hequal ▸ hdiv.trans hall.card_subgroup_dvd_card))
    · intro divisor hdivisor hdiv
      have hindex : hall.index = extensionHall.index :=
        semidirect_subgroup_index action extensionHall hactorLe
      have hnotMem := hextensionHall.2 divisor hdivisor (hindex ▸ hdiv)
      exact fun hmem => hnotMem (Or.inl hmem)
  refine ⟨hall, hhall, ?_, semidirect_comap_inl_invariant action extensionHall hactorLe⟩
  intro element helement
  apply hinitialLe
  change (SemidirectProduct.inl element : extension).left ∈ subgroup
  simpa only [SemidirectProduct.left_inl] using helement

theorem exists_invariant_hall {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [Finite actor] [Finite acted] [Group.IsSolvable acted]
    [MulDistribMulAction actor acted]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime actor)
    (hcomplement : ¬prime ∣ Nat.card acted) (primes : Set ℕ) :
    ∃ hall : Subgroup acted, HallFor primes hall ∧
      ∀ member : actor, hall.map (MulDistribMulAction.toMonoidHom acted member) = hall := by
  obtain ⟨hall, hhall, _, hinvariant⟩ := exists_invariant_hall_containing prime hprime hpgroup
    hcomplement primes (⊥ : Subgroup acted)
    (by rw [Subgroup.card_bot]; exact PrimeSetOrder.one primes)
    (by intro member; exact Subgroup.map_bot _)
  exact ⟨hall, hhall, hinvariant⟩

theorem exists_fixed_conjugator_of_invariant_halls {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [Finite acted] [Group.IsSolvable acted]
    [MulDistribMulAction actor acted]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime actor)
    (hcomplement : ¬prime ∣ Nat.card acted) (primes : Set ℕ)
    (first second : Subgroup acted) (hfirst : HallFor primes first) (hsecond : HallFor primes second)
    (hfirstInvariant : ∀ member : actor,
      first.map (MulDistribMulAction.toMonoidHom acted member) = first)
    (hsecondInvariant : ∀ member : actor,
      second.map (MulDistribMulAction.toMonoidHom acted member) = second) :
    ∃ conjugator : acted, (∀ member : actor, member • conjugator = conjugator) ∧
      first.map (MulAut.conj conjugator).toMonoidHom = second :=
  exists_fixed_conjugator_of_pGroup_prime_complement_action prime hprime hpgroup hcomplement
    first second hfirstInvariant hsecondInvariant (hall_conjugacy_of_solvable primes first second hfirst hsecond)

end CFSG.RankThreeEvenClassification.Helpers
