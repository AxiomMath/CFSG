module

public import CFSG.LocalAnalysis.ComponentClassification.CoprimeAutomorphisms

public section

namespace CFSG.ComponentClassification.ThompsonAB

theorem coprime_eq_one {V B : Type*} [Group V] [Finite V] [Group B] [Finite B]
    (prime : ℕ) [Fact prime.Prime] (hV : IsPGroup prime V) (hB : IsPGroup prime B)
    (action : B →* MulAut V) (automorphism : MulAut V)
    (hcommutes : ∀ element : B, Commute automorphism (action element))
    (hfixed : ∀ member : V, (∀ element : B, action element member = member) →
      automorphism member = member)
    (exponent : ℕ) (hpower : automorphism ^ exponent = 1)
    (hcoprime : exponent.Coprime prime) : automorphism = 1 := by
  let product := V ⋊[action] B
  let : Finite product := Finite.of_injective (SemidirectProduct.equivProd : product ≃ V × B)
    SemidirectProduct.equivProd.injective
  have hcompatibility : ∀ element : B,
      (action element).trans automorphism = automorphism.trans (action element) := by
    intro element
    ext member
    exact congrArg (fun transformation : MulAut V => transformation member)
      (hcommutes element).eq
  let extension : MulAut product :=
    SemidirectProduct.congr automorphism (MulEquiv.refl B) hcompatibility
  have hleft : ∀ member : product, (extension member).left = automorphism member.left :=
    SemidirectProduct.congr_apply_left _ _ _
  have hright : ∀ member : product, (extension member).right = member.right :=
    SemidirectProduct.congr_apply_right _ _ _
  have hproductPrime : IsPGroup prime product := by
    obtain ⟨leftExponent, hleftCard⟩ := hV.exists_card_eq
    obtain ⟨rightExponent, hrightCard⟩ := hB.exists_card_eq
    apply IsPGroup.of_card (n := leftExponent + rightExponent)
    rw [SemidirectProduct.card, hleftCard, hrightCard, pow_add]
  have hextensionPower : extension ^ exponent = 1 := by
    have hpowers : ∀ power : ℕ, ∀ member : product,
        ((extension ^ power) member).left = (automorphism ^ power) member.left ∧
          ((extension ^ power) member).right = member.right := by
      intro power
      induction power with
      | zero => intro member; exact ⟨rfl, rfl⟩
      | succ power hinduction =>
          intro member
          rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply]
          exact ⟨(hleft _).trans (congrArg automorphism (hinduction member).1),
            (hright _).trans (hinduction member).2⟩
    apply MulEquiv.ext
    intro member
    apply SemidirectProduct.ext
    · rw [(hpowers exponent member).1, hpower]
      rfl
    · exact (hpowers exponent member).2
  let complement : Subgroup product := (SemidirectProduct.inr (φ := action)).range
  let centralizer := Subgroup.centralizer (complement : Set product)
  let selfCentralizing := complement ⊔ centralizer
  have hself : Subgroup.centralizer (selfCentralizing : Set product) ≤ selfCentralizing :=
    (Subgroup.centralizer_le (le_sup_left : complement ≤ selfCentralizing)).trans le_sup_right
  have hcomplementFixed : complement ≤ FixedCommutingProduct.fixedSubgroup extension := by
    intro member hmem
    obtain ⟨element, rfl⟩ := hmem
    change extension (SemidirectProduct.inr element) = SemidirectProduct.inr element
    apply SemidirectProduct.ext
    · rw [hleft]
      exact map_one automorphism
    · exact hright _
  have hcentralizerFixed : centralizer ≤ FixedCommutingProduct.fixedSubgroup extension := by
    intro member hmem
    have hleftFixed : ∀ element : B, action element member.left = member.left := by
      intro element
      have hcommutation := Subgroup.mem_centralizer_iff.mp hmem
        (SemidirectProduct.inr element) ⟨element, rfl⟩
      have heq := congrArg SemidirectProduct.left hcommutation
      change 1 * action element member.left = member.left * action member.right 1 at heq
      simpa only [one_mul, map_one, mul_one] using heq
    change extension member = member
    apply SemidirectProduct.ext
    · rw [hleft]
      exact hfixed member.left hleftFixed
    · exact hright _
  have hselfFixed : selfCentralizing ≤ FixedCommutingProduct.fixedSubgroup extension :=
    sup_le hcomplementFixed hcentralizerFixed
  have hcoprimeCard : exponent.Coprime (Nat.card product) := by
    obtain ⟨power, hcard⟩ := hproductPrime.exists_card_eq
    rw [hcard]
    exact hcoprime.pow_right power
  have hextensionIdentity := CoprimeAutomorphisms.eq_one_of_self_centralizing prime
    hproductPrime selfCentralizing hself extension exponent hextensionPower hcoprimeCard hselfFixed
  ext member
  have heq := congrArg (fun transformation : MulAut product =>
    (transformation (SemidirectProduct.inl member)).left) hextensionIdentity
  rw [hleft] at heq
  exact heq

end CFSG.ComponentClassification.ThompsonAB
