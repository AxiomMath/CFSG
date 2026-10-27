module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreOddLieAut

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def OddLieCoreFamilyInput (τ : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    ∀ n p f : ℕ, p.Prime → p ≠ 2 → StatedLieAdmissible τ n p f → LieModel S τ n p f →
    (¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel S .PSL 2 p f) →
    ∀ i : MulAut S, orderOf i = 2 → ∀ R : Subgroup (MulAut S), Odd (Nat.card R) →
      (∀ r ∈ R, r * i = i * r) →
      (∀ s : S, i s = s → Odd (orderOf s) → ∀ r ∈ R,
        MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) →
      ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁

theorem oddLieOuterCoreInput_of_families (h : ∀ τ, OddLieCoreFamilyInput τ) :
    OddLieOuterCoreInput := by
  intro S _ _ _ hna hodd hL2 i hi R hR hRi hRc
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hm⟩ := hodd
  exact h τ S hna n p f hp hp2 hadm hm hL2 i hi R hR hRi hRc

theorem oddLieCoreFamilyInput_of_not_admissible {τ : StatedLieTag}
    (hτ : ∀ n p f : ℕ, p ≠ 2 → ¬ StatedLieAdmissible τ n p f) : OddLieCoreFamilyInput τ :=
  fun _ _ _ _ _ n p f _ hp2 hadm => absurd hadm (hτ n p f hp2)

theorem oddLieCoreFamilyInput_twistedB2 : OddLieCoreFamilyInput .twistedB2 :=
  oddLieCoreFamilyInput_of_not_admissible fun _ _ _ hp2 hadm => hp2 hadm.2.2.2.1

theorem oddLieCoreFamilyInput_twistedF4 : OddLieCoreFamilyInput .twistedF4 :=
  oddLieCoreFamilyInput_of_not_admissible fun _ _ _ hp2 hadm => hp2 hadm.2.2.2.1

theorem oddLieCoreFamilyInput_Tits : OddLieCoreFamilyInput .Tits :=
  oddLieCoreFamilyInput_of_not_admissible fun _ _ _ hp2 hadm => hp2 hadm.2.2.2.1

end CFSG.ComponentClassification.Foote5.OddLieCore
