module

public import CFSG.CharacterTheory.BlockBasics.Defects

public noncomputable section

open scoped Classical

namespace CFSG.BrauerCharacters

open CFSG.TwoRankLowerBound.Helpers CFSG.BrauerThirdMainTheorem.Helpers

variable {ideal : Ideal ComplexAlgebraicIntegers} [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
  [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]

theorem sum_mem_localMaxIdeal_of_action {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup p Q)
    {X : Type} [Fintype X] [MulAction Q X] (f : X → ℂ) (hf : ∀ (q : Q) (x : X), f (q • x) = f x)
    (hfR : ∀ x, f x ∈ CFSG.BlocksLocalRing ideal) (hfix : ∀ x : X, ∃ q : Q, q • x ≠ x) :
    ∑ x, f x ∈ CFSG.BlocksLocalMaxIdeal ideal := by
  have hm : ideal.IsMaximal := inferInstance
  have hpm := CFSG.BlockBasics.prime_mem_of_charP p ideal
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := Finset.univ.image f)
    (fun x hx => Finset.mem_image_of_mem f hx)]
  apply localMaxIdeal_sum ideal hm
  intro v hv
  obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp hv
  have hsum : ∑ x ∈ Finset.univ.filter (fun x => f x = f x₀), f x =
      ((Finset.univ.filter (fun x => f x = f x₀)).card : ℂ) * f x₀ := by
    rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2), Finset.sum_const,
      nsmul_eq_mul]
  rw [hsum]
  apply localMaxIdeal_mul_localRing ideal hm _ (hfR x₀)
  apply localMaxIdeal_natCast_of_dvd ideal hm p hpm
  let act : MulAction Q {x : X // f x = f x₀} :=
    { smul := fun q y => ⟨q • (y : X), (hf q y).trans y.2⟩
      one_smul := fun y => Subtype.ext (one_smul Q (y : X))
      mul_smul := fun q r y => Subtype.ext (mul_smul q r (y : X)) }
  have hcong := hQ.card_modEq_card_fixedPoints {x : X // f x = f x₀}
  have hempty : Nat.card (MulAction.fixedPoints Q {x : X // f x = f x₀}) = 0 := by
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨y, hy⟩
    obtain ⟨q, hq⟩ := hfix y
    exact hq (congrArg Subtype.val (hy q))
  rw [hempty, Nat.card_eq_fintype_card, Fintype.card_subtype] at hcong
  exact (Nat.modEq_zero_iff_dvd).mp hcong

end CFSG.BrauerCharacters
