module

public import CFSG.CharacterTheory.BrauerCharacters.CoefficientTheorem

public noncomputable section

open scoped Classical Pointwise

namespace CFSG.BrauerCharacters

open CFSG.TwoRankLowerBound.Helpers CFSG.BrauerThirdMainTheorem.Helpers

variable {ideal : Ideal ComplexAlgebraicIntegers} [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
  [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] {G : Type} [Group G] [Fintype G]

@[expose] def relTrace (C : Subgroup G) (w : G → ℂ) (g : G) : ℂ :=
  ∑ q : G ⧸ C, w ((Quotient.out q)⁻¹ * g * Quotient.out q)

omit [Fintype G] in
theorem relTrace_out_eq {C : Subgroup G} {w : G → ℂ}
    (hwC : ∀ (g : G) (c : C), w ((c : G) * g * (c : G)⁻¹) = w g) (g : G) {q : G ⧸ C} {y : G}
    (hy : (y : G ⧸ C) = q) :
    w ((Quotient.out q)⁻¹ * g * Quotient.out q) = w (y⁻¹ * g * y) := by
  have h : (y : G ⧸ C) = ((Quotient.out q : G) : G ⧸ C) := by rw [hy, QuotientGroup.out_eq']
  obtain ⟨c, hc, hqc⟩ : ∃ c ∈ C, (Quotient.out q : G) = y * c :=
    ⟨_, QuotientGroup.eq.mp h, by group⟩
  rw [hqc, ← hwC (y⁻¹ * g * y) ⟨c, hc⟩⁻¹]
  congr 1
  change (y * c)⁻¹ * g * (y * c) = c⁻¹ * (y⁻¹ * g * y) * c⁻¹⁻¹
  group

omit [Fintype G] in
theorem sum_mem_localMaxIdeal_of_fixed {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup p Q)
    {X : Type} [Fintype X] [MulAction Q X] (f : X → ℂ) (hf : ∀ (q : Q) (x : X), f (q • x) = f x)
    (hfR : ∀ x, f x ∈ CFSG.BlocksLocalRing ideal)
    (hfix : ∀ x : X, (∀ q : Q, q • x = x) → f x ∈ CFSG.BlocksLocalMaxIdeal ideal) :
    ∑ x, f x ∈ CFSG.BlocksLocalMaxIdeal ideal := by
  have hm : ideal.IsMaximal := inferInstance
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x => f x ∈ CFSG.BlocksLocalMaxIdeal ideal) f]
  apply localMaxIdeal_add ideal hm
  · apply localMaxIdeal_sum ideal hm
    intro x _
    exact x.2
  · let act : MulAction Q {x : X // ¬ f x ∈ CFSG.BlocksLocalMaxIdeal ideal} :=
      { smul := fun q y => ⟨q • (y : X), by rw [hf]; exact y.2⟩
        one_smul := fun y => Subtype.ext (one_smul Q (y : X))
        mul_smul := fun q r y => Subtype.ext (mul_smul q r (y : X)) }
    refine sum_mem_localMaxIdeal_of_action (ideal := ideal) p hQ
      (fun y : {x : X // ¬ f x ∈ CFSG.BlocksLocalMaxIdeal ideal} => f y)
      (fun q y => hf q y) (fun y => hfR y) (fun y => ?_)
    by_contra hall
    push Not at hall
    exact y.2 (hfix (y : X) fun q => congrArg Subtype.val (hall q))

omit [Fintype G] [Fact p.Prime] in
theorem natCast_not_mem_localMaxIdeal {n : ℕ} (hn : ¬ p ∣ n) :
    (n : ℂ) ∉ CFSG.BlocksLocalMaxIdeal ideal := by
  have hm : ideal.IsMaximal := inferInstance
  rintro ⟨a, d, ha, hd, had⟩
  have hd0 : (d : ℂ) ≠ 0 := denominator_ne_zero ideal hd
  have h1 : (n : ComplexAlgebraicIntegers) * d = a := by
    apply Subtype.ext
    push_cast
    rw [had, div_mul_cancel₀ _ hd0]
  have h2 : (n : ComplexAlgebraicIntegers) * d ∈ ideal := by rw [h1]; exact ha
  rcases hm.isPrime.mem_or_mem h2 with h | h
  · have h3 : ((n : ℕ) : ComplexAlgebraicIntegers ⧸ ideal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk ideal)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h
    exact hn ((CharP.cast_eq_zero_iff (ComplexAlgebraicIntegers ⧸ ideal) p n).mp h3)
  · exact hd h

end CFSG.BrauerCharacters
