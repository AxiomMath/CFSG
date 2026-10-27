module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineOddPairRegular
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair

variable {Y Ω : Type*} [Group Y] [Finite Ω] [MulAction Y Ω]

@[expose] def OriginalFixedSet (A : Subgroup Y) : Set Ω :=
  {γ | ∀ a ∈ A, a • γ = γ}

theorem prime_regular_pair_fixed_count_ge_prime
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (Q : Subgroup ((MulAction.toPermHom Y Ω).range)) [Q.Normal]
    [IsElementaryAbelian ℓ Q]
    (hreg : RegularOnEntire (MulAction.toPermHom Y Ω).range Q)
    (A : Subgroup Y) (α β : Ω) (hne : α ≠ β)
    (hα : ∀ a ∈ A, a • α = α) (hβ : ∀ a ∈ A, a • β = β) :
    ℓ ≤ Nat.card (OriginalFixedSet (Ω := Ω) A) := by
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let F := (MulAction.toPermHom Y Ω).range
  obtain ⟨q, hq, _⟩ := hreg α β
  have hqne : q ≠ 1 := by
    intro h
    rw [h] at hq
    exact hne hq
  have hqpow : q ^ ℓ = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p ℓ Q) q
  have hqorder : orderOf q = ℓ := orderOf_eq_prime hqpow hqne
  let points : Fin ℓ → OriginalFixedSet (Ω := Ω) A := fun i =>
    ⟨((((q ^ i.val : Q) : F) : Equiv.Perm Ω) α), by
      intro a ha
      exact pair_fixed_regular_transporter_powers F Q hreg α β q hq
        ((MulAction.toPermHom Y Ω).rangeRestrict a) (hα a ha) (hβ a ha) i.val⟩
  have hpoints : Function.Injective points := by
    intro i j hij
    have hcoords := (regular_coordinates_bijective F Q hreg α).1
      (congrArg Subtype.val hij)
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (by simp [hqorder])
      (by simp [hqorder]) hcoords
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective points hpoints

theorem odd_prime_regular_pair_fixed_count_ge_three
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (Q : Subgroup ((MulAction.toPermHom Y Ω).range)) [Q.Normal]
    [IsElementaryAbelian ℓ Q]
    (hreg : RegularOnEntire (MulAction.toPermHom Y Ω).range Q)
    (A : Subgroup Y) (α β : Ω) (hne : α ≠ β)
    (hα : ∀ a ∈ A, a • α = α) (hβ : ∀ a ∈ A, a • β = β) :
    3 ≤ Nat.card (OriginalFixedSet (Ω := Ω) A) := by
  have hthree : 3 ≤ ℓ := by
    have htwo := hℓ.two_le
    have hneTwo : ℓ ≠ 2 := by
      intro h
      exact hodd.not_two_dvd_nat (h ▸ dvd_rfl)
    omega
  exact hthree.trans (prime_regular_pair_fixed_count_ge_prime ℓ hℓ Q hreg A α β hne hα hβ)

end CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair
