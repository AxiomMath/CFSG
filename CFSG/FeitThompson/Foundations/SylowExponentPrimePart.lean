module

public import Mathlib.GroupTheory.Sylow
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X] {p k : ℕ}

theorem orderOf_dvd_exponent_of_mem {P : Subgroup X} {x : X} (hx : x ∈ P) :
    orderOf x ∣ Monoid.exponent P :=
  orderOf_dvd_of_pow_eq_one (Subgroup.pow_exponent_eq_one hx)

theorem exponent_subgroup_dvd (P : Subgroup X) : Monoid.exponent P ∣ Monoid.exponent X :=
  Monoid.exponent_dvd_of_monoidHom P.subtype Subtype.val_injective

theorem exponent_eq_pow_factorization_exponent [Finite X] (hp : p.Prime) {P : Subgroup X}
    (hP : Nat.card P = p ^ (Nat.card X).factorization p) :
    Monoid.exponent P = p ^ (Monoid.exponent X).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hexp : Monoid.exponent X ≠ 0 := Monoid.ExponentExists.exponent_ne_zero .of_finite
  have hPp : IsPGroup p P := IsPGroup.of_card hP
  refine Nat.dvd_antisymm ?_ ?_
  ·
    rw [Monoid.exponent_dvd]
    intro g
    obtain ⟨a, ha⟩ := hPp.exists_orderOf_eq_pow g
    have hdvd : orderOf g ∣ Monoid.exponent X :=
      Subgroup.orderOf_coe g ▸ Monoid.order_dvd_exponent (g : X)
    rw [ha] at hdvd ⊢
    exact pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization hexp).mp hdvd)
  ·
    obtain ⟨g, hg⟩ := hp.exists_orderOf_eq_pow_factorization_exponent X
    obtain ⟨c, hc⟩ := exists_forall_inv_mul_mul_mem hP
      (S := Subgroup.zpowers g) (IsPGroup.of_card (by rw [Nat.card_zpowers, hg]))
    have hmem : c⁻¹ * g * c ∈ P := hc g (Subgroup.mem_zpowers g)
    have heq : orderOf (c⁻¹ * g * c) = orderOf g :=
      SemiconjBy.orderOf_eq c (by unfold SemiconjBy; group)
    calc p ^ (Monoid.exponent X).factorization p = orderOf (c⁻¹ * g * c) := by rw [heq, hg]
      _ ∣ Monoid.exponent P := orderOf_dvd_exponent_of_mem hmem

theorem exponent_sylow_eq_pow_factorization_exponent [Finite X] [Fact p.Prime] (P : Sylow p X) :
    Monoid.exponent (P : Subgroup X) = p ^ (Monoid.exponent X).factorization p :=
  exponent_eq_pow_factorization_exponent Fact.out P.card_eq_multiplicity

theorem pow_dvd_exponent_iff_pow_dvd_exponent_sylow [Finite X] [Fact p.Prime] (P : Sylow p X) :
    p ^ k ∣ Monoid.exponent X ↔ p ^ k ∣ Monoid.exponent (P : Subgroup X) := by
  have hp : p.Prime := Fact.out
  have hexp : Monoid.exponent X ≠ 0 := Monoid.ExponentExists.exponent_ne_zero .of_finite
  rw [exponent_sylow_eq_pow_factorization_exponent P, hp.pow_dvd_iff_le_factorization hexp,
    Nat.pow_dvd_pow_iff_le_right hp.one_lt]

theorem IsPGroup.exists_orderOf_eq_exponent [Finite X] (hp : p.Prime) (hX : IsPGroup p X) :
    ∃ g : X, orderOf g = Monoid.exponent X := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hX.exists_exponent_eq_pow
  obtain ⟨g, hg⟩ := hp.exists_orderOf_eq_pow_factorization_exponent X
  exact ⟨g, by rw [hg, hn, Nat.Prime.factorization_pow hp]; simp⟩

end

end CFSG.FeitThompson
