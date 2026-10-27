module

public import Mathlib.GroupTheory.PGroup
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X]

theorem isCyclic_of_disjoint_of_isCyclic_quotient (H : Subgroup X) [H.Normal]
    [IsCyclic (X ⧸ H)] {P : Subgroup X} (h : Disjoint H P) : IsCyclic P := by
  refine isCyclic_of_injective ((QuotientGroup.mk' H).comp P.subtype) ?_
  intro x y hxy
  have h1 : (x : X)⁻¹ * (y : X) ∈ H := QuotientGroup.eq.mp (by simpa using hxy)
  have h2 : (x : X)⁻¹ * (y : X) ∈ P := P.mul_mem (P.inv_mem x.2) y.2
  exact Subtype.ext (inv_mul_eq_one.mp (Subgroup.disjoint_def.mp h h1 h2))

theorem le_of_isPGroup_of_not_isCyclic {H : Subgroup X} [H.Normal]
    (hcop : (Nat.card H).Coprime H.index) [IsCyclic (X ⧸ H)] {p : ℕ} [Fact p.Prime]
    {P : Subgroup X} (hP : IsPGroup p P) (hPnc : ¬ IsCyclic P) : P ≤ H :=
  (hP.le_or_disjoint_of_coprime hcop).resolve_right fun h =>
    hPnc (isCyclic_of_disjoint_of_isCyclic_quotient H h)

theorem le_of_natCard_eq_prime_pow_of_not_isCyclic {H : Subgroup X} [H.Normal]
    (hcop : (Nat.card H).Coprime H.index) [IsCyclic (X ⧸ H)] {p : ℕ} (hp : p.Prime)
    {P : Subgroup X} {a : ℕ} (hPcard : Nat.card P = p ^ a) (hPnc : ¬ IsCyclic P) : P ≤ H :=
  haveI : Fact p.Prime := ⟨hp⟩
  le_of_isPGroup_of_not_isCyclic hcop (IsPGroup.of_card hPcard) hPnc

theorem le_of_natCard_eq_prime_pow_of_not_isCyclic' {H : Subgroup X} [H.Normal]
    (hcop : (Nat.card H).Coprime (Nat.card (Set.range fun g : X => g • (H : Set X))))
    [IsCyclic (X ⧸ H)] {p : ℕ} (hp : p.Prime) {P : Subgroup X} {a : ℕ}
    (hPcard : Nat.card P = p ^ a) (hPnc : ¬ IsCyclic P) : P ≤ H :=
  le_of_natCard_eq_prime_pow_of_not_isCyclic
    (by rwa [natCard_range_leftCoset] at hcop) hp hPcard hPnc

end

end CFSG.FeitThompson
