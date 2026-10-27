module

public import CFSG.Certificates.Kernel.PermCent.OrbGroup

public section

namespace CFSG.KC.SylowReps

open Subgroup

variable {G : Type*} [Group G]

theorem pow_factorization_eq {p k m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    p ^ (p ^ k * m).factorization p = p ^ k := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero k hp.ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hm, smul_eq_mul, mul_one, add_zero]

theorem isPGroup_zpowers {X : Type*} [Group X] {p k : ℕ} (hp : p.Prime) {x : X}
    (hx : x ^ (p ^ k) = 1) : IsPGroup p (zpowers x) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hx)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])

theorem forall_of_sylow (A T : Subgroup G) [Finite A] {p k m : ℕ} (hp : p.Prime) (hTA : T ≤ A)
    (hT : Nat.card T = p ^ k) (hA : Nat.card A = p ^ k * m) (hm : ¬ p ∣ m) (Φ : G → Prop)
    (hΦ : ∀ g ∈ A, ∀ x ∈ A, Φ (g * x * g⁻¹) → Φ x) (hTΦ : ∀ x ∈ T, Φ x) :
    ∀ x ∈ A, x ^ (p ^ k) = 1 → Φ x := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro x hxA hx
  let S : Subgroup A := T.subgroupOf A
  have hS : Nat.card S = p ^ (Nat.card A).factorization p := by
    rw [hA, pow_factorization_eq hp hm, ← hT]
    exact Nat.card_congr (subgroupOfEquivOfLe hTA).toEquiv
  have hx' : (⟨x, hxA⟩ : A) ^ (p ^ k) = 1 := Subtype.ext (by simpa using hx)
  obtain ⟨g, hg⟩ := CFSG.KC.OrbGroup.exists_conj_mem_of_card S hS (isPGroup_zpowers hp hx')
  have hmem : (g : G)⁻¹ * x * (g : G) ∈ T := by
    have := Subgroup.mem_subgroupOf.1 hg
    simpa using this
  refine hΦ (g : G)⁻¹ (A.inv_mem g.2) x hxA ?_
  rw [inv_inv]
  exact hTΦ _ hmem

theorem forall_of_sylow_reps (A T : Subgroup G) [Finite A] {p k m : ℕ} (hp : p.Prime)
    (hTA : T ≤ A) (hT : Nat.card T = p ^ k) (hA : Nat.card A = p ^ k * m) (hm : ¬ p ∣ m)
    (Φ : G → Prop) (hΦ : ∀ g ∈ A, ∀ x ∈ A, Φ (g * x * g⁻¹) → Φ x) (LT R : List G)
    (hLT : ∀ x ∈ T, x ∈ LT) (hR : ∀ r ∈ R, Φ r)
    (hcov : ∀ x ∈ LT, Φ x ∨ ∃ r ∈ R, ∃ g ∈ A, g * x = r * g) :
    ∀ x ∈ A, x ^ (p ^ k) = 1 → Φ x := by
  refine forall_of_sylow A T hp hTA hT hA hm Φ hΦ fun x hxT => ?_
  rcases hcov x (hLT x hxT) with h | ⟨r, hr, g, hg, e⟩
  · exact h
  · refine hΦ g hg x (hTA hxT) ?_
    rw [e, mul_inv_cancel_right]
    exact hR r hr

end CFSG.KC.SylowReps

end
