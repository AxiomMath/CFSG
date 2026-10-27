module

public import CFSG.GroupTheory.SylowPQMaximal.Defs
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise

variable {p q : ℕ} {Y : Type*} [Group Y]

private theorem isPGroup_of_forall_prime_dvd_eq {G : Type*} [Group G] [Finite G] {p : ℕ}
    (h : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r = p) : IsPGroup p G := by
  have hcard : Nat.card G = p ^ (Nat.card G).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun hr hd => h _ hr hd)
  exact IsPGroup.of_card hcard

theorem sylowPQMaximal_of_not_dvd [Finite Y] [Fact p.Prime] (hq : ¬ q ∣ Nat.card Y) :
    SylowPQMaximal p q Y := by
  intro P H hPH hH
  refine isPGroup_of_forall_prime_dvd_eq (p := p) fun r hr hrH => ?_
  have hqH : ¬ q ∣ Nat.card H := fun h => hq (h.trans (Subgroup.card_subgroup_dvd_card H))
  rcases (isPiSubgroup_pair_iff.mp hH) r hr hrH with h | h
  · exact h
  · exact absurd (h ▸ hrH) hqH

theorem card_sup_eq_mul_of_mul_eq_mul [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {R P : Subgroup Y} (hR : IsPGroup q R) (hP : IsPGroup p P)
    (hRP : (R : Set Y) * (P : Set Y) = (P : Set Y) * (R : Set Y)) :
    Nat.card (R ⊔ P : Subgroup Y) = Nat.card R * Nat.card P := by
  have hd : R ⊓ P = ⊥ := by
    rw [← disjoint_iff]
    exact IsPGroup.disjoint_of_ne q p hpq.symm R P hR hP
  exact CFSG.Quasithin.H23P4.card_eq_mul_of_coe_eq_mul
    (CFSG.Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hRP) hd

theorem SylowPQMaximal.eq_bot_of_mul_eq_mul [Finite Y] [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (h : SylowPQMaximal p q Y) (P : Sylow p Y) {R : Subgroup Y}
    (hR : IsPGroup q R) (hRP : (R : Set Y) * (P : Set Y) = (P : Set Y) * (R : Set Y)) :
    R = ⊥ := by
  have hcard : Nat.card (R ⊔ P : Subgroup Y) = Nat.card R * Nat.card P :=
    card_sup_eq_mul_of_mul_eq_mul hpq hR P.isPGroup' hRP
  obtain ⟨a, ha⟩ := hR.exists_card_eq
  obtain ⟨b, hb⟩ := (P.isPGroup' : IsPGroup p (P : Subgroup Y)).exists_card_eq
  have hpi : IsPiSubgroup {r : Nat.Primes | (r : ℕ) = p ∨ (r : ℕ) = q}
      (R ⊔ P : Subgroup Y) := by
    rw [isPiSubgroup_pair_iff]
    intro r hr hrH
    rw [hcard, ha, hb] at hrH
    rcases (hr.dvd_mul.mp hrH) with h | h
    · refine Or.inr ?_
      exact (Nat.prime_dvd_prime_iff_eq hr (Fact.out : q.Prime)).mp (hr.dvd_of_dvd_pow h)
    · refine Or.inl ?_
      exact (Nat.prime_dvd_prime_iff_eq hr (Fact.out : p.Prime)).mp (hr.dvd_of_dvd_pow h)
  have hRp : IsPGroup p (R ⊔ P : Subgroup Y) :=
    h P (R ⊔ P) le_sup_right hpi
  have hRp' : IsPGroup p R := hRp.to_le le_sup_left
  have hd : Disjoint R R := IsPGroup.disjoint_of_ne p q hpq R R hRp' hR
  exact disjoint_self.mp hd

end CFSG.GroupTheory
