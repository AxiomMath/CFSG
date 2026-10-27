module

public import CFSG.GroupTheory.SteinbergBKCoprimeHallConjugacy

public section

namespace CFSG.GroupTheory.SteinbergBK

theorem isHallSubgroup_sylow {H : Type*} [Group H] [Finite H] {q : ℕ} [Fact q.Prime]
    (P : Sylow q H) : IsHallSubgroup {r : Nat.Primes | (r : ℕ) = q} (P : Subgroup H) := by
  refine isHallSubgroup_of _ _ (fun r hr => ?_) (fun r hr hdvd => ?_)
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [hk] at hr
    exact (Nat.prime_dvd_prime_iff_eq r.2 Fact.out).mp (r.2.dvd_of_dvd_pow hr)
  · have hrq : (r : ℕ) = q := hr
    rw [hrq] at hdvd
    exact P.not_dvd_index hdvd

theorem solvable_coprime_invariant_sylow_conjugacy {A H : Type*} [Group A] [Group H] [Finite A]
    [Finite H] (hH : Group.IsSolvable H) (hcop : Nat.Coprime (Nat.card A) (Nat.card H))
    (ρ : A →* MulAut H) {q : ℕ} [Fact q.Prime] (Q R : Sylow q H)
    (hQ : ∀ a : A, ∀ x ∈ (Q : Subgroup H), ρ a x ∈ (Q : Subgroup H))
    (hR : ∀ a : A, ∀ x ∈ (R : Subgroup H), ρ a x ∈ (R : Subgroup H)) :
    ∃ c : H, (∀ a : A, ρ a c = c) ∧ (Q : Subgroup H).map (MulAut.conj c⁻¹).toMonoidHom = R := by
  let _ : MulDistribMulAction A H := MulDistribMulAction.compHom H ρ
  obtain ⟨c, hc, hcQ⟩ := solvable_coprime_invariant_hall_conjugacy (A := A) hH hcop _
    (isHallSubgroup_sylow Q) (isHallSubgroup_sylow R) hQ hR
  exact ⟨c, hc, hcQ⟩

end CFSG.GroupTheory.SteinbergBK
