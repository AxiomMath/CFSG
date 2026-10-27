module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.CGT.T75O

theorem card_le_of_isPGroup_two {G : Type*} [Group G] [Finite G] {k m : ℕ} (hm : Odd m)
    (hG : Nat.card G = 2 ^ k * m) {K : Subgroup G} (hK : IsPGroup 2 K) : Nat.card K ≤ 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hK
  have hdvd : Nat.card K ∣ Nat.card G := Subgroup.card_subgroup_dvd_card K
  rw [hj, hG] at hdvd
  have hcop : Nat.Coprime (2 ^ j) m :=
    Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hm)
  have h2 : 2 ^ j ∣ 2 ^ k := hcop.dvd_of_dvd_mul_right hdvd
  rw [hj]
  exact Nat.le_of_dvd (by positivity) h2

theorem le_of_normalizes_of_card_le {G : Type*} [Group G] [Finite G] {T S : Subgroup G}
    (hT : IsPGroup 2 T) (hS : IsPGroup 2 S) (hST : S ≤ Subgroup.normalizer (T : Set G))
    (hmax : ∀ K : Subgroup G, IsPGroup 2 K → Nat.card K ≤ Nat.card S) : T ≤ S := by
  have hTS : IsPGroup 2 ↥(T ⊔ S) := hT.to_sup_of_normal_left' hS hST
  have h1 : Nat.card ↥(T ⊔ S) ≤ Nat.card S := hmax _ hTS
  have h2 : T ⊔ S = S := (Subgroup.eq_of_le_of_card_ge (le_sup_right : S ≤ T ⊔ S) h1).symm
  exact h2 ▸ le_sup_left

end CFSG.CGT.T75O
