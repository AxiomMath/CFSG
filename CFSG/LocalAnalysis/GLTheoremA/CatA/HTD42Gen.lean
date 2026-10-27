module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264tTD42Aux

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HTD42

open CFSG.Open

theorem pow_three_zpow_eq_one {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) (k : ℤ) :
    (x ^ k) ^ 3 = 1 := by
  have key : (x ^ k) ^ ((3 : ℕ) : ℤ) = (x ^ ((3 : ℕ) : ℤ)) ^ k := by
    rw [← zpow_mul, ← zpow_mul, mul_comm]
  have h3 : x ^ ((3 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact hx
  rw [← zpow_natCast, key, h3, one_zpow]

theorem sup_zpowers_card_nine {G : Type*} [Group G] [Finite G] {a b : G}
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1)
    (hab : a * b = b * a) (hb : b ∉ Subgroup.zpowers a) :
    Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) = 9 ∧
      IsElemAbelian 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hb (Subgroup.one_mem _)
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hcA : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hoa]
  have hcB : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hob]
  have hcomm : Commute b a := hab.symm
  have hBN : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.zpowers_le]
    apply mem_normalizer_of_comm
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hcomm.zpow_right k).eq
  have hmul := card_sup_mul_card_inf_of_le_normalizer hBN
  have hinf : Nat.card (Subgroup.zpowers a ⊓ Subgroup.zpowers b : Subgroup G) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers a ⊓ Subgroup.zpowers b : Subgroup G) ∣ 3 := by
      rw [← hcA]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact h
    · exfalso
      have hle : Subgroup.zpowers a ⊓ Subgroup.zpowers b = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hcA])
      have hab' : Subgroup.zpowers a ≤ Subgroup.zpowers b := hle ▸ inf_le_right
      have heq : Subgroup.zpowers a = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge hab' (by rw [hcA, hcB])
      exact hb (heq ▸ Subgroup.mem_zpowers b)
  have hcard : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) = 9 := by
    rw [hinf, mul_one, hcA, hcB] at hmul
    omega
  have hcAB : ∀ h ∈ Subgroup.zpowers a, ∀ l ∈ Subgroup.zpowers b, h * l = l * h := by
    intro h hh l hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
    exact ((show Commute a b from hab).zpow_zpow k m).eq
  refine ⟨hcard, ?_, ?_⟩
  ·
    have hA : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((Commute.refl a).zpow_zpow k l).eq
    have hB : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((Commute.refl b).zpow_zpow k l).eq
    exact isMulCommutative_sup_of_commute hA hB hcAB
  ·
    have hpowA : ∀ x ∈ Subgroup.zpowers a, x ^ 3 = 1 := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact pow_three_zpow_eq_one ha3 k
    have hpowB : ∀ x ∈ Subgroup.zpowers b, x ^ 3 = 1 := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact pow_three_zpow_eq_one hb3 k
    intro x hx
    obtain ⟨h1, hh1, l1, hl1, rfl⟩ := mem_sup_exists_of_commute hcAB hx
    have hcom : Commute h1 l1 := hcAB h1 hh1 l1 hl1
    rw [hcom.mul_pow, hpowA h1 hh1, hpowB l1 hl1, one_mul]

theorem fixed_of_sup_zpowers {G : Type*} [Group G] {a b : G} (hab : a * b = b * a)
    (φ : G →* G) (ha : φ a = a) (hb : φ b = b) :
    ∀ x ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G), φ x = x := by
  have hcAB : ∀ h ∈ Subgroup.zpowers a, ∀ l ∈ Subgroup.zpowers b, h * l = l * h := by
    intro h hh l hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
    exact ((show Commute a b from hab).zpow_zpow k m).eq
  intro x hx
  obtain ⟨h1, hh1, l1, hl1, rfl⟩ := mem_sup_exists_of_commute hcAB hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh1
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl1
  rw [map_mul, map_zpow, map_zpow, ha, hb]

end CFSG.LocalAnalysis.GLTheoremA.HTD42
