module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.QuasithinUnique.Id2519.Tab.Class8

theorem two_pow_le_of_dvd {k e u : ℕ} (hu : ¬ 2 ∣ u) (h : 2 ^ k ∣ 2 ^ e * u) : 2 ^ k ≤ 2 ^ e := by
  have hcop : Nat.Coprime (2 ^ k) u :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hu)
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right h)

theorem card_le_of_injective {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (hA : IsPGroup 2 A) (f : A →* B) (hf : Function.Injective f) {e u : ℕ} (hu : ¬ 2 ∣ u)
    (hB : Nat.card B = 2 ^ e * u) : Nat.card A ≤ 2 ^ e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hA
  have hd := Subgroup.card_dvd_of_injective f hf
  rw [hk, hB] at hd
  rw [hk]
  exact two_pow_le_of_dvd hu hd

theorem pow_le_card_isSylowTwoOf {G : Type} [Group G] [Finite G] {X P : Subgroup G}
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf P X) {m v : ℕ} (hX : Nat.card X = 2 ^ m * v) :
    2 ^ m ≤ Nat.card P := by
  have h := Subgroup.relIndex_mul_card (H := P) (K := X)
  rw [inf_of_le_left hP.1] at h
  have hodd : ¬ 2 ∣ P.relIndex X := hP.2.2
  have hcop : Nat.Coprime (2 ^ m) (P.relIndex X) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have hdvd : 2 ^ m ∣ P.relIndex X * Nat.card P := by rw [h, hX]; exact dvd_mul_right _ _
  exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_left hdvd)

theorem eight_le_relIndex {G : Type} [Group G] [Finite G] {X P : Subgroup G} (C : Subgroup G)
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf P X) {B : Type} [Group B] [Finite B]
    (f : ↥(C ⊓ P) →* B) (hf : Function.Injective f) {e u : ℕ} (hu : ¬ 2 ∣ u)
    (hB : Nat.card B = 2 ^ e * u) {m v : ℕ} (hX : Nat.card X = 2 ^ m * v)
    (hem : 8 * 2 ^ e ≤ 2 ^ m) : 8 ≤ C.relIndex P := by
  have hA : IsPGroup 2 ↥(C ⊓ P) :=
    hP.2.1.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
  have hb := card_le_of_injective hA f hf hu hB
  have hP2 := pow_le_card_isSylowTwoOf hP hX
  have h := Subgroup.relIndex_mul_card (H := C) (K := P)
  have hpos : 0 < Nat.card ↥(C ⊓ P) := Nat.card_pos
  have h8 : 8 * Nat.card ↥(C ⊓ P) ≤ C.relIndex P * Nat.card ↥(C ⊓ P) := by
    rw [h]
    calc 8 * Nat.card ↥(C ⊓ P) ≤ 8 * 2 ^ e := Nat.mul_le_mul_left 8 hb
      _ ≤ 2 ^ m := hem
      _ ≤ Nat.card P := hP2
  exact Nat.le_of_mul_le_mul_right h8 hpos

end CFSG.QuasithinUnique.Id2519.Tab.Class8
