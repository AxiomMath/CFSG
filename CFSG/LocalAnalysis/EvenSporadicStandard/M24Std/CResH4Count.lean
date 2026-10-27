module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG.EvenSporadicStandard.M24Std.CResH4

open Subgroup

variable {G H : Type*} [Group G] [Group H]

theorem natCard_map_mul_natCard_inf_ker (f : G →* H) (A : Subgroup G) :
    Nat.card (A.map f) * Nat.card ↥(A ⊓ f.ker) = Nat.card A := by
  have h := Subgroup.card_ker_mul_card_range (f.domRestrict A)
  rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict] at h
  have e : Nat.card (f.ker.subgroupOf A) = Nat.card ↥(A ⊓ f.ker) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective (K := f.ker.subgroupOf A),
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [e] at h
  rw [mul_comm]
  exact h

theorem natCard_comap_eq {P X : Type*} [Group P] [Group X] (ρ : P →* X) (N : Subgroup X)
    (hN : N ≤ ρ.range) : Nat.card (N.comap ρ) = Nat.card N * Nat.card ρ.ker := by
  have h := natCard_map_mul_natCard_inf_ker ρ (N.comap ρ)
  rw [Subgroup.map_comap_eq_self hN, inf_eq_right.2 (fun k hk => by
    rw [mem_comap, MonoidHom.mem_ker.1 hk]; exact N.one_mem)] at h
  exact h.symm

theorem card_eq_or_card_eq_three_mul_card_map_comap {P X Q : Type*} [Group P] [Group X]
    [Group Q] (ρ : P →* X) (φ : P →* Q) (hker : ρ.ker ≤ φ.ker) (hk : Nat.card φ.ker = 3)
    (N : Subgroup X) (hN : N ≤ ρ.range) :
    Nat.card N = Nat.card ((N.comap ρ).map φ) ∨ Nat.card N = 3 * Nat.card ((N.comap ρ).map φ) := by
  have h1 := natCard_comap_eq ρ N hN
  have h2 := natCard_map_mul_natCard_inf_ker φ (N.comap ρ)
  have hle : ρ.ker ≤ N.comap ρ ⊓ φ.ker := le_inf (fun k hk => by
    rw [mem_comap, MonoidHom.mem_ker.1 hk]; exact N.one_mem) hker
  have hd1 : Nat.card ρ.ker ∣ Nat.card ↥(N.comap ρ ⊓ φ.ker) := Subgroup.card_dvd_of_le hle
  have hd2 : Nat.card ↥(N.comap ρ ⊓ φ.ker) ∣ 3 := hk ▸ Subgroup.card_dvd_of_le inf_le_right
  have hp : (3 : ℕ).Prime := Nat.prime_three
  rcases (Nat.dvd_prime hp).1 hd2 with hb | hb
  · rw [hb] at hd1 h2
    rw [Nat.dvd_one.1 hd1, mul_one] at h1
    left
    omega
  · rw [hb] at hd1 h2
    rcases (Nat.dvd_prime hp).1 hd1 with ha | ha
    · rw [ha, mul_one] at h1
      right
      omega
    · rw [ha] at h1
      left
      omega

end CFSG.EvenSporadicStandard.M24Std.CResH4
