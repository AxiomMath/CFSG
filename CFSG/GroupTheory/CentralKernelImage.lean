module

public import Mathlib.GroupTheory.Index

import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

theorem mem_centralizer_of_commute_of_conj {S G : Type*} [Group S] [Group G] {p : ℕ}
    (hZ : ∀ z ∈ Subgroup.center S, z ^ p = 1 → z = 1) {κ : S →* G}
    (hκ : κ.ker ≤ Subgroup.center S) {x : G} {t : S} (ht : t ^ p = 1)
    (hx : ∀ u, x * κ u * x⁻¹ = κ (t * u * t⁻¹)) {g : S} (hg : x * κ g = κ g * x) :
    g ∈ Subgroup.centralizer ({t} : Set S) := by
  have hconjκ : κ (t * g * t⁻¹) = κ g := by
    rw [← hx g, hg, mul_assoc, mul_inv_cancel, mul_one]
  set z : S := t * g * t⁻¹ * g⁻¹ with hzdef
  have hzker : z ∈ κ.ker := by
    rw [MonoidHom.mem_ker, hzdef, map_mul, map_inv, hconjκ, mul_inv_cancel]
  have hzcenter : z ∈ Subgroup.center S := hκ hzker
  have hconj : t * g * t⁻¹ = z * g := by
    rw [hzdef]
    group
  have hkey : ∀ k : ℕ, t ^ k * g * (t⁻¹) ^ k = z ^ k * g := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hzk : t * z ^ k * t⁻¹ = z ^ k := by
          have hmem : z ^ k ∈ Subgroup.center S :=
            Subgroup.pow_mem (K := Subgroup.center S) hzcenter k
          rw [Subgroup.mem_center_iff.mp hmem t, mul_assoc, mul_inv_cancel, mul_one]
        calc
          t ^ (k + 1) * g * (t⁻¹) ^ (k + 1)
              = t * (t ^ k * g * (t⁻¹) ^ k) * t⁻¹ := by
                  rw [pow_succ', pow_succ]; group
          _ = t * (z ^ k * g) * t⁻¹ := by rw [ih]
          _ = (t * z ^ k * t⁻¹) * (t * g * t⁻¹) := by group
          _ = z ^ k * (z * g) := by rw [hzk, hconj]
          _ = z ^ (k + 1) * g := by rw [pow_succ]; group
  have hgp : g = z ^ p * g := by
    have hti : (t⁻¹) ^ p = 1 := by rw [inv_pow, ht, inv_one]
    simpa [ht, hti] using hkey p
  have hzp : z ^ p = 1 := by
    have h := congrArg (fun w => w * g⁻¹) hgp
    simpa using h.symm
  have hz1 : z = 1 := hZ z hzcenter hzp
  have hconj' : t * g * t⁻¹ = g := by rw [hconj, hz1, one_mul]
  have hgt : t * g = g * t := by
    calc t * g = (t * g * t⁻¹) * t := by group
      _ = g * t := by rw [hconj']
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hgt.symm

theorem le_map_of_commutator_le {S G : Type*} [Group S] [Group G] {κ : S →* G}
    {C H : Subgroup S} (hCH : ⁅C, C⁆ ≤ H) {J : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (hJC : J ≤ C.map κ) : J ≤ H.map κ := by
  rw [← hJ]
  calc ⁅J, J⁆ ≤ ⁅C.map κ, C.map κ⁆ := Subgroup.commutator_mono hJC hJC
    _ = ⁅C, C⁆.map κ := (Subgroup.map_commutator (H₁ := C) (H₂ := C) κ).symm
    _ ≤ H.map κ := Subgroup.map_mono hCH

theorem ker_eq_bot_of_le_map_of_card_le {S G : Type*} [Group S] [Finite S] [Group G]
    {κ : S →* G} {H : Subgroup S} (hkerH : κ.ker ≤ H) {J : Subgroup G} (hJ : J ≤ H.map κ)
    (hcard : Nat.card H ≤ Nat.card J) : κ.ker = ⊥ := by
  have : Finite (H.map κ) :=
    Finite.of_surjective (κ.subgroupMap H) (κ.subgroupMap_surjective H)
  have hmul : Nat.card (κ.ker.subgroupOf H) * Nat.card (H.map κ) = Nat.card H := by
    rw [← Subgroup.relIndex_ker (K := H) κ]
    exact Subgroup.card_mul_index (H := κ.ker.subgroupOf H)
  have hsub : Nat.card (κ.ker.subgroupOf H) = Nat.card κ.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerH).toEquiv
  have hmul' : Nat.card κ.ker * Nat.card (H.map κ) = Nat.card H := by
    rw [← hsub, hmul]
  have hJH : Nat.card J ≤ Nat.card (H.map κ) := Subgroup.card_le_of_le hJ
  have hle : Nat.card κ.ker * Nat.card (H.map κ) ≤ Nat.card (H.map κ) := by
    rw [hmul']
    exact le_trans hcard hJH
  have hpos : 0 < Nat.card (H.map κ) := Finite.card_pos_iff.mpr ⟨1⟩
  have hk : Nat.card κ.ker ≤ 1 :=
    Nat.le_of_mul_le_mul_right (by simpa using hle) hpos
  have hk1 : Nat.card κ.ker = 1 := by
    have hposker : 0 < Nat.card κ.ker := Finite.card_pos_iff.mpr ⟨1⟩
    exact le_antisymm hk (by simpa using Nat.succ_le_of_lt hposker)
  exact Subgroup.eq_bot_of_card_eq (H := κ.ker) hk1

end CFSG.GroupTheory

end
