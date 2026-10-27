module

public import Mathlib.Tactic.Group
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem exists_invol_cent_nine {G : Type} [Group G] [Finite G] {L : Subgroup G} {β ξ' : G}
    (hβL : β ∈ L) (hβ3 : orderOf β = 3)
    (hD : Nat.card ↥(L ⊓ centralizer ({β} : Set G)) = 1080)
    (hξL : ξ' ∈ L) (hξβ : ξ' * β * ξ'⁻¹ = β⁻¹)
    (hcomm : ∀ x ∈ L ⊓ centralizer ({β} : Set G), ξ' * x * ξ'⁻¹ * x⁻¹ ∈ zpowers β) :
    ∃ ι ∈ L, ι * ι = 1 ∧ ι ≠ 1 ∧ 9 ∣ Nat.card ↥(L ⊓ centralizer ({ι} : Set G)) := by
  obtain ⟨D, hD_eq⟩ : ∃ D : Subgroup G, D = L ⊓ centralizer ({β} : Set G) := ⟨_, rfl⟩
  have hDcard : Nat.card ↥D = 1080 := by rw [hD_eq]; exact hD
  have memD : ∀ x : G, x ∈ D ↔ x ∈ L ∧ x * β = β * x := fun x => by
    rw [hD_eq, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hcommD : ∀ x ∈ D, ξ' * x * ξ'⁻¹ * x⁻¹ ∈ zpowers β := by
    rw [hD_eq]; exact hcomm
  have hcomm_zp : ∀ x ∈ D, ∀ b ∈ zpowers β, x * b = b * x := by
    intro x hx b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hxβ : Commute x β := ((memD x).1 hx).2
    exact hxβ.zpow_right k
  have hmul : ∀ x y : G, x ∈ D → y ∈ D →
      ξ' * (x * y) * ξ'⁻¹ * (x * y)⁻¹ = (ξ' * x * ξ'⁻¹ * x⁻¹) * (ξ' * y * ξ'⁻¹ * y⁻¹) := by
    intro x y hx hy
    have hxb := hcomm_zp x hx _ (hcommD y hy)
    calc ξ' * (x * y) * ξ'⁻¹ * (x * y)⁻¹
        = (ξ' * x * ξ'⁻¹ * x⁻¹) * (x * (ξ' * y * ξ'⁻¹ * y⁻¹) * x⁻¹) := by group
      _ = (ξ' * x * ξ'⁻¹ * x⁻¹) * (ξ' * y * ξ'⁻¹ * y⁻¹) := by rw [hxb]; group
  let φ : D →* zpowers β :=
    MonoidHom.mk' (fun x => ⟨ξ' * (x : G) * ξ'⁻¹ * (x : G)⁻¹, hcommD _ x.2⟩)
      (fun x y => Subtype.ext (hmul (x : G) (y : G) x.2 y.2))
  have hker : ∀ x : D, φ x = 1 → ξ' * (x : G) = (x : G) * ξ' := by
    intro x hx
    have h1x : ξ' * (x : G) * ξ'⁻¹ * (x : G)⁻¹ = 1 := congrArg Subtype.val hx
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1x)
  have hprod : Nat.card φ.ker * φ.ker.index = 1080 := by
    rw [Subgroup.card_mul_index, hDcard]
  have hr : Nat.card φ.range ∣ 3 := by
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rwa [Nat.card_zpowers, hβ3] at h
  have hidx : φ.ker.index = Nat.card φ.range := Subgroup.index_ker φ
  have h9 : 9 ∣ Nat.card φ.ker := by
    rw [hidx] at hprod
    rcases (Nat.dvd_prime Nat.prime_three).1 hr with h | h <;> rw [h] at hprod <;> omega
  have h1 : ξ' * β = β⁻¹ * ξ' := mul_inv_eq_iff_eq_mul.1 hξβ
  have h2 : ξ' * β⁻¹ = β * ξ' := by
    have h3 : ξ' * β⁻¹ * ξ'⁻¹ = β := by
      calc ξ' * β⁻¹ * ξ'⁻¹ = (ξ' * β * ξ'⁻¹)⁻¹ := by group
        _ = β := by rw [hξβ, inv_inv]
    exact mul_inv_eq_iff_eq_mul.1 h3
  have hsq : ξ' ^ 2 * β = β * ξ' ^ 2 := by
    calc ξ' ^ 2 * β = ξ' * (ξ' * β) := by rw [sq, mul_assoc]
      _ = ξ' * (β⁻¹ * ξ') := by rw [h1]
      _ = (ξ' * β⁻¹) * ξ' := by rw [mul_assoc]
      _ = (β * ξ') * ξ' := by rw [h2]
      _ = β * ξ' ^ 2 := by rw [sq, mul_assoc]
  have hneven : Even (orderOf ξ') := by
    by_contra hodd
    obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.1 hodd
    have hξ_eq : ξ' = (ξ' ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = orderOf ξ' + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    have hc : Commute ξ' β := by
      have hc' : Commute ((ξ' ^ 2) ^ (j + 1)) β := (show Commute (ξ' ^ 2) β from hsq).pow_left (j + 1)
      rw [← hξ_eq] at hc'
      exact hc'
    have hinv : β⁻¹ = β := by
      have h4 : β⁻¹ * ξ' = β * ξ' := by rw [← h1]; exact hc
      exact mul_right_cancel h4
    have hββ : β * β = 1 := by
      calc β * β = β * β⁻¹ := by rw [hinv]
        _ = 1 := mul_inv_cancel β
    have hdvd : orderOf β ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hββ)
    rw [hβ3] at hdvd
    norm_num at hdvd
  have hpos : 0 < orderOf ξ' := orderOf_pos ξ'
  obtain ⟨m, hm⟩ := hneven
  have hmpos : 0 < m := by omega
  refine ⟨ξ' ^ m, pow_mem hξL m, ?_, ?_, ?_⟩
  · rw [← pow_add, ← hm, pow_orderOf_eq_one]
  · intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    have hle := Nat.le_of_dvd hmpos hd
    omega
  ·
    have hKle : φ.ker.map D.subtype ≤ L ⊓ centralizer ({ξ' ^ m} : Set G) := by
      rintro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_inf.2 ⟨((memD (x : G)).1 x.2).1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have hcx : Commute ξ' (x : G) := hker x (MonoidHom.mem_ker.1 hx)
      exact (hcx.pow_left m).symm
    have hKcard : Nat.card ↥(φ.ker.map D.subtype) = Nat.card ↥φ.ker :=
      Subgroup.card_map_of_injective Subtype.val_injective
    have hdvd := Subgroup.card_dvd_of_le hKle
    rw [hKcard] at hdvd
    exact dvd_trans h9 hdvd

end CFSG.EvenSporadicStandard.Fin76b
