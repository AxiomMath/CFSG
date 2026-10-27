module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem card_le_mul_card_cent {G : Type*} [Group G] [Finite G] (E Y : Subgroup G)
    (hY2 : IsPGroup 2 Y) (hYN : Y ≤ normalizer (E : Set G)) (haut : Nat.card (MulAut ↥E) = 1920) :
    Nat.card ↥Y ≤ 128 * Nat.card ↥(Y ⊓ centralizer (E : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : ↥Y →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hYN)
  have hrange2 : IsPGroup 2 ρ.range := hY2.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := hrange2.exists_card_eq
  have hdvd : Nat.card ρ.range ∣ 1920 := haut ▸ Subgroup.card_subgroup_dvd_card _
  have hn7 : n ≤ 7 := by
    by_contra h
    have h8 : 2 ^ 8 ∣ 1920 := (Nat.pow_dvd_pow 2 (not_le.1 h)).trans (hn ▸ hdvd)
    norm_num at h8
  have hrange_le : Nat.card ρ.range ≤ 128 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hn7
      _ = 128 := by norm_num
  have hker : ρ.ker = (Y ⊓ centralizer (E : Set G)).subgroupOf Y := by
    ext y
    simp only [MonoidHom.mem_ker, mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨y.2, fun e he => ?_⟩
      have h1 := congrArg (fun φ : MulAut ↥E => (φ ⟨e, he⟩ : G)) h
      have h2 : (y : G) * e * (y : G)⁻¹ = e := h1
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    · rintro ⟨-, h⟩
      refine MulEquiv.ext fun e => Subtype.ext ?_
      show (y : G) * e * (y : G)⁻¹ = e
      exact mul_inv_eq_iff_eq_mul.2 (h e e.2).symm
  have hkcard : Nat.card ρ.ker = Nat.card ↥(Y ⊓ centralizer (E : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmain := Subgroup.card_mul_index ρ.ker
  rw [Subgroup.index_ker, hkcard] at hmain
  rw [← hmain]
  calc Nat.card ↥(Y ⊓ centralizer (E : Set G)) * Nat.card ρ.range
      ≤ Nat.card ↥(Y ⊓ centralizer (E : Set G)) * 128 := Nat.mul_le_mul_left _ hrange_le
    _ = 128 * Nat.card ↥(Y ⊓ centralizer (E : Set G)) := mul_comm _ _

end CFSG.EvenSporadicStandard.Fin76b
