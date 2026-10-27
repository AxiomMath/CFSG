module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem card_mul_le_of_inf_eq_bot {A B C : Subgroup G} (hA : A ≤ C) (hB : B ≤ C)
    (hAB : A ⊓ B = ⊥) : Nat.card A * Nat.card B ≤ Nat.card C := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : A × B => (⟨p.1.1 * p.2.1, C.mul_mem (hA p.1.2) (hB p.2.2)⟩ : C)) ?_
  rintro ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩⟩ ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩⟩ h
  have hmul : (a1 : G) * b1 = a2 * b2 := congrArg Subtype.val h
  have key : a2⁻¹ * a1 = b2 * b1⁻¹ := by
    have hh := congrArg (fun x : G => a2⁻¹ * x * b1⁻¹) hmul
    simpa [mul_assoc] using hh
  have hmemA : a2⁻¹ * a1 ∈ A := A.mul_mem (A.inv_mem ha2) ha1
  have hmemB : a2⁻¹ * a1 ∈ B := by rw [key]; exact B.mul_mem hb2 (B.inv_mem hb1)
  have hone : a2⁻¹ * a1 = 1 := by
    have : a2⁻¹ * a1 ∈ (⊥ : Subgroup G) := by rw [← hAB]; exact ⟨hmemA, hmemB⟩
    simpa using this
  have haeq : a1 = a2 := by
    have hh := congrArg (fun x : G => a2 * x) hone
    simpa [mul_assoc] using hh
  have hone' : b2 * b1⁻¹ = 1 := key ▸ hone
  have hbeq : b1 = b2 := by
    have hh := congrArg (fun x : G => x * b1) hone'
    simpa [mul_assoc] using hh.symm
  exact Prod.ext (Subtype.ext haeq) (Subtype.ext hbeq)

theorem isPGroup_two_of_normal {K N : Subgroup G} {n : ℕ} (hK : Nat.card K = 3 * 2 ^ n)
    (hNK : N ≤ K) (hN : ∀ k ∈ K, ∀ x ∈ N, k * x * k⁻¹ ∈ N) {ρ : G} (hρK : ρ ∈ K)
    (hρ3 : ρ ^ 3 = 1) (hρ1 : ρ ≠ 1) (hρN : ρ ∉ N) : IsPGroup 2 N := by
  haveI hN'norm : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff hNK).mpr (fun h k hh hk => hN k hk h hh)
  let ρ' : K := ⟨ρ, hρK⟩
  have hρ'3 : ρ' ^ 3 = 1 := Subtype.ext (by simpa using hρ3)
  have hρ'N : ρ' ∉ N.subgroupOf K := fun h => hρN (Subgroup.mem_subgroupOf.mp h)
  have hq3 : (QuotientGroup.mk' (N.subgroupOf K) ρ') ^ 3 = 1 := by
    rw [← map_pow, hρ'3, map_one]
  have hq1 : QuotientGroup.mk' (N.subgroupOf K) ρ' ≠ 1 := by
    intro h
    exact hρ'N ((QuotientGroup.eq_one_iff ρ').mp h)
  have horder : orderOf (QuotientGroup.mk' (N.subgroupOf K) ρ') = 3 :=
    orderOf_eq_prime hq3 hq1
  have h3dvd : 3 ∣ (N.subgroupOf K).index := by
    rw [Subgroup.index_eq_card]
    exact horder ▸ orderOf_dvd_natCard _
  obtain ⟨m, hm⟩ := h3dvd
  have hcardN' : Nat.card (N.subgroupOf K) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK)
  have hmul : (N.subgroupOf K).index * Nat.card (N.subgroupOf K) = Nat.card ↥K :=
    Subgroup.index_mul_card _
  rw [hm, hcardN', hK] at hmul
  have hmul' : m * Nat.card N = 2 ^ n := by
    have hh : 3 * (m * Nat.card N) = 3 * 2 ^ n := by
      simpa [mul_assoc] using hmul
    exact Nat.mul_left_cancel (by norm_num) hh
  exact IsPGroup.of_card_dvd_pow (p := 2) (n := n)
    ⟨m, by rw [mul_comm]; exact hmul'.symm⟩

theorem le_of_normal_isPGroup {K N 𝒮 : Subgroup G} (hNK : N ≤ K)
    (hN : ∀ k ∈ K, ∀ x ∈ N, k * x * k⁻¹ ∈ N) (hN2 : IsPGroup 2 N) (h𝒮K : 𝒮 ≤ K)
    (h𝒮 : IsPGroup 2 𝒮) (hidx : ¬ 2 ∣ 𝒮.relIndex K) : N ≤ 𝒮 := by
  haveI hN'norm : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff hNK).mpr (fun h k hh hk => hN k hk h hh)
  have hN2' : IsPGroup 2 (N.subgroupOf K) := hN2.comap_subtype
  have h𝒮2' : IsPGroup 2 (𝒮.subgroupOf K) := h𝒮.comap_subtype
  have hidx' : ¬ 2 ∣ (𝒮.subgroupOf K).index := hidx
  have hle' : N.subgroupOf K ≤ 𝒮.subgroupOf K := by
    simpa using hN2'.le_sylow_of_normal (h𝒮2'.toSylow hidx')
  intro x hx
  have hx' : (⟨x, hNK hx⟩ : K) ∈ N.subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
  have hS : (↑(⟨x, hNK hx⟩ : K) : G) ∈ 𝒮 := Subgroup.mem_subgroupOf.mp (hle' hx')
  simpa using hS

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
