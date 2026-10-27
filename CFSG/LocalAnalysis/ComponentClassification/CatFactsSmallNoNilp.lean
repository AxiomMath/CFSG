module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallModel

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups Subgroup

theorem mem_of_pow_two_pow_mem {H : Type*} [Group H] {N : Subgroup H} {x : H} {m k : ℕ}
    (hm : Odd m) (hx : x ^ m = 1) (hk : x ^ 2 ^ k ∈ N) : x ∈ N := by
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcop hm0
  have hxe : (x ^ 2 ^ k) ^ j = x := by
    rw [← pow_mul, pow_eq_pow_mod _ hx, hj, ← pow_eq_pow_mod _ hx, pow_one]
  rw [← hxe]
  exact pow_mem hk j

variable {K G : Type*} [Group K] [Group G] (M : AutModel K G)

theorem not_two_nilpotent_of_witness [Finite K] {m : ℕ} (hm : Odd m)
    (hK : ∀ d : ℕ, d ∣ Nat.card K → Odd d → d ∣ m) (θ : MulAut K) {x₁ x₂ : G}
    (h₁ : x₁ ∈ M.P) (h₂ : x₂ ∈ M.P) (hc₁ : x₁ * (M.Φ θ : G) = (M.Φ θ : G) * x₁)
    (hc₂ : x₂ * (M.Φ θ : G) = (M.Φ θ : G) * x₂) (hx₁ : x₁ ^ m = 1) (hx₂ : x₂ ^ m = 1)
    (h12 : (x₁ * x₂) ^ m ≠ 1) :
    ¬ ∃ N : Subgroup K, N ≤ GSThmB.Eight.fixSubgroup θ ∧
      (N.subgroupOf (GSThmB.Eight.fixSubgroup θ)).Normal ∧ Odd (Nat.card N) ∧
      ∀ y ∈ GSThmB.Eight.fixSubgroup θ, ∃ k : ℕ, y ^ 2 ^ k ∈ N := by
  rintro ⟨N, hNle, -, hNodd, hN2⟩
  set k₁ := M.e.symm ⟨x₁, h₁⟩
  set k₂ := M.e.symm ⟨x₂, h₂⟩
  have he₁ : modelEmb M k₁ = x₁ := modelEmb_symm M x₁ h₁
  have he₂ : modelEmb M k₂ = x₂ := modelEmb_symm M x₂ h₂
  have hfix₁ : k₁ ∈ GSThmB.Eight.fixSubgroup θ := by
    rw [GSThmB.Eight.mem_fixSubgroup, apply_eq_self_iff M θ, he₁]
    exact hc₁.symm
  have hfix₂ : k₂ ∈ GSThmB.Eight.fixSubgroup θ := by
    rw [GSThmB.Eight.mem_fixSubgroup, apply_eq_self_iff M θ, he₂]
    exact hc₂.symm
  have hk₁m : k₁ ^ m = 1 := modelEmb_injective M (by rw [map_pow, he₁, hx₁, map_one])
  have hk₂m : k₂ ^ m = 1 := modelEmb_injective M (by rw [map_pow, he₂, hx₂, map_one])
  obtain ⟨a, ha⟩ := hN2 k₁ hfix₁
  obtain ⟨b, hb⟩ := hN2 k₂ hfix₂
  have hN₁ := mem_of_pow_two_pow_mem hm hk₁m ha
  have hN₂ := mem_of_pow_two_pow_mem hm hk₂m hb
  have hmul : k₁ * k₂ ∈ N := mul_mem hN₁ hN₂
  have hord : orderOf (k₁ * k₂) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hmul
  have hNK : Nat.card N ∣ Nat.card K := card_subgroup_dvd_card N
  have hNm : Nat.card N ∣ m := hK _ hNK hNodd
  have hpow : (k₁ * k₂) ^ m = 1 := orderOf_dvd_iff_pow_eq_one.1 (hord.trans hNm)
  apply h12
  rw [← he₁, ← he₂, ← map_mul, ← map_pow, hpow, map_one]

end CFSG.ComponentClassification.CatFactsSmall
