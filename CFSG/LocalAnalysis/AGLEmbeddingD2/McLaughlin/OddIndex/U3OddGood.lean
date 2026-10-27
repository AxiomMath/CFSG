module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddBad
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddNormalizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddModel

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

@[expose] def U3OddGood (F : Type) [Field F] [Finite F] (p f : ℕ) [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) : Prop :=
  ∀ ω : Fˣ, orderOf ω = 3 → ∀ W : Subgroup (SU (unitaryInvolution F p f) 3), normA0 hF ω ≤ W →
    (∃ x ∈ W, x * zSU hF = zSU hF * x ∧ x ∉ normA0 hF ω) → ¬ 2 ∣ W.index

theorem badCase_model (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) {ω : Fˣ} (hω : orderOf ω = 3)
    (hq3 : (p ^ f) % 3 = 1) (hq4 : (p ^ f) % 4 = 3) {ν : Fˣ} (hν2 : ν ^ ((p ^ f + 1) / 2) = -1)
    (hνq : (ν ^ (p ^ f))⁻¹ = ν) {W : Subgroup (SU (unitaryInvolution F p f) 3)}
    (hNW : normA0 hF ω ≤ W)
    (hbad : ∀ x ∈ W, x * zSU hF = zSU hF * x → x ∈ normA0 hF ω) :
    BadCase W (normA0 hF ω) (tSU hF).range (zSU hF) (tSU hF ν) (tSU hF ω) ((p ^ f + 1) / 4) where
  le_W := hNW
  le_N := range_tSU_le_normA0 hF hω hq3
  isCyclic := isCyclic_range_tSU hF
  relIndex_eq := relIndex_range_normA0 hF hω hq3
  z_mul_self := zSU_mul_self hF
  z_ne_one := zSU_ne_one hF hp2
  centralizer_z := hbad
  p₀_mem := range_tSU_le_normA0 hF hω hq3 ⟨ν, rfl⟩
  p₀_central := fun x hx => tSU_comm_normA0 hF hω hq3 hνq x hx
  pow_eq := by
    have hk : 2 * ((p ^ f + 1) / 4) = (p ^ f + 1) / 2 := by omega
    rw [zSU, ← map_mul, ← map_pow, ← pow_two, ← pow_mul, hk, hν2]
  orderOf_a := orderOf_tSU hF hω
  centralizer_a := fun x _ hx => by
    rw [← centralizer_a0 hF hω hq3]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hx
  inverts_a := fun x _ hx => (mem_normalizer_zpowers_iff (orderOf_tSU hF hω)).mpr (Or.inr hx)

theorem u3OddCore_of_good (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq3 : (p ^ f) % 3 = 1)
    (hq4 : (p ^ f) % 4 = 3) (hG : U3OddGood F p f hF) : U3OddCore F p f hF := by
  intro ω hω W Y hNW hYW hAY hY
  by_cases hbad : ∀ x ∈ W, x * zSU hF = zSU hF * x → x ∈ normA0 hF ω
  · obtain ⟨ν, -, hν2, hνq⟩ := exists_unit_orderOf_card_add_one hF hp2
    exact ((badCase_model hF hp2 hω hq3 hq4 hν2 hνq hNW hbad).false_of_isLThreeTwo hYW
      (hAY (Subgroup.mem_zpowers _)) hY).elim
  · push Not at hbad
    exact Or.inr (hG ω hω W hNW hbad)

theorem overgroupL32U3Odd_of_good
    (hG : ∀ (F : Type) [Field F] [Finite F] (p f : ℕ) [Fact p.Prime] [CharP F p]
      (hF : Nat.card F = (p ^ f) ^ 2), p ≠ 2 → (p ^ f) % 3 = 1 → (p ^ f) % 4 = 3 →
        U3OddGood F p f hF) : OvergroupL32U3Odd :=
  overgroupL32U3Odd_of_u3OddCore_mod4_three fun F _ _ p f _ _ hF hp2 hq3 hq4 =>
    u3OddCore_of_good hF hp2 hq3 hq4 (hG F p f hF hp2 hq3 hq4)

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
