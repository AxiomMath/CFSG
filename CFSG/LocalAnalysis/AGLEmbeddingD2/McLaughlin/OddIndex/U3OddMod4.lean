module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddCard
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddReduce

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.LieType.Universal.Unitary CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.Open CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

@[expose] def U3OddCore (F : Type) [Field F] [Finite F] (p f : ℕ) [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) : Prop :=
  ∀ ω : Fˣ, orderOf ω = 3 → ∀ W Y : Subgroup (SU (unitaryInvolution F p f) 3),
    Subgroup.normalizer ((Subgroup.zpowers (tSU hF ω) : Subgroup _) : Set _) ≤ W → Y ≤ W →
      Subgroup.zpowers (tSU hF ω) ≤ Y → IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y) →
        W = ⊤ ∨ ¬ 2 ∣ W.index

omit [Finite F] in
theorem pow_eq_self_of_orderOf_three {ω : Fˣ} (hω : orderOf ω = 3) {q : ℕ} (hq : q % 3 = 1) :
    ω ^ q = ω := by
  have h3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  conv_lhs => rw [← Nat.div_add_mod q 3, hq, pow_add, pow_mul, h3, one_pow, one_mul, pow_one]

theorem mem_normalizer_zpowers_of_commute {G : Type*} [Group G] {a x : G} (h : Commute x a) :
    x ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ y ∈ Subgroup.zpowers a, x * y * x⁻¹ = y := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [(Commute.zpow_right h n).eq, mul_inv_cancel_right]
  have key' : ∀ y ∈ Subgroup.zpowers a, x⁻¹ * y * x = y := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [mul_assoc, ← (Commute.zpow_right h n).eq, inv_mul_cancel_left]
  intro y
  constructor
  · intro hy
    rw [key y hy]; exact hy
  · intro hy
    have := key' _ hy
    rw [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this
    exact this.symm ▸ hy

theorem mem_normalizer_zpowers_of_inv {G : Type*} [Group G] {a s : G} (hs : s * s = 1)
    (hsa : s * a * s⁻¹ = a⁻¹) :
    s ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have key : ∀ y ∈ Subgroup.zpowers a, s * y * s⁻¹ ∈ Subgroup.zpowers a := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← conj_zpow, hsa]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) n
  intro y
  constructor
  · exact key y
  · intro hy
    have := key _ hy
    rwa [show s * (s * y * s⁻¹) * s⁻¹ = y by
      rw [hsi]
      calc s * (s * y * s) * s = (s * s) * y * (s * s) := by simp only [mul_assoc]
        _ = y := by rw [hs]; simp] at this

theorem not_four_mul_dvd_card (q : ℕ) (hq4 : q % 4 = 1) (hq : 2 ≤ q) :
    ¬ 4 * (q ^ 2 - 1) ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  intro h
  have hpos : 0 < q ^ 2 - 1 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  have h' : 4 ∣ q ^ 3 * (q ^ 3 + 1) := by
    have h2 : (q ^ 2 - 1) * 4 ∣ (q ^ 2 - 1) * (q ^ 3 * (q ^ 3 + 1)) := by
      have e1 : 4 * (q ^ 2 - 1) = (q ^ 2 - 1) * 4 := mul_comm _ _
      have e2 : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) = (q ^ 2 - 1) * (q ^ 3 * (q ^ 3 + 1)) := by ring
      rw [e1, e2] at h
      exact h
    exact Nat.dvd_of_mul_dvd_mul_left hpos h2
  have : q ^ 3 * (q ^ 3 + 1) % 4 = 2 := by
    simp [Nat.mul_mod, Nat.pow_mod, Nat.add_mod, hq4]
  omega

theorem u3OddCore_of_mod4 (hF : Nat.card F = (p ^ f) ^ 2) (hq3 : (p ^ f) % 3 = 1)
    (hq4 : (p ^ f) % 4 = 1) : U3OddCore F p f hF := by
  intro ω hω W Y hNW _ _ _
  right
  have hω' : ω ^ (p ^ f) = ω := pow_eq_self_of_orderOf_three hω hq3
  set a := tSU hF ω with ha
  have hTN : (tSU hF).range ≤ W := by
    rintro _ ⟨μ, rfl⟩
    refine hNW (mem_normalizer_zpowers_of_commute ?_)
    show tSU hF μ * tSU hF ω = tSU hF ω * tSU hF μ
    rw [← map_mul, ← map_mul, mul_comm]
  have hsN : (sSU : SU (unitaryInvolution F p f) 3) ∈ W := by
    refine hNW (mem_normalizer_zpowers_of_inv sSU_mul_self ?_)
    rw [ha, sSU_conj_tSU, hω', map_inv]
  have hn : ∀ x ∈ (tSU hF).range, (sSU : SU (unitaryInvolution F p f) 3) * x * sSU⁻¹ ∈
      (tSU hF).range := by
    rintro _ ⟨μ, rfl⟩
    rw [sSU_conj_tSU]
    exact ⟨_, rfl⟩
  have hdvd := two_mul_card_dvd_of_involution sSU_mul_self (sSU_not_mem_range hF) hn hTN hsN
  have hpq : 2 ≤ p ^ f := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    by_contra h
    have h2 : p ^ f ≤ 1 := by omega
    have h3 : (p ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h2 2
    omega
  refine not_two_dvd_index_of_dvd_card hdvd ?_
  rw [card_range_tSU hF, card_SU3 hF]
  exact not_four_mul_dvd_card _ hq4 hpq

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
