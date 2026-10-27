module

public import CFSG.LieType.Steinberg.CentralExt.FieldTwoMultiplier
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.CentralExt CFSG.LocalAnalysis.ComponentInitial CFSG.Open

theorem ordE8_lt {q : ℕ} (hq : 2 ≤ q) : ordE8 q < q ^ 248 := by
  have h : ∀ d : ℕ, 1 ≤ d → 0 < q ^ d - 1 ∧ q ^ d - 1 < q ^ d := by
    intro d hd
    have h1 : 2 ≤ q ^ d := le_trans hq (Nat.le_self_pow (by omega) q)
    exact ⟨by omega, by omega⟩
  unfold ordE8
  have e : q ^ 248 = q ^ 120 * q ^ 30 * q ^ 24 * q ^ 20 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 8 * q ^ 2 := by
    simp only [← pow_add]
  rw [e]
  have hq0 : 0 < q := by omega
  gcongr
  all_goals first | exact (h _ (by norm_num)).2 | exact (h _ (by norm_num)).1.le | positivity

section Center


theorem center_eq_bot_of_E8 {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : L ⧸ Subgroup.center L ≃* AdjointQuotient .E8 K) : Subgroup.center L = ⊥ := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (k := n) hn hK
  have hfin : Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E8 K)) := by
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · exact (FieldTwo.e8_two_hopfMultiplier (by simpa using hK)).2
      · exact (FieldFour.e8_four_hopfMultiplier hK).2
    · refine (AdjointClosed.e8_hopfMultiplier ?_).2
      rw [hK]
      calc 5 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
  have hfin' : Finite (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E8 K)) :=
    Finite.of_subsingleton
  have h1 := GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hL e
  have h2 : Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E8 K)) = 1 :=
    Nat.card_unique
  rw [h2] at h1
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 h1)

end Center

section Outer

variable {S : Type} [Group S] {Γ : Type*} [Group Γ]

theorem card_le_two_mul_of_theta [Finite S] (Θ : MulAut S →* Γ) (B : Subgroup (MulAut S))
    (hΘ : ∀ b ∈ B, ∀ b' ∈ B, Θ b ≠ 1 → Θ b' ≠ 1 → Θ b = Θ b') :
    Nat.card B ≤ 2 * Nat.card ↥(B ⊓ Θ.ker) := by
  classical
  have hfin : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S)) (fun f g h => MulEquiv.ext (congrFun h))
  let f : ↥B →* Γ := Θ.comp B.subtype
  have h1 := Subgroup.card_mul_index f.ker
  have h2 : f.ker.index = Nat.card f.range := Subgroup.index_ker f
  have h3 : Nat.card f.range ≤ 2 := by
    by_cases hex : ∃ b ∈ B, Θ b ≠ 1
    · obtain ⟨b₀, hb₀, hb₀1⟩ := hex
      have hsub : (f.range : Set Γ) ⊆ {1, Θ b₀} := by
        rintro _ ⟨b, rfl⟩
        by_cases h1 : Θ b = 1
        · exact Or.inl h1
        · exact Or.inr (hΘ b b.2 b₀ hb₀ h1 hb₀1)
      calc Nat.card f.range = Set.ncard (f.range : Set Γ) := Nat.card_coe_set_eq _
        _ ≤ Set.ncard ({1, Θ b₀} : Set Γ) := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := (Set.ncard_insert_le 1 {Θ b₀}).trans (by rw [Set.ncard_singleton])
    · push Not at hex
      have hsub : (f.range : Set Γ) ⊆ {1} := by
        rintro _ ⟨b, rfl⟩
        exact hex b b.2
      calc Nat.card f.range = Set.ncard (f.range : Set Γ) := Nat.card_coe_set_eq _
        _ ≤ Set.ncard ({1} : Set Γ) := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by rw [Set.ncard_singleton]; norm_num
  have h4 : Nat.card f.ker = Nat.card ↥(B ⊓ Θ.ker) := by
    have : f.ker = (B ⊓ Θ.ker).subgroupOf B := by
      ext x
      simp [f, Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← h1, h2, h4]
  nlinarith [h3, Nat.zero_le (Nat.card ↥(B ⊓ Θ.ker))]

end Outer

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
