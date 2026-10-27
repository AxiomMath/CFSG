module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpCountProof

theorem spc_two_eq_zero {F : Type} [Field F] [CharP F 2] : (2 : F) = 0 := by
  exact_mod_cast CharP.cast_eq_zero F 2

theorem spc_sq_inj {F : Type} [Field F] [CharP F 2] {a b : F} (h : a ^ 2 = b ^ 2) : a = b := by
  have h2 : (2 : F) = 0 := spc_two_eq_zero
  have h0 : (a - b) ^ 2 = 0 := by linear_combination h + (b ^ 2 - a * b) * h2
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)

theorem spc_sq_exists {F : Type} [Field F] [Fintype F] [CharP F 2] (c : F) :
    ∃ b : F, b ^ 2 = c := by
  have hinj : Function.Injective (fun x : F => x ^ 2) := fun a b h => spc_sq_inj h
  exact Finite.surjective_of_injective hinj c

theorem spc_root_dvd_three {F : Type} [Field F] [Fintype F] [CharP F 2] {γ : F}
    (hγ : γ ^ 2 + γ + 1 = 0) : 3 ∣ Nat.card F - 1 := by
  have h2 : (2 : F) = 0 := spc_two_eq_zero
  have hγ0 : γ ≠ 0 := by
    intro h0
    rw [h0] at hγ
    norm_num at hγ
  have h3 : γ ^ 3 = 1 := by linear_combination (γ - 1) * hγ
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, (u : F) = γ := ⟨Units.mk0 γ hγ0, Units.val_mk0 hγ0⟩
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hu]
    exact h3
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, Units.val_one] at hu
    rw [← hu] at hγ
    have h10 : (1 : F) = 0 := by linear_combination hγ - h2
    exact one_ne_zero h10
  have hd : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
  have hd' : orderOf u ∣ Nat.card F - 1 := by
    rw [← Nat.card_units F]
    exact orderOf_dvd_natCard u
  have hod : orderOf u = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hu1
    · exact h
  rw [hod] at hd'
  exact hd'

theorem spc_exists_root {F : Type} [Field F] [Fintype F] [CharP F 2] (h : 3 ∣ Nat.card F - 1) :
    ∃ γ : F, γ ^ 2 + γ + 1 = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units F]
    exact h
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hu3 : u ^ 3 = 1 := by
    rw [← hu]
    exact pow_orderOf_eq_one u
  have hγ3 : (u : F) ^ 3 = 1 := by
    have h := congrArg Units.val hu3
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
  have hne : (u : F) - 1 ≠ 0 := by
    intro h0
    have h1 : u = 1 := Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h0)
    rw [h1, orderOf_one] at hu
    norm_num at hu
  refine ⟨(u : F), ?_⟩
  have hfac : ((u : F) - 1) * ((u : F) ^ 2 + (u : F) + 1) = 0 := by
    linear_combination hγ3
  exact (mul_eq_zero.1 hfac).resolve_left hne

theorem spc_root_partner {F : Type} [Field F] [CharP F 2] {γ δ : F}
    (hγ : γ ^ 2 + γ + 1 = 0) (hδ : δ ^ 2 + δ + 1 = 0) : δ = γ ∨ δ = γ + 1 := by
  have h2 : (2 : F) = 0 := spc_two_eq_zero
  have h : (δ - γ) * (δ + γ + 1) = 0 := by linear_combination hδ - hγ
  rcases mul_eq_zero.1 h with h1 | h1
  · exact Or.inl (sub_eq_zero.1 h1)
  · exact Or.inr (by linear_combination h1 + (-γ - 1) * h2)

theorem spc_root_succ {F : Type} [Field F] [CharP F 2] {γ : F} (hγ : γ ^ 2 + γ + 1 = 0) :
    (γ + 1) ^ 2 + (γ + 1) + 1 = 0 := by
  have h2 : (2 : F) = 0 := spc_two_eq_zero
  linear_combination hγ + (γ + 1) * h2

theorem spc_card_roots_two {F : Type} [Field F] [CharP F 2] {γ : F} (hγ : γ ^ 2 + γ + 1 = 0) :
    Nat.card {δ : F // δ ^ 2 + δ + 1 = 0} = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨γ, hγ⟩, ⟨γ + 1, spc_root_succ hγ⟩, ?_, ?_⟩
  · intro h
    have h' : γ = γ + 1 := congrArg Subtype.val h
    have h1 : (1 : F) = 0 := by linear_combination -h'
    exact one_ne_zero h1
  · apply Set.eq_univ_of_forall
    rintro ⟨δ, hδ⟩
    rcases spc_root_partner hγ hδ with h | h
    · exact Set.mem_insert_iff.2 (Or.inl (Subtype.ext h))
    · exact Set.mem_insert_iff.2 (Or.inr (Set.mem_singleton_iff.2 (Subtype.ext h)))

theorem card_roots_cube {F : Type} [Field F] [Fintype F] [CharP F 2] :
    Nat.card {γ : F // γ ^ 2 + γ + 1 = 0} = if 3 ∣ Nat.card F - 1 then 2 else 0 := by
  split_ifs with h
  · obtain ⟨γ, hγ⟩ := spc_exists_root h
    exact spc_card_roots_two hγ
  · haveI : IsEmpty {γ : F // γ ^ 2 + γ + 1 = 0} :=
      ⟨fun γ => h (spc_root_dvd_three γ.2)⟩
    exact Nat.card_of_isEmpty

theorem spc_norm_pair {F : Type} [Field F] {γ b : F} (hγ : γ ^ 2 + γ + 1 ≠ 0)
    (hb : b ^ 2 = (γ ^ 2 + γ + 1)⁻¹) : (γ * b) ^ 2 + (γ * b) * b + b ^ 2 = 1 := by
  linear_combination (γ ^ 2 + γ + 1) * hb + mul_inv_cancel₀ hγ

theorem card_norm_one {F : Type} [Field F] [Fintype F] [CharP F 2] :
    Nat.card {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1} =
      Nat.card F + 1 - Nat.card {γ : F // γ ^ 2 + γ + 1 = 0} := by
  classical
  have hsum : Nat.card F = Nat.card {γ : F // γ ^ 2 + γ + 1 = 0} +
      Nat.card {γ : F // ¬ (γ ^ 2 + γ + 1 = 0)} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun γ : F => γ ^ 2 + γ + 1 = 0)).symm
  choose s hs using spc_sq_exists (F := F)
  have hsne : ∀ γ : {γ : F // ¬ (γ ^ 2 + γ + 1 = 0)}, s (γ.1 ^ 2 + γ.1 + 1)⁻¹ ≠ 0 := by
    intro γ h0
    have h3 := hs (γ.1 ^ 2 + γ.1 + 1)⁻¹
    rw [h0, zero_pow two_ne_zero] at h3
    exact inv_ne_zero γ.2 h3.symm
  have hbij : Function.Bijective (fun o : Option {γ : F // ¬ (γ ^ 2 + γ + 1 = 0)} =>
      o.elim (⟨(1, 0), by simp⟩ : {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1})
        (fun γ => ⟨(γ.1 * s (γ.1 ^ 2 + γ.1 + 1)⁻¹, s (γ.1 ^ 2 + γ.1 + 1)⁻¹),
          spc_norm_pair (γ := γ.1) (b := s (γ.1 ^ 2 + γ.1 + 1)⁻¹) γ.2 (hs _)⟩)) := by
    constructor
    · rintro (_ | γ) (_ | δ) h
      · rfl
      · exfalso
        have h2 : (0 : F) = s (δ.1 ^ 2 + δ.1 + 1)⁻¹ :=
          congrArg (fun p : {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1} => p.1.2) h
        exact hsne δ h2.symm
      · exfalso
        have h2 : s (γ.1 ^ 2 + γ.1 + 1)⁻¹ = 0 :=
          congrArg (fun p : {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1} => p.1.2) h
        exact hsne γ h2
      · have h1 : γ.1 * s (γ.1 ^ 2 + γ.1 + 1)⁻¹ = δ.1 * s (δ.1 ^ 2 + δ.1 + 1)⁻¹ :=
          congrArg (fun p : {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1} => p.1.1) h
        have h2 : s (γ.1 ^ 2 + γ.1 + 1)⁻¹ = s (δ.1 ^ 2 + δ.1 + 1)⁻¹ :=
          congrArg (fun p : {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1} => p.1.2) h
        rw [← h2] at h1
        exact congrArg some (Subtype.ext (mul_right_cancel₀ (hsne γ) h1))
    · rintro ⟨⟨a, b⟩, hp⟩
      change a ^ 2 + a * b + b ^ 2 = 1 at hp
      by_cases hb0 : b = 0
      · have ha2 : a ^ 2 = 1 ^ 2 := by
          rw [hb0] at hp
          linear_combination hp
        have ha : a = 1 := spc_sq_inj ha2
        refine ⟨none, Subtype.ext (Prod.ext ?_ ?_)⟩
        · exact ha.symm
        · exact hb0.symm
      · obtain ⟨γ, hγ⟩ : ∃ γ : F, γ = a / b := ⟨_, rfl⟩
        have hγa : γ * b = a := by
          rw [hγ]
          exact div_mul_cancel₀ a hb0
        have hb2 : b ^ 2 * (γ ^ 2 + γ + 1) = 1 := by
          linear_combination hp + (γ * b + a + b) * hγa
        have hc : γ ^ 2 + γ + 1 ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hb2
          exact zero_ne_one hb2
        have hbinv : b ^ 2 = (γ ^ 2 + γ + 1)⁻¹ := eq_inv_of_mul_eq_one_left hb2
        have hsb : s (γ ^ 2 + γ + 1)⁻¹ = b :=
          spc_sq_inj ((hs (γ ^ 2 + γ + 1)⁻¹).trans hbinv.symm)
        refine ⟨some ⟨γ, hc⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
        · show γ * s (γ ^ 2 + γ + 1)⁻¹ = a
          rw [hsb]
          exact hγa
        · show s (γ ^ 2 + γ + 1)⁻¹ = b
          exact hsb
  rw [← Nat.card_eq_of_bijective _ hbij, Finite.card_option]
  omega

theorem card_norm_one_eq {F : Type} [Field F] [Fintype F] [CharP F 2] :
    Nat.card {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1} =
      if 3 ∣ Nat.card F - 1 then Nat.card F - 1 else Nat.card F + 1 := by
  rw [card_norm_one, card_roots_cube]
  split_ifs <;> omega

end K421SpCountProof

end CFSG.LocalAnalysis.RankThreeUC.S15
