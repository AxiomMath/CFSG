module

public import CFSG.LargeExtraspecial.S97RXIdx4
public import CFSG.LargeExtraspecial.S97RXMod
public import CFSG.LargeExtraspecial.S97RXOrb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G} {h k : G}
  {m : S.M}

namespace Pair111

variable (P : Pair111 S g A h k ((m : G) * k)) (hE : Ebar S k ((m : G) * k) ≠ ⊥)
  (hodd : Odd (Nat.card (center (S9.Q97 S k m))))
include P hE hodd

theorem card_T97_mul :
    Nat.card (T97 S k m k) * Nat.card (Ebar S k ((m : G) * k)) = Nat.card (S.Lbar k) := by
  rw [H97.card_T97 hodd P.hy.hyp4, ← P.inf_O2Sub_eq]
  exact (P.hyp97 hE).card_Tj97_mul le_sup_left

theorem card_T97_eq_four_or (h4 : 4 * Nat.card (Ebar S k ((m : G) * k)) ≤ Nat.card (S.Lbar k)) :
    Nat.card (T97 S k m k) = 4 ∨ 8 ≤ Nat.card (T97 S k m k) := by
  have hc := P.card_T97_mul hE hodd
  have hE0 : 0 < Nat.card (Ebar S k ((m : G) * k)) := Nat.card_pos
  have hdvd : Nat.card (T97 S k m k) ∣ 2 ^ (S.width - 1) := by
    rw [← P.hy.cons.card_Lbar, ← hc]
    exact dvd_mul_right _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h4' : 4 ≤ Nat.card (T97 S k m k) := by
    by_contra hlt
    push Not at hlt
    rw [← hc] at h4
    nlinarith
  rw [hj] at h4' ⊢
  rcases Nat.lt_or_ge j 3 with hj3 | hj3
  · interval_cases j
    · norm_num at h4'
    · norm_num at h4'
    · exact Or.inl (by norm_num)
  · exact Or.inr (by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj3)

theorem false_of_four (hT4 : Nat.card (T97 S k m k) = 4)
    (hU4 : 4 ≤ finrank (ZMod 2) ↥(S9.Ut S k (S9.X97 S k m)))
    (htr : ∀ x ∈ T97 S k m k, x ≠ 1 → ∀ y ∈ T97 S k m k, y ≠ 1 →
      ∃ c ∈ normalizer (T97 S k m k : Set (Lam97 S k m)), c * x * c⁻¹ = y) : False := by
  have hc := P.card_T97_mul hE hodd
  rw [hT4] at hc
  exact P.false_of_index_four hc.symm hU4 fun l hl hlE =>
    P.exists_move hE hodd htr (by omega) hl hlE

theorem four_le_finrank_of_orderOf_five (hsimp : IsSimpleGroup (Lam97 S k m)) {c : Lam97 S k m}
    (hc : orderOf c = 5) : 4 ≤ finrank (ZMod 2) ↥(S9.Ut S k (S9.X97 S k m)) := by
  by_contra hlt
  push Not at hlt
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine false_of_orderOf_prime (P.modCfg hE hodd hsimp).inj (p := 5) (by norm_num)
    (fun j hj0 hj => ?_) hc
  have hj3 : j ≤ 3 := by omega
  interval_cases j <;> decide

theorem false_of_SR (h4 : 4 * Nat.card (Ebar S k ((m : G) * k)) ≤ Nat.card (S.Lbar k))
    (hsimp : IsSimpleGroup (Lam97 S k m))
    (htr : ∀ x ∈ T97 S k m k, x ≠ 1 → ∀ y ∈ T97 S k m k, y ≠ 1 →
      ∃ c ∈ normalizer (T97 S k m k : Set (Lam97 S k m)), c * x * c⁻¹ = y)
    (hSR : SRProp (T97 S k m k)) : False := by
  have C := P.modCfg hE hodd hsimp
  rcases P.card_T97_eq_four_or hE hodd h4 with hT4 | hT8
  · by_cases hd : finrank (ZMod 2) ↥(S9.Ut S k (S9.X97 S k m)) ≤ 3
    · exact C.false_of_SR_four hSR hT4 hd
    · exact P.false_of_four hE hodd hT4 (by omega) htr
  · exact C.false_of_SR_eight hSR hT8

theorem false_of_orderOf_prime (hsimp : IsSimpleGroup (Lam97 S k m)) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (h2 : ∀ j, 0 < j → j ≤ finrank (ZMod 2) ↥(S9.Ut S k (S9.X97 S k m)) → ¬ 2 ^ j ≡ 1 [MOD p])
    {c : Lam97 S k m} (hc : orderOf c = p) : False :=
  S11.false_of_orderOf_prime (P.modCfg hE hodd hsimp).inj hp2 h2 hc

theorem finrank_le_ten (hT : Nat.card (T97 S k m k) = 16) :
    finrank (ZMod 2) ↥(S9.Ut S k (S9.X97 S k m)) ≤ 10 := by
  have h1 := P.two_pow_finrank_le hE hodd
  rw [hT] at h1
  by_contra hlt
  push Not at hlt
  have : 2 ^ 11 ≤ 2 ^ finrank (ZMod 2) ↥(S9.Ut S k (S9.X97 S k m)) :=
    Nat.pow_le_pow_right (by norm_num) hlt
  omega

end Pair111

end CFSG.LargeExtraspecial.S11
