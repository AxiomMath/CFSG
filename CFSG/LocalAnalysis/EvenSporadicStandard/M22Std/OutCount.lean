module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutSetup
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.L1Fixed

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G} {F L1 N : Subgroup G}

omit [Finite G] in
private theorem elemAb_sup_zpowers_aux {y : G} (hy2 : y * y = 1) {A : Subgroup G}
    (hA : A ≤ centralizer ({y} : Set G)) (hc : ∀ x ∈ A, ∀ x' ∈ A, x * x' = x' * x)
    (hs : ∀ x ∈ A, x * x = 1) :
    (∀ x ∈ A ⊔ zpowers y, ∀ x' ∈ A ⊔ zpowers y, x * x' = x' * x) ∧
      ∀ x ∈ A ⊔ zpowers y, x * x = 1 := by
  have hz : zpowers y ≤ centralizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_centralizer_iff.2 fun a ha => mem_centralizer_singleton_iff.1 (hA ha)
  have hbc : ∀ b ∈ zpowers y, ∀ a ∈ A, a * b = b * a := fun b hb a ha =>
    mem_centralizer_iff.1 (hz hb) a ha
  have hbb : ∀ b ∈ zpowers y, b = 1 ∨ b = y := fun b hb => mem_zpowers_involution hy2 hb
  have hcom : ∀ b ∈ zpowers y, ∀ b' ∈ zpowers y, b * b' = b' * b := fun b hb b' hb' => by
    rcases hbb b hb with rfl | rfl <;> rcases hbb b' hb' with rfl | rfl <;> simp
  have hsq : ∀ b ∈ zpowers y, b * b = 1 := fun b hb => by
    rcases hbb b hb with rfl | rfl
    · simp
    · exact hy2
  constructor
  · intro x hx x' hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hz hx
    obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hz hx'
    calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
      _ = a * (a' * b) * b' := by rw [hbc b hb a' ha']
      _ = (a * a') * (b * b') := by simp only [mul_assoc]
      _ = (a' * a) * (b' * b) := by rw [hc a ha a' ha', hcom b hb b' hb']
      _ = a' * (a * b') * b := by simp only [mul_assoc]
      _ = a' * (b' * a) * b := by rw [hbc b' hb' a ha]
      _ = a' * b' * (a * b) := by simp only [mul_assoc]
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hz hx
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hbc b hb a ha]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [hs a ha, hsq b hb, mul_one]

namespace OutSetup

variable (S : OutSetup L z F L1 N)

include S

theorem sixteen_le_card_centralizer_L1 {y : G} (hyX : y ∈ normalizer (L1 : Set G))
    (hy2 : y * y = 1) : 16 ≤ Nat.card ↥(centralizer ({y} : Set G) ⊓ L1) := by
  have h := card_le_sq_card_centralizer S.L1_comm S.L1_sq (Subgroup.mem_normalizer_iff.1 hyX)
    (fun x _ => by rw [hy2, one_mul, mul_one])
  rw [S.L1_card, inf_comm] at h
  by_contra hlt
  push Not at hlt
  have : Nat.card ↥(centralizer ({y} : Set G) ⊓ L1) ^ 2 ≤ 15 ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  omega

theorem card_centralizer_L1_le (hcr : CentRank z) {y : G} (hy2 : y * y = 1) (hconj : IsConj z y) :
    Nat.card ↥(centralizer ({y} : Set G) ⊓ L1) ≤ 32 := by
  set W : Subgroup G := centralizer ({y} : Set G) ⊓ L1 with hW
  have hyL1 : y ∉ L1 := fun h =>
    not_isConj_of_elemAb hcr S.L1_comm S.L1_sq (by rw [S.L1_card]; norm_num) h hconj
  have hWc : W ≤ centralizer ({y} : Set G) := inf_le_left
  have hWcomm : ∀ x ∈ W, ∀ x' ∈ W, x * x' = x' * x := fun x hx x' hx' =>
    S.L1_comm x (mem_inf.1 hx).2 x' (mem_inf.1 hx').2
  have hWsq : ∀ x ∈ W, x * x = 1 := fun x hx => S.L1_sq x (mem_inf.1 hx).2
  obtain ⟨hAc, hAs⟩ := elemAb_sup_zpowers_aux hy2 hWc hWcomm hWsq
  have hyA : y ∈ W ⊔ zpowers y := mem_sup_right (mem_zpowers y)
  have hyW : y ∉ W := fun h => hyL1 (mem_inf.1 h).2
  have hcardA : 2 * Nat.card W ≤ Nat.card ↥(W ⊔ zpowers y) := by
    obtain ⟨k, hk⟩ : Nat.card W ∣ Nat.card ↥(W ⊔ zpowers y) :=
      Subgroup.card_dvd_of_le le_sup_left
    have hne : Nat.card ↥(W ⊔ zpowers y) ≠ Nat.card W := fun heq =>
      hyW ((Subgroup.eq_of_le_of_card_ge (le_sup_left : W ≤ W ⊔ zpowers y) (le_of_eq heq)) ▸ hyA)
    have hk1 : k ≠ 1 := fun h => hne (by rw [hk, h, mul_one])
    have hk0 : k ≠ 0 := by
      rintro rfl
      have := Nat.card_pos (α := ↥(W ⊔ zpowers y))
      omega
    have hpos : 0 < Nat.card W := Nat.card_pos
    rw [hk]
    nlinarith [Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨hk0, hk1⟩]
  by_contra hgt
  push Not at hgt
  exact not_isConj_of_elemAb hcr hAc hAs (by omega) hyA hconj

end OutSetup

end CFSG.EvenSporadicStandard.M22Std
