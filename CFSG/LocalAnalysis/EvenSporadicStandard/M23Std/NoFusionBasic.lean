module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.Rank
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.L1Fixed

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

omit [Finite G] in
theorem elemAb_sup_zpowers_of_sq {y : G} (hy2 : y * y = 1) {A : Subgroup G}
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

theorem card_two_subgroup_le_centralizer (h : OneClassData L z t)
    (hL2 : ¬ 256 ∣ Nat.card L) (h128 : 128 ∣ Nat.card L) {K : Subgroup G} (hK : IsPGroup 2 K)
    (hKC : K ≤ centralizer ({z} : Set G)) : Nat.card K ≤ 256 := by
  have hCL : Nat.card (centralizer ({z} : Set G)) = Nat.card L * 2 := by
    rw [centralizer_z_eq h]
    exact card_sup_zpowers h le_rfl
  obtain ⟨m, hm⟩ := h128
  have hmodd : Odd m := by
    by_contra hodd
    exact hL2 ⟨m / 2, by rcases Nat.even_or_odd m with ⟨k, hk⟩ | ho
                         · omega
                         · exact absurd ho hodd⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hK
  have hdvd : Nat.card K ∣ Nat.card (centralizer ({z} : Set G)) := Subgroup.card_dvd_of_le hKC
  rw [hCL, hm] at hdvd
  have hcop : Nat.Coprime (Nat.card K) m := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hmodd)
  have h256 : Nat.card K ∣ 256 := by
    refine hcop.dvd_of_dvd_mul_right ?_
    have : 128 * m * 2 = 256 * m := by ring
    rwa [this] at hdvd
  exact Nat.le_of_dvd (by norm_num) h256

namespace Setup

variable (S : Setup L z t F L1 N)

include S

omit [Finite G] in
theorem mem_centralizer_of_involution_mul {y l : G} (hy2 : y * y = 1) (hl : l ∈ L1)
    (h2 : y * l * (y * l) = 1) : l ∈ L1 ⊓ centralizer ({y} : Set G) := by
  refine mem_inf.2 ⟨hl, mem_centralizer_singleton_iff.2 ?_⟩
  have hli : l * l = 1 := S.L1_sq l hl
  have h1 : y * l * y = l := by
    have h3 : y * l * y * l = 1 := by
      calc y * l * y * l = y * l * (y * l) := by group
        _ = 1 := h2
    calc y * l * y = (y * l * y * l) * l⁻¹ := by group
      _ = l := by rw [h3, one_mul, inv_eq_of_mul_eq_one_right hli]
  calc l * y = y * (y * l * y) := by
        calc l * y = (y * y) * l * y := by rw [hy2, one_mul]
          _ = y * (y * l * y) := by group
    _ = y * l := by rw [h1]

theorem card_centralizer_L1_of_isConj (hRank : RankFour L) {y : G}
    (hyX : y ∈ normalizer (L1 : Set G)) (hy2 : y * y = 1) (hyL : y ∉ L1)
    (hconj : IsConj z y) : Nat.card ↥(L1 ⊓ centralizer ({y} : Set G)) = 16 := by
  set W := L1 ⊓ centralizer ({y} : Set G) with hW
  have hlow : Nat.card L1 ≤ Nat.card W ^ 2 :=
    card_le_sq_card_centralizer S.L1_comm S.L1_sq (Subgroup.mem_normalizer_iff.1 hyX)
      (fun x hx => by rw [hy2, one_mul, mul_one]) 
  rw [S.L1_card] at hlow
  have hWc : W ≤ centralizer ({y} : Set G) := inf_le_right
  have hWcomm : ∀ x ∈ W, ∀ x' ∈ W, x * x' = x' * x := fun x hx x' hx' =>
    S.L1_comm x (mem_inf.1 hx).1 x' (mem_inf.1 hx').1
  have hWsq : ∀ x ∈ W, x * x = 1 := fun x hx => S.L1_sq x (mem_inf.1 hx).1
  obtain ⟨hAc, hAs⟩ := elemAb_sup_zpowers_of_sq hy2 hWc hWcomm hWsq
  have hyA : y ∈ W ⊔ zpowers y := mem_sup_right (mem_zpowers y)
  have hyW : y ∉ W := fun h => hyL (mem_inf.1 h).1
  have hcardA : 2 * Nat.card W ≤ Nat.card ↥(W ⊔ zpowers y) := by
    have hdvd : Nat.card W ∣ Nat.card ↥(W ⊔ zpowers y) := Subgroup.card_dvd_of_le le_sup_left
    obtain ⟨k, hk⟩ := hdvd
    have hne : Nat.card ↥(W ⊔ zpowers y) ≠ Nat.card W := by
      intro heq
      have hEq : W = W ⊔ zpowers y :=
        Subgroup.eq_of_le_of_card_ge (le_sup_left : W ≤ W ⊔ zpowers y) (le_of_eq heq)
      exact hyW (hEq ▸ hyA)
    have hk1 : k ≠ 1 := fun h => hne (by rw [hk, h, mul_one])
    have hk0 : k ≠ 0 := by
      rintro rfl
      have := Nat.card_pos (α := ↥(W ⊔ zpowers y))
      omega
    have hpos : 0 < Nat.card W := Nat.card_pos
    rw [hk]
    nlinarith [Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨hk0, hk1⟩]
  have hle32 : Nat.card ↥(W ⊔ zpowers y) ≤ 32 := by
    by_contra hgt
    push Not at hgt
    exact not_isConj_of_elemAb S.one hRank hAc hAs hgt hyA hconj
  nlinarith

end Setup

end CFSG.EvenSporadicStandard.M23Std
