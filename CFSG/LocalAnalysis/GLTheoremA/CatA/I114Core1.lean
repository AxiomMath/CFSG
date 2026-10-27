module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Grp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_mem_not_normalizer {B K : Subgroup Y}
    (hrel : (Subgroup.normalizer (K : Set Y)).relIndex B = 3) :
    ∃ x ∈ B, x ∉ Subgroup.normalizer (K : Set Y) := by
  by_contra h
  push Not at h
  have h1 : (Subgroup.normalizer (K : Set Y)).relIndex B = 1 :=
    Subgroup.relIndex_eq_one.2 (fun x hx => h x hx)
  omega

theorem zpow_three_cases {x : Y} (hord : orderOf x = 3) (j : ℤ) :
    x ^ j = 1 ∨ x ^ j = x ∨ x ^ j = x * x := by
  have h := zpow_mod_orderOf x j
  rw [hord] at h
  have e : j % ((3 : ℕ) : ℤ) = 0 ∨ j % ((3 : ℕ) : ℤ) = 1 ∨ j % ((3 : ℕ) : ℤ) = 2 := by
    push_cast
    omega
  rcases e with e | e | e
  · left; rw [← h, e, zpow_zero]
  · right; left; rw [← h, e, zpow_one]
  · right; right; rw [← h, e, zpow_two]

theorem coset_cases {B K : Subgroup Y} (hB : IsElemAbelian 3 B) {x : Y} (hxB : x ∈ B)
    (hxN : x ∉ Subgroup.normalizer (K : Set Y))
    (hrel : (Subgroup.normalizer (K : Set Y)).relIndex B = 3) :
    ∀ b ∈ B, cj b K = K ∨ cj b K = cj x K ∨ cj b K = cj (x * x) K := by
  have hx3 : x ^ 3 = 1 := hB.2 x hxB
  have hx1 : x ≠ 1 := fun h => hxN (h ▸ Subgroup.one_mem _)
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  set N : Subgroup Y := Subgroup.normalizer (K : Set Y) with hNdef
  set M : Subgroup Y := N ⊓ B with hMdef
  have hcomm : ElemCommute M (Subgroup.zpowers x) := by
    intro m hm c hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact isElemAbelian_commute hB hm.2 (B.zpow_mem hxB j)
  have hcard : Nat.card M * 3 = Nat.card B := by
    have := Subgroup.relIndex_mul_card (H := N) (K := B)
    rw [hrel] at this
    rw [hMdef, mul_comm]
    exact this
  have hinter : M ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgM, hgz⟩ := hg
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgz
    rw [Subgroup.mem_bot]
    rcases zpow_three_cases hord j with h | h | h
    · exact h
    · exfalso
      apply hxN
      rw [h] at hgM
      exact hgM.1
    · exfalso
      apply hxN
      have e : x * x * (x * x) = x := by
        have : x * x * (x * x) = x ^ 4 := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
        rw [this, show (4 : ℕ) = 3 + 1 from rfl, pow_add, hx3, one_mul, pow_one]
      rw [h] at hgM
      rw [← e]
      exact N.mul_mem hgM.1 hgM.1
  have hsup : M ⊔ Subgroup.zpowers x = B := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact sup_le inf_le_right (Subgroup.zpowers_le.2 hxB)
    · have h1 := card_sup_mul_card_inf_of_le_normalizer (A := M) (B := Subgroup.zpowers x)
        (commutes_normalizer hcomm)
      rw [hinter, Subgroup.card_bot, mul_one, Nat.card_zpowers, hord] at h1
      omega
  intro b hb
  have hb' : b ∈ M ⊔ Subgroup.zpowers x := by rw [hsup]; exact hb
  obtain ⟨m, hm, c, hc, rfl⟩ := mem_sup_of_commutes hcomm b hb'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hmN : m ∈ N := hm.1
  have hcm : cj m K = K := mem_normalizer_iff_cj.1 hmN
  have hcomm' : m * x ^ j = x ^ j * m := hcomm m hm (x ^ j) (Subgroup.mem_zpowers_iff.2 ⟨j, rfl⟩)
  rw [hcomm', cj_mul, hcm]
  rcases zpow_three_cases hord j with h | h | h
  · left; rw [h, cj_one]
  · right; left; rw [h]
  · right; right; rw [h]

theorem closure_le_three {B K : Subgroup Y} (hB : IsElemAbelian 3 B) {x : Y} (hxB : x ∈ B)
    (hxN : x ∉ Subgroup.normalizer (K : Set Y))
    (hrel : (Subgroup.normalizer (K : Set Y)).relIndex B = 3) :
    (⨆ b ∈ B, cj b K) ≤ K ⊔ cj x K ⊔ cj (x * x) K := by
  refine iSup₂_le fun b hb => ?_
  rcases coset_cases hB hxB hxN hrel b hb with h | h | h
  · rw [h]; exact le_sup_left.trans le_sup_left
  · rw [h]; exact le_sup_right.trans le_sup_left
  · rw [h]; exact le_sup_right

theorem cube_one_of_center {L : Subgroup Y} (hL : Nat.card (Subgroup.center ↥L) = 3) {b : Y}
    (hb : b ∈ L) (hc : ∀ l ∈ L, l * b = b * l) : b ^ 3 = 1 := by
  have hmem : (⟨b, hb⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g.1 g.2)
  let w : Subgroup.center ↥L := ⟨⟨b, hb⟩, hmem⟩
  have hw : w ^ Nat.card (Subgroup.center ↥L) = 1 := pow_card_eq_one'
  rw [hL] at hw
  have := congrArg (fun z : Subgroup.center ↥L => (z : ↥L).1) hw
  simpa using this

theorem eq_one_of_two_group_of_cube {T : Subgroup Y} (hT : IsPGroup 2 T) {t : Y} (ht : t ∈ T)
    (h3 : t ^ 3 = 1) : t = 1 := by
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hg : t ^ Nat.gcd 3 (2 ^ k) = 1 := (pow_gcd_eq_one (a := t)).2 ⟨h3, hk'⟩
  have hcop : Nat.gcd 3 (2 ^ k) = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))
  rw [hcop, pow_one] at hg
  exact hg

theorem two_group_le_pair_trivial {K K₂ K₃ T : Subgroup Y}
    (hKK₂ : ElemCommute K K₂) (hKK₃ : ElemCommute K K₃) (hK₂K₃ : ElemCommute K₂ K₃)
    (hZ₂ : Nat.card (Subgroup.center ↥K₂) = 3) (hZ₃ : Nat.card (Subgroup.center ↥K₃) = 3)
    (hT₁ : T ≤ K₂ ⊔ K₃) (hT₂ : T ≤ K₃ ⊔ K) (hT₃ : T ≤ K ⊔ K₂) (hTp : IsPGroup 2 T) :
    T = ⊥ := by
  have hK₂KK₃ : ElemCommute K₂ (K₃ ⊔ K) :=
    commutes_sup_right hK₂K₃ (commutes_symm hKK₂)
  have hK₃K₂K : ElemCommute K₃ (K ⊔ K₂) :=
    commutes_sup_right (commutes_symm hKK₃) (commutes_symm hK₂K₃)
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  obtain ⟨b, hb, c, hc, rfl⟩ := mem_sup_of_commutes hK₂K₃ t (hT₁ ht)
  have hbS : b ∈ K₃ ⊔ K := by
    have key : b * c * c⁻¹ ∈ K₃ ⊔ K :=
      (K₃ ⊔ K).mul_mem (hT₂ ht) ((le_sup_left : K₃ ≤ K₃ ⊔ K) (K₃.inv_mem hc))
    simpa only [mul_inv_cancel_right] using key
  have hcS : c ∈ K ⊔ K₂ := by
    have key : b⁻¹ * (b * c) ∈ K ⊔ K₂ :=
      (K ⊔ K₂).mul_mem ((le_sup_right : K₂ ≤ K ⊔ K₂) (K₂.inv_mem hb)) (hT₃ ht)
    simpa only [inv_mul_cancel_left] using key
  have hb3 : b ^ 3 = 1 :=
    cube_one_of_center hZ₂ hb (fun l hl => hK₂KK₃ l hl b hbS)
  have hc3 : c ^ 3 = 1 :=
    cube_one_of_center hZ₃ hc (fun l hl => hK₃K₂K l hl c hcS)
  have hbc : Commute b c := hK₂K₃ b hb c hc
  have h3 : (b * c) ^ 3 = 1 := by
    rw [hbc.mul_pow, hb3, hc3, one_mul]
  exact eq_one_of_two_group_of_cube hTp ht h3

end CFSG.LocalAnalysis.GLTheoremA.I114
