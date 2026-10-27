module

public import CFSG.ClassicalInvolution.Q3.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

theorem sl2Three_eq_of_mul_self_eq_one :
    ∀ a b : SL(2, ZMod 3), a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a = b := by
  decide +kernel

theorem sl2Three_exists_orderOf_three : ∃ g : SL(2, ZMod 3), orderOf g = 3 := by
  have h : ∃ g : SL(2, ZMod 3), g ^ 3 = 1 ∧ g ≠ 1 := by decide +kernel
  obtain ⟨g, hg3, hg1⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨g, orderOf_eq_prime hg3 hg1⟩

theorem sl2Three_exists_orderOf_four : ∃ g : SL(2, ZMod 3), orderOf g = 4 := by
  have h : ∃ g : SL(2, ZMod 3), g ^ 2 ≠ 1 ∧ g ^ 4 = 1 := by decide +kernel
  obtain ⟨g, hg2, hg4⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g) (by simpa using hg2) (by simpa using hg4)
  exact ⟨g, by simpa using this⟩

section

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {z : Y}

omit [Finite Y] in
theorem IsClassicalMember3.le_centralizer (h : IsClassicalMember3 L z) :
    L ≤ Subgroup.centralizer ({z} : Set Y) :=
  isSubnormal_le h.subnormal

omit [Finite Y] in
theorem IsClassicalMember3.mul_eq {x : Y} (h : IsClassicalMember3 L z) (hx : x ∈ L) :
    x * z = z * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hx)

omit [Finite Y] in
theorem IsClassicalMember3.exists_hom (h : IsClassicalMember3 L z) :
    ∃ ψ : L →* SL(2, ZMod 3), Function.Surjective ψ ∧
      ∀ x : L, ψ x = 1 ↔ x ∈ classicalInvolutionOddCore L := by
  obtain ⟨e⟩ := h.nonempty_equiv
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun x => ?_⟩
  change e (QuotientGroup.mk x) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem IsClassicalMember3.odd_card_oddCore (_h : IsClassicalMember3 L z) :
    Odd (Nat.card (classicalInvolutionOddCore L)) :=
  CFSG.ComponentClassification.OddCore.odd_card ↥L

theorem IsClassicalMember3.odd_orderOf_of_mem_oddCore (h : IsClassicalMember3 L z) {w : L}
    (hw : w ∈ classicalInvolutionOddCore L) : Odd (orderOf w) := by
  have h1 : orderOf (⟨w, hw⟩ : classicalInvolutionOddCore L) = orderOf w := by
    rw [← Subgroup.orderOf_coe]
  rw [← h1]
  exact h.odd_card_oddCore.of_dvd_nat (orderOf_dvd_natCard _)

theorem IsClassicalMember3.eq_of_orderOf_eq_two (h : IsClassicalMember3 L z) {x : Y}
    (hxL : x ∈ L) (hx : orderOf x = 2) : x = z := by
  obtain ⟨ψ, -, hψ⟩ := h.exists_hom
  set x' : L := ⟨x, hxL⟩ with hx'def
  set z' : L := ⟨z, h.mem⟩ with hz'def
  have hx' : orderOf x' = 2 := by rw [← hx, ← Subgroup.orderOf_coe]
  have hz' : orderOf z' = 2 := by rw [← h.orderOf_eq_two, ← Subgroup.orderOf_coe]
  have hsq : ∀ w : L, orderOf w = 2 → w * w = 1 := fun w hw => by
    have := pow_orderOf_eq_one w
    rwa [hw, pow_two] at this
  have hne : ∀ w : L, orderOf w = 2 → ψ w ≠ 1 := fun w hw h1 => by
    have := h.odd_orderOf_of_mem_oddCore ((hψ w).1 h1)
    rw [hw] at this
    exact absurd this (by decide)
  have heq : ψ x' = ψ z' := by
    refine sl2Three_eq_of_mul_self_eq_one _ _ ?_ ?_ (hne x' hx') (hne z' hz')
    · rw [← map_mul, hsq x' hx', map_one]
    · rw [← map_mul, hsq z' hz', map_one]
  have hker : x'⁻¹ * z' ∈ classicalInvolutionOddCore L :=
    (hψ _).1 (by rw [map_mul, map_inv, heq, inv_mul_cancel])
  have hcomm : x' * z' = z' * x' := Subtype.ext (h.mul_eq hxL)
  have hpow : (x'⁻¹ * z') ^ 2 = 1 := by
    rw [pow_two]
    calc x'⁻¹ * z' * (x'⁻¹ * z') = (x'⁻¹ * x'⁻¹) * (z' * z') := by
          have h2 : z' * x'⁻¹ = x'⁻¹ * z' := by
            rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
          calc x'⁻¹ * z' * (x'⁻¹ * z') = x'⁻¹ * (z' * x'⁻¹) * z' := by group
            _ = x'⁻¹ * (x'⁻¹ * z') * z' := by rw [h2]
            _ = (x'⁻¹ * x'⁻¹) * (z' * z') := by group
      _ = 1 := by rw [hsq z' hz', ← mul_inv_rev, hsq x' hx', inv_one, mul_one]
  have hodd := h.odd_orderOf_of_mem_oddCore hker
  have hdvd : orderOf (x'⁻¹ * z') ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
  have h1 : orderOf (x'⁻¹ * z') = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact h1
    · rw [h2] at hodd
      exact absurd hodd (by decide)
  have h3 : x'⁻¹ * z' = 1 := orderOf_eq_one_iff.mp h1
  exact congrArg Subtype.val (inv_mul_eq_one.mp h3)

theorem IsClassicalMember3.exists_orderOf_eq (h : IsClassicalMember3 L z) {d : ℕ}
    (hg : ∃ g : SL(2, ZMod 3), orderOf g = d) : ∃ y ∈ L, orderOf y = d := by
  obtain ⟨ψ, hψs, -⟩ := h.exists_hom
  obtain ⟨g, hg⟩ := hg
  obtain ⟨x, rfl⟩ := hψs g
  have hdvd : d ∣ orderOf x := hg ▸ orderOf_map_dvd ψ x
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hn0 : orderOf x / d ≠ 0 := by
    intro h0
    have := Nat.div_mul_cancel hdvd
    rw [h0, zero_mul] at this
    exact hx0 this.symm
  refine ⟨((x ^ (orderOf x / d) : L) : Y), (x ^ (orderOf x / d)).2, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd hn0 (Nat.div_dvd_of_dvd hdvd),
    Nat.div_div_self hdvd hx0]

theorem IsClassicalMember3.exists_orderOf_eq_three (h : IsClassicalMember3 L z) :
    ∃ y ∈ L, orderOf y = 3 :=
  h.exists_orderOf_eq sl2Three_exists_orderOf_three

theorem IsClassicalMember3.exists_orderOf_eq_four (h : IsClassicalMember3 L z) :
    ∃ y ∈ L, orderOf y = 4 :=
  h.exists_orderOf_eq sl2Three_exists_orderOf_four

theorem IsClassicalMember3.mul_self_eq_of_orderOf_eq_four (h : IsClassicalMember3 L z) {x : Y}
    (hxL : x ∈ L) (hx : orderOf x = 4) : x * x = z := by
  refine h.eq_of_orderOf_eq_two (L.mul_mem hxL hxL) ?_
  rw [← pow_two, orderOf_pow' _ (by norm_num), hx]
  norm_num

theorem IsClassicalMember3.three_dvd_card (h : IsClassicalMember3 L z) : 3 ∣ Nat.card L := by
  obtain ⟨y, hyL, hy⟩ := h.exists_orderOf_eq_three
  have := Subgroup.orderOf_dvd_natCard L hyL
  rwa [hy] at this

omit [Finite Y] in
theorem IsClassicalMember3.card_eq (h : IsClassicalMember3 L z) :
    Nat.card L = 24 * Nat.card (classicalInvolutionOddCore L) := by
  obtain ⟨e⟩ := h.nonempty_equiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore L),
    Nat.card_congr e.toEquiv, natCard_sl2Three]

end

end CFSG.ClassicalInvolution.Q3
