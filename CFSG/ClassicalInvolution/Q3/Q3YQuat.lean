module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsLift
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement

section Member

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {z : X}

theorem IsClassicalMember3.exists_quaternion_pair_sq (h : IsClassicalMember3 L z) :
    ∃ x ∈ L, ∃ y ∈ L, x * x = z ∧ y * y = z ∧ x * y * x⁻¹ * y⁻¹ = z := by
  have hodd3 : Odd (Nat.card (ZMod 3)) := odd_natCard_zmod_three
  obtain ⟨e⟩ := h.nonempty_equiv
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  set ρ : L →* SL(2, ZMod 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore L)) with hρ
  have hρker : ∀ q : L, ρ q = 1 → q ∈ classicalInvolutionOddCore L := fun q hq =>
    (QuotientGroup.eq_one_iff q).mp (e.injective (by simpa [hρ] using hq))
  set z' : L := ⟨z, h.mem⟩ with hz'
  have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact h.orderOf_eq_two
  have hρz : ρ z' = -1 := by
    have h1 := (orderOf_eq_two_iff_of_equiv_sl2 hodd3 e
      (QuotientGroup.mk' (classicalInvolutionOddCore L) z')).mp (orderOf_mk_oddCore_eq_two hz'2)
    rw [hρ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [h1, MulEquiv.apply_symm_apply]
  have hLcard : Nat.card L = 24 * Nat.card (classicalInvolutionOddCore L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore L),
      Nat.card_congr e.toEquiv, natCard_sl2Three]
  have hfac : (Nat.card L).factorization 2 = 3 := by
    have h24 : (24 : ℕ).factorization 2 = 3 := by
      have : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
      rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two]
      simp [Nat.Prime.factorization Nat.prime_three]
    have hm : (Nat.card (classicalInvolutionOddCore L)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hd =>
        (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr hd)
    rw [hLcard, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply, h24, hm]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 (Subgroup.zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'2, pow_one])
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup L) = 8 := by
    rw [Sylow.card_eq_multiplicity Q, hfac]
    norm_num
  have hinj : ∀ q ∈ (Q : Subgroup L), ρ q = 1 → q = 1 := by
    intro q hq hρq
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') ⟨q, hq⟩
    rw [Subgroup.orderOf_mk] at hk
    have hodd := odd_orderOf_of_mem_oddCore₃ (hρker q hρq)
    rw [hk] at hodd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hk0⟩)
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hQsub : (Q : Subgroup L).map ρ ≤ sl2ThreeQ := by
    rintro _ ⟨q, hq, rfl⟩
    refine mem_sl2ThreeQ_iff.mpr (sl2Three_pow_four_of_pow_eight _ ?_)
    have h1 : q ^ 8 = 1 := by
      have h2 : (⟨q, hq⟩ : (Q : Subgroup L)) ^ Nat.card (Q : Subgroup L) = 1 := pow_card_eq_one'
      have h3 : q ^ Nat.card (Q : Subgroup L) = 1 := congrArg Subtype.val h2
      rwa [hQcard] at h3
    rw [← map_pow, h1, map_one]
  have hQeq : (Q : Subgroup L).map ρ = sl2ThreeQ := by
    refine Subgroup.eq_of_le_of_card_ge hQsub ?_
    rw [natCard_sl2ThreeQ]
    have hinj' : Function.Injective (ρ.comp (Q : Subgroup L).subtype) := by
      rw [injective_iff_map_eq_one]
      intro q hq
      exact Subtype.ext (hinj q.1 q.2 hq)
    have hrange : (ρ.comp (Q : Subgroup L).subtype).range = (Q : Subgroup L).map ρ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj', Subgroup.card_top,
      hQcard]
  have hQz : z' ∈ (Q : Subgroup L) := hQ (Subgroup.mem_zpowers z')
  have heq : ∀ q ∈ (Q : Subgroup L), ρ q = -1 → q = z' := by
    intro q hq hρq
    have h1 : z'⁻¹ * q = 1 := hinj _ ((Q : Subgroup L).mul_mem ((Q : Subgroup L).inv_mem hQz) hq)
      (by rw [map_mul, map_inv, hρz, hρq]; simp)
    exact (inv_mul_eq_one.mp h1).symm
  have hi₀ : (⟨!![2, 2; 2, 1], by decide⟩ : SL(2, ZMod 3)) ∈ sl2ThreeQ :=
    mem_sl2ThreeQ_iff.mpr (by decide +kernel)
  have hj₀ : (⟨!![2, 1; 1, 1], by decide⟩ : SL(2, ZMod 3)) ∈ sl2ThreeQ :=
    mem_sl2ThreeQ_iff.mpr (by decide +kernel)
  obtain ⟨x, hxQ, hx⟩ := hQeq ▸ hi₀
  obtain ⟨y, hyQ, hy⟩ := hQeq ▸ hj₀
  have hxx : x * x = z' := heq _ ((Q : Subgroup L).mul_mem hxQ hxQ) (by
    rw [map_mul, hx]; decide +kernel)
  have hxy : x * y * x⁻¹ * y⁻¹ = z' := heq _ (by
      exact (Q : Subgroup L).mul_mem ((Q : Subgroup L).mul_mem ((Q : Subgroup L).mul_mem hxQ hyQ)
        ((Q : Subgroup L).inv_mem hxQ)) ((Q : Subgroup L).inv_mem hyQ)) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx, hy]; decide +kernel)
  have hyy : y * y = z' := heq _ ((Q : Subgroup L).mul_mem hyQ hyQ) (by
    rw [map_mul, hy]; decide +kernel)
  refine ⟨x, x.2, y, y.2, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hxx
  · exact congrArg Subtype.val hyy
  · exact congrArg Subtype.val hxy
end Member

end CFSG.ClassicalInvolution.Q3

namespace CFSG.ClassicalInvolution.Q3.Q3Y

section Pair

variable {P : Type*} [Group P]

theorem false_of_quaternion_pair (S : Subgroup P) {ζ w a a' b : P} (hζ1 : ζ ≠ 1)
    (hζ2 : ζ * ζ = 1) (haa : a * a = ζ) (ha'a' : a' * a' = ζ) (hbb : b * b = ζ)
    (hnc : a * a' ≠ a' * a) (hab : a * b = b * a) (ha'b : a' * b = b * a')
    (haS : a ∈ S) (ha'S : a' ∈ S) (hbS : b ∈ S) (hwζ : w ≠ ζ)
    (hBD : ∀ p q : P, p ∈ S → q ∈ S → p * p = 1 → q * q = 1 → p ≠ 1 → q ≠ 1 → p ≠ q →
      p * q = q * p → w = p ∨ w = q ∨ w = p * q) : False := by
  have hζb : ζ * b = b * ζ := by rw [← hbb, ← mul_assoc, mul_assoc]
  have hζS : ζ ∈ S := haa ▸ S.mul_mem haS haS
  have core : ∀ u v : P, u ∈ S → u * u = ζ → v * v = ζ → u * b = b * u → v * b = b * v →
      u * v ≠ v * u → w = u * b ∨ w = u * b * ζ := by
    intro u v huS huu hvv hub hvb huv
    have hζu : ζ * u = u * ζ := by rw [← huu, ← mul_assoc, mul_assoc]
    have hζv : ζ * v = v * ζ := by rw [← hvv, ← mul_assoc, mul_assoc]
    have hvbi : Commute v b⁻¹ := (show Commute v b from hvb).inv_right
    have hvζ : Commute v ζ := (show Commute v ζ from hζv.symm)
    have hc2 : (u * b) * (u * b) = 1 := by
      calc (u * b) * (u * b) = u * (b * u) * b := by group
        _ = u * (u * b) * b := by rw [← hub]
        _ = (u * u) * (b * b) := by group
        _ = 1 := by rw [huu, hbb, hζ2]
    have hc1 : u * b ≠ 1 := by
      intro h
      apply huv
      rw [eq_inv_of_mul_eq_one_left h]
      exact hvbi.eq.symm
    have hcζ : u * b ≠ ζ := by
      intro h
      apply huv
      rw [eq_mul_inv_of_mul_eq h]
      exact (Commute.mul_right hvζ hvbi).eq.symm
    have hcomm : (u * b) * ζ = ζ * (u * b) := by
      calc (u * b) * ζ = u * (b * ζ) := mul_assoc _ _ _
        _ = u * (ζ * b) := by rw [hζb]
        _ = (u * ζ) * b := by rw [← mul_assoc]
        _ = (ζ * u) * b := by rw [hζu]
        _ = ζ * (u * b) := mul_assoc _ _ _
    rcases hBD (u * b) ζ (S.mul_mem huS hbS) hζS hc2 hζ2 hc1 hζ1 hcζ hcomm with h | h | h
    · exact Or.inl h
    · exact absurd h hwζ
    · exact Or.inr h
  have hζa' : ζ * a' = a' * ζ := by rw [← ha'a', ← mul_assoc, mul_assoc]
  have e : a' * b * ζ = a' * ζ * b := by rw [mul_assoc, ← hζb, ← mul_assoc]
  have e' : a * b * ζ = a * ζ * b := by
    have hζa : ζ * a = a * ζ := by rw [← haa, ← mul_assoc, mul_assoc]
    rw [mul_assoc, ← hζb, ← mul_assoc]
  have hA := core a a' haS haa ha'a' hab ha'b hnc
  have hB := core a' a ha'S ha'a' haa ha'b hab (fun h => hnc h.symm)
  have hζa : ζ * a = a * ζ := by rw [← haa, ← mul_assoc, mul_assoc]
  rcases hA with h1 | h1 <;> rcases hB with h2 | h2
  · exact hnc (by rw [mul_right_cancel (h1.symm.trans h2)])
  · have h3 : a = a' * ζ := mul_right_cancel ((h1.symm.trans h2).trans e)
    apply hnc
    rw [h3, mul_assoc, hζa', ← mul_assoc]
  · have h3 : a' = a * ζ := mul_right_cancel ((h2.symm.trans h1).trans e')
    apply hnc
    rw [h3, mul_assoc, hζa, ← mul_assoc]
  · exact hnc (by rw [mul_right_cancel (mul_right_cancel (h1.symm.trans h2))])

end Pair

end CFSG.ClassicalInvolution.Q3.Q3Y
