module

public import CFSG.ClassicalInvolution.Q3.Q3SBasic
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

theorem sl2Three_eq_mul_three : ∀ g : SL(2, ZMod 3), ∃ x y : SL(2, ZMod 3),
    x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ (x⁻¹ * g * y⁻¹) ^ 3 = 1 := by
  decide

theorem mul_self_mod_three {m : ℕ} (hm : ¬ 3 ∣ m) : m * m % 3 = 1 := by
  have h : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rw [Nat.mul_mod]
  rcases h with h | h <;> rw [h]

theorem exists_three_pow_lift {G H : Type*} [Group G] [Finite G] [Group H] (ψ : G →* H)
    (hψ : Function.Surjective ψ) {s : H} (hs : s ^ 3 = 1) :
    ∃ x : G, (∃ k : ℕ, orderOf x = 3 ^ k) ∧ ψ x = s := by
  obtain ⟨y, rfl⟩ := hψ s
  have hn : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 3)
  refine ⟨y ^ (m * m), ⟨a, ?_⟩, ?_⟩
  · have hcop : Nat.Coprime (3 ^ a) m :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm)
    rw [orderOf_pow' y (mul_ne_zero hm0 hm0), hnm, Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  · rw [map_pow, pow_eq_pow_mod (m * m) hs, mul_self_mod_three hm, pow_one]

variable {Y : Type} [Group Y]

theorem eq_of_conjNormal_eq_conj {T : Subgroup Y} [T.Normal]
    (hC : Subgroup.centralizer (T : Set Y) = ⊥) {σ : Y} {t : T}
    (h : (MulAut.conjNormal σ : MulAut T) = MulAut.conj t) : σ = t := by
  have hmem : (t : Y)⁻¹ * σ ∈ Subgroup.centralizer (T : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun β : MulAut T => ((β ⟨x, hx⟩ : T) : Y)) h
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc x * ((t : Y)⁻¹ * σ) = (t : Y)⁻¹ * ((t : Y) * x * (t : Y)⁻¹) * σ := by group
      _ = (t : Y)⁻¹ * (σ * x * σ⁻¹) * σ := by rw [h1]
      _ = (t : Y)⁻¹ * σ * x := by group
  rw [hC, Subgroup.mem_bot] at hmem
  calc σ = (t : Y) * ((t : Y)⁻¹ * σ) := by group
    _ = t := by rw [hmem, mul_one]

variable [Finite Y]

theorem isClassicalMember3_inf_of_three_mem {z : Y} {L : Subgroup Y}
    (hz : IsClassicalMember3 L z) {T : Subgroup Y} [hTn : T.Normal]
    (h3 : ∀ x ∈ L, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ T) : IsClassicalMember3 (L ⊓ T) z := by
  obtain ⟨ψ, hψs, hψk⟩ := hz.exists_hom
  let ι : ↥(L ⊓ T) →* ↥L := Subgroup.inclusion inf_le_left
  let ψ' : ↥(L ⊓ T) →* SL(2, ZMod 3) := ψ.comp ι
  have hthree : ∀ s : SL(2, ZMod 3), s ^ 3 = 1 → ∃ w, ψ' w = s := by
    intro s hs
    obtain ⟨x, ⟨k, hk⟩, rfl⟩ := exists_three_pow_lift ψ hψs hs
    have hxT : (x : Y) ∈ T := h3 x x.2 ⟨k, by rw [Subgroup.orderOf_coe]; exact hk⟩
    exact ⟨⟨x, x.2, hxT⟩, rfl⟩
  have hsurj : Function.Surjective ψ' := by
    intro g
    obtain ⟨a, b, ha, hb, hc⟩ := sl2Three_eq_mul_three g
    obtain ⟨wa, hwa⟩ := hthree a ha
    obtain ⟨wb, hwb⟩ := hthree b hb
    obtain ⟨wc, hwc⟩ := hthree _ hc
    refine ⟨wa * wc * wb, ?_⟩
    rw [map_mul, map_mul, hwa, hwb, hwc]
    group
  have hodd : Odd (Nat.card ψ'.ker) := by
    have hle : ψ'.ker.map ι ≤ classicalInvolutionOddCore L := by
      rintro _ ⟨w, hw, rfl⟩
      exact (hψk (ι w)).mp hw
    have h1 : Nat.card (ψ'.ker.map ι) = Nat.card ψ'.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)
    rw [← h1]
    exact hz.odd_card_oddCore.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hzT : z ∈ T := by
    obtain ⟨w, hw⟩ := hsurj (ψ ⟨z, hz.mem⟩)
    set o : Y := (w : Y)⁻¹ * z with ho
    have hoL : o ∈ L := L.mul_mem (L.inv_mem w.2.1) hz.mem
    have hoO : (⟨o, hoL⟩ : L) ∈ classicalInvolutionOddCore L := by
      refine (hψk _).mp ?_
      have h1 : (⟨o, hoL⟩ : L) = (ι w)⁻¹ * ⟨z, hz.mem⟩ := rfl
      rw [h1, map_mul, map_inv]
      change (ψ' w)⁻¹ * ψ ⟨z, hz.mem⟩ = 1
      rw [hw, inv_mul_cancel]
    have hoodd : Odd (orderOf o) := by
      have h1 := hz.odd_orderOf_of_mem_oddCore hoO
      rwa [Subgroup.orderOf_mk] at h1
    have hzw : (w : Y) * z = z * (w : Y) := hz.mul_eq w.2.1
    have hzz : z * z = 1 := by rw [← sq, ← hz.orderOf_eq_two, pow_orderOf_eq_one]
    have ho2 : o ^ 2 = ((w : Y) ^ 2)⁻¹ := by
      rw [ho, sq, sq, mul_inv_rev]
      calc (w : Y)⁻¹ * z * ((w : Y)⁻¹ * z) = (w : Y)⁻¹ * (z * (w : Y)⁻¹) * z := by group
        _ = (w : Y)⁻¹ * ((w : Y)⁻¹ * z) * z := by
            rw [show z * (w : Y)⁻¹ = (w : Y)⁻¹ * z by
              calc z * (w : Y)⁻¹ = (w : Y)⁻¹ * ((w : Y) * z) * (w : Y)⁻¹ := by group
                _ = (w : Y)⁻¹ * (z * (w : Y)) * (w : Y)⁻¹ := by rw [hzw]
                _ = (w : Y)⁻¹ * z := by group]
        _ = (w : Y)⁻¹ * (w : Y)⁻¹ * (z * z) := by group
        _ = (w : Y)⁻¹ * (w : Y)⁻¹ := by rw [hzz, mul_one]
    have hoT : o ∈ T := by
      obtain ⟨j, hj⟩ := hoodd
      have h1 : o = (o ^ 2) ^ (j + 1) := by
        rw [← pow_mul, show 2 * (j + 1) = orderOf o + 1 by omega, pow_succ, pow_orderOf_eq_one,
          one_mul]
      rw [h1, ho2]
      exact T.pow_mem (T.inv_mem (T.pow_mem w.2.2 2)) _
    have hz' : z = (w : Y) * o := by rw [ho]; group
    rw [hz']
    exact T.mul_mem w.2.2 hoT
  refine ⟨hz.orderOf_eq_two, ⟨hz.mem, hzT⟩, ?_, ?_⟩
  · refine IsSubnormal.step inf_le_left ⟨fun n hn g => ?_⟩ hz.subnormal
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨L.mul_mem (L.mul_mem g.2 hn.1) (L.inv_mem g.2), hTn.conj_mem _ hn.2 _⟩
  · exact ⟨(CFSG.ComponentClassification.OddKernel.coreQuotientEquiv ψ' hsurj hodd).trans
      ((QuotientGroup.quotientMulEquivOfEq componentOddCore_sl2Three).trans
        QuotientGroup.quotientBot)⟩

end CFSG.ClassicalInvolution.Q3.Q3T
