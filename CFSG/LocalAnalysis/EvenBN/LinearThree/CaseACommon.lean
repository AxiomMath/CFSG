module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.TwoSevenOddCore

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.OddStandard.Seitz77 (Datum)

namespace Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

open CFSG.LocalAnalysis.EvenBN.GMSK

theorem commutator_oddCore_Ebar_of_conj (hf : 3 ≤ f) (d : Datum A) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (w : WData d Vi (2 ^ f))
    {K : Type} [Field K] [Finite K] (D : LeviData A Vi K) (hKc : Nat.card K = 2 ^ f)
    (hconj : ∀ z ∈ w.Ltil D.lev.range, orderOf (w.ttil * z) = 2 → z * z = 1 →
      ∃ m : w.Ntil, m * w.ttil * m⁻¹ = w.ttil * z) :
    ⁅standardComponentOddCore w.Nbar, w.Ebar D.lev.range⁆ = ⊥ := by
  have : CharP K 2 :=
    ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hKc
  have hK3 : 3 ≤ Nat.card K := by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hsimp, hnab, hE, -, -, -, -⟩ := w.lbar_data hf hR hW hN hKc D
  set R := standardComponentOddCore w.Nbar with hRdef
  set Lb := w.Lbar D.lev.range with hLb
  have hRodd : Odd (Nat.card R) := odd_card_standardComponentOddCore _
  have hRsq : ∀ x ∈ R, x * x = 1 → x = 1 := by
    intro x hx hx2
    have h1 : orderOf x ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hx
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hx2])
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
    · exact orderOf_eq_one_iff.mp h3
    · rw [h3] at h1
      exact absurd (even_iff_two_dvd.mpr h1) (Nat.not_even_iff_odd.mpr hRodd)
  obtain ⟨E, hEL, hEel, hE4⟩ := hE
  obtain ⟨z, hzE, hz1⟩ : ∃ z ∈ E, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
    rw [this, Subgroup.card_bot] at hE4
    omega
  have hz2 : z * z = 1 := by rw [← sq]; exact hEel.2 z hzE
  have hzL : z ∈ Lb := hEL hzE
  have hzt : w.tbar * z = z * w.tbar :=
    (mem_centralizer_singleton_iff.mp (w.Lbar_le_centralizer D hzL)).symm
  have ht2 : w.tbar * w.tbar = 1 := by
    have := pow_orderOf_eq_one w.tbar
    rwa [w.orderOf_tbar, sq] at this
  have ht1 : w.tbar ≠ 1 := by
    intro h1
    have := w.orderOf_tbar
    rw [h1, orderOf_one] at this
    omega
  have htz : w.tbar ≠ z := by
    intro heq
    have hcen : (⟨z, hzL⟩ : Lb) ∈ center Lb := mem_center_iff.mpr fun y => Subtype.ext (by
      have hy := mem_centralizer_singleton_iff.mp (w.Lbar_le_centralizer D y.2)
      rw [heq] at hy
      exact hy)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Lb) with h1 | h1
    · rw [h1, mem_bot] at hcen
      exact hz1 (congrArg Subtype.val hcen)
    · obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (mem_center_iff.mp (h1 ▸ mem_top y) x)
  have hsq : w.tbar * z * (w.tbar * z) = (w.tbar * w.tbar) * (z * z) := by
    rw [mul_assoc, ← mul_assoc z, ← hzt]; group
  have htz2 : orderOf (w.ttil * w.projTil z) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => htz ?_
    · rw [← map_mul, ← map_pow, sq, hsq, ht2, hz2, one_mul, map_one]
    · rw [← map_mul] at h1
      have h2 : w.tbar * z ∈ R := (QuotientGroup.eq_one_iff _).mp h1
      have h3 := hRsq _ h2 (by rw [hsq, ht2, hz2, one_mul])
      calc w.tbar = w.tbar * z * z := by rw [mul_assoc, hz2, mul_one]
        _ = z := by rw [h3, one_mul]
  obtain ⟨mt, hmt⟩ : ∃ m : w.Ntil, m * w.ttil * m⁻¹ = w.ttil * w.projTil z :=
    hconj _ ⟨z, hzL, rfl⟩ htz2 (by rw [← map_mul, hz2, map_one])
  obtain ⟨mb, rfl⟩ := QuotientGroup.mk'_surjective _ mt
  have hxy : (w.tbar * z)⁻¹ * (mb * w.tbar * mb⁻¹) ∈ R := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    change w.projTil ((w.tbar * z)⁻¹ * (mb * w.tbar * mb⁻¹)) = 1
    rw [map_mul, map_inv, map_mul, map_mul, map_mul, map_inv]
    change (w.ttil * w.projTil z)⁻¹ * (w.projTil mb * w.ttil * (w.projTil mb)⁻¹) = 1
    rw [show w.projTil mb = (QuotientGroup.mk' (standardComponentOddCore w.Nbar)) mb from rfl, hmt,
      inv_mul_cancel]
  have hx2 : w.tbar * z * (w.tbar * z) = 1 := by rw [hsq, ht2, hz2, one_mul]
  have hy2 : mb * w.tbar * mb⁻¹ * (mb * w.tbar * mb⁻¹) = 1 := by
    rw [show mb * w.tbar * mb⁻¹ * (mb * w.tbar * mb⁻¹) = mb * (w.tbar * w.tbar) * mb⁻¹ by group,
      ht2, mul_one, mul_inv_cancel]
  obtain ⟨m', hm'⟩ := exists_conj_of_inv_mul_mem hRodd hx2 hy2 hxy
  have hm : (m'⁻¹ * mb) * w.tbar * (m'⁻¹ * mb)⁻¹ = w.tbar * z := by
    calc (m'⁻¹ * mb) * w.tbar * (m'⁻¹ * mb)⁻¹ = m'⁻¹ * (mb * w.tbar * mb⁻¹) * m' := by group
      _ = m'⁻¹ * (m' * (w.tbar * z) * m'⁻¹) * m' := by rw [hm']
      _ = w.tbar * z := by group
  have hC : R ⊓ centralizer ({w.tbar} : Set w.Nbar) ≤ centralizer ({z} : Set w.Nbar) := by
    intro x hx
    have := w.oddCore_inf_centralizer_le hK3 D ⟨E, hEL, hEel, hE4⟩ hx
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp this z hzL).symm
  have hRz := le_centralizer_of_conj_mul hRodd ht2 hz2 hzt ht1 hz1 htz hC hm
  have hLR : Lb ≤ centralizer (R : Set w.Nbar) :=
    le_centralizer_of_isSimpleGroup (by rw [normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
      hzL hz1 hRz
  have hER : w.Ebar D.lev.range ≤ centralizer (R : Set w.Nbar) := normalClosure_le_normal hLR
  rw [commutator_eq_bot_iff_le_centralizer]
  exact le_centralizer_iff.mp hER

theorem commutator_oddCore_Ebar_of_caseA (hf : 3 ≤ f) (d : Datum A) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (w : WData d Vi (2 ^ f))
    {K : Type} [Field K] [Finite K] (D : LeviData A Vi K) (hKc : Nat.card K = 2 ^ f)
    (hA : w.CaseA f D.lev.range) :
    ⁅standardComponentOddCore w.Nbar, w.Ebar D.lev.range⁆ = ⊥ :=
  commutator_oddCore_Ebar_of_conj hf d hR hW hN w D hKc fun _ hz htz _ =>
    hA.exists_conj (by omega) hz htz

end Hyp

end CFSG.LocalAnalysis.EvenBN.LinearThree
