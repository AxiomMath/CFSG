module

public import CFSG.GH74.Uniqueness.SU.SU10Bar
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientLifting
public import CFSG.GH74.Uniqueness.Bender.Lemma32

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.Bender

section Quotient

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_conj_of_map_eq {s t : Y} (hs : orderOf s = 2) (ht : orderOf t = 2)
    (h : QuotientGroup.mk' (pPrimeCore 2 Y) s = QuotientGroup.mk' (pPrimeCore 2 Y) t) :
    ∃ n ∈ pPrimeCore 2 Y, n⁻¹ * s * n = t := by
  have hodd : Odd (Nat.card (QuotientGroup.mk' (pPrimeCore 2 Y)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.coprime_two_left.mp coprime_card_pPrimeCore
  have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hs1 : s ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have ht1 : t ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨n, hn, hconj⟩ := CFSG.ProperTwoGeneratedCore.involutions_kernel_conjugate
    (QuotientGroup.mk' (pPrimeCore 2 Y)) hodd (s := s) (t := t) ⟨hs1, hs2⟩ ⟨ht1, ht2⟩ h
  exact ⟨n, by simpa [QuotientGroup.ker_mk'] using hn, hconj⟩

theorem exists_conj_of_map_conj {s t : Y} (hs : orderOf s = 2) (ht : orderOf t = 2) {c : Y}
    (h : QuotientGroup.mk' (pPrimeCore 2 Y) t =
      (QuotientGroup.mk' (pPrimeCore 2 Y) c)⁻¹ * QuotientGroup.mk' (pPrimeCore 2 Y) s *
        QuotientGroup.mk' (pPrimeCore 2 Y) c) :
    ∃ y : Y, y⁻¹ * s * y = t := by
  have hs' : orderOf (c⁻¹ * s * c) = 2 := by
    simpa [MulAut.conj_apply, hs] using (MulAut.conj c⁻¹).orderOf_eq s
  obtain ⟨n, -, hn⟩ := exists_conj_of_map_eq hs' ht (by
    rw [h]
    simp [map_mul, map_inv])
  exact ⟨c * n, by rw [← hn]; group⟩

end Quotient

theorem exists_conj_of_involutions_bender
    {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.BenderSuzuki.IsBenderGroup ↥K) {a b : X} (ha : a ∈ K) (hb : b ∈ K)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : ∃ c ∈ K, c⁻¹ * a * c = b := by
  obtain ⟨n, i, e, hB⟩ := isBenderGroup_iff_exists_benderType.mp hK
  have haa : (⟨a, ha⟩ : ↥K) * ⟨a, ha⟩ = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one a
    rwa [ha2, sq] at this
  have hbb : (⟨b, hb⟩ : ↥K) * ⟨b, hb⟩ = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one b
    rwa [hb2, sq] at this
  have ha1 : (⟨a, ha⟩ : ↥K) ≠ 1 := fun h => by
    have := congrArg Subtype.val h
    simp only [OneMemClass.coe_one] at this
    rw [this, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have hb1 : (⟨b, hb⟩ : ↥K) ≠ 1 := fun h => by
    have := congrArg Subtype.val h
    simp only [OneMemClass.coe_one] at this
    rw [this, orderOf_one] at hb2
    exact absurd hb2 (by norm_num)
  obtain ⟨c, hc⟩ := isConj_iff.mp (hB.lemma_3_4_a haa ha1 hbb hb1)
  refine ⟨(c : X)⁻¹, K.inv_mem c.2, ?_⟩
  simpa using congrArg Subtype.val hc

end CFSG.GH74.Uniqueness.SU.SU10
