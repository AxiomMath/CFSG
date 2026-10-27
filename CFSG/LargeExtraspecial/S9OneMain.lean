module

public import CFSG.LargeExtraspecial.S9FusB
public import CFSG.LargeExtraspecial.S8CorBApply
public import CFSG.LargeExtraspecial.S9OneB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem timmesfeld_9_1_corB (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t))
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t) :
    (∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) → x * t * x⁻¹ ∈ Nbar S g t) ∧
      ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) → x * t * x⁻¹ ≠ t →
        ∃ n ∈ Nbar S g t, n * (x * t * x⁻¹) * n⁻¹ = x * t * x⁻¹ * t := by
  refine ⟨fun x hxM hτt => ?_, fun x hxM hτt hτne => ?_⟩
  · obtain ⟨k, -, hk⟩ := exists_mem_Abar_conj hCE H hNo C ht ht1 hVQ hSp h6 hL hxM hτt
    exact hk.2
  · obtain ⟨k, hk, hkA⟩ := exists_mem_Abar_conj hCE H hNo C ht ht1 hVQ hSp h6 hL hxM hτt
    have haQ := H.conj_mem
    have hkt := commute_of_mem_Rbar haQ hk
    have hkt' : (S.ρ k)⁻¹ * t = t * (S.ρ k)⁻¹ := by
      calc (S.ρ k)⁻¹ * t = (S.ρ k)⁻¹ * (t * S.ρ k) * (S.ρ k)⁻¹ := by group
        _ = (S.ρ k)⁻¹ * (S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hkt]
        _ = t * (S.ρ k)⁻¹ := by group
    have e : (S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k =
        ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ := by
      calc (S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k =
          ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ * ((S.ρ k)⁻¹ * S.ρ k) := by group
        _ = ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ := by rw [inv_mul_cancel, mul_one]
    have hkxM : (S.ρ k)⁻¹ * x ∈ S.Mbar := S.Mbar.mul_mem (inv_mem (Rbar_le_Mbar hk)) hxM
    have hA : ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ ∈ S.Lbar g ⊓ Nbar S g t := by
      rw [← e]
      refine ⟨(mem_Lbar_mul_iff S k g).mp hkA.1, ?_⟩
      have h1 := conj_mem_Nbar haQ (k := k⁻¹) (by rw [map_inv]; exact hkt') hkA.2
      rwa [map_inv, inv_inv] at h1
    have hne : ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ ≠ t := by
      rw [← e]
      intro he
      apply hτne
      calc x * t * x⁻¹ = S.ρ k * ((S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k) * (S.ρ k)⁻¹ := by group
        _ = S.ρ k * t * (S.ρ k)⁻¹ := by rw [he]
        _ = t := by rw [hkt, mul_inv_cancel_right]
    obtain ⟨n, hn, hnτ⟩ := exists_conj_eq_mul_t hCE H hNo C ht ht1 hVQ hSp hkxM hA hne
    rw [← e] at hnτ
    refine ⟨S.ρ k * n * (S.ρ k)⁻¹, conj_mem_Nbar haQ hkt hn, ?_⟩
    calc S.ρ k * n * (S.ρ k)⁻¹ * (x * t * x⁻¹) * (S.ρ k * n * (S.ρ k)⁻¹)⁻¹ =
        S.ρ k * (n * ((S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k) * n⁻¹) * (S.ρ k)⁻¹ := by group
      _ = S.ρ k * ((S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hnτ]
      _ = x * t * x⁻¹ * (S.ρ k * t * (S.ρ k)⁻¹) := by group
      _ = x * t * x⁻¹ * t := by rw [hkt, mul_inv_cancel_right]

theorem isPGroup_Nbar_of_spCase (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) : IsPGroup 2 (Nbar S g t) := by
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hNQ : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ
    (pairGen_of_spCase H C ht ht1 hVQ hSp) (Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp)
    hh hb
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  intro n
  refine ⟨2, Subtype.ext ?_⟩
  have h1 := hNQ.sq n n.2
  rw [Subgroup.coe_pow, show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, pow_two, OneMemClass.coe_one]
  rw [← pow_two] at h1
  rcases S8.eq_one_or_eq_of_mem_zpowers htt h1 with h2 | h2
  · rw [h2, one_mul]
  · rw [h2, htt]

theorem four_lt_width_of_spCase (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hSp : SpCase H C ht ht1 hVQ)
    (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) : 4 < S.width := by
  have hcard := card_Lbar_inf_Nbar_sp H C ht ht1 hVQ hSp
  have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hle : zpowers t ≤ S.Lbar g ⊓ Nbar S g t := by
    rw [zpowers_le]
    exact ⟨ht, self_mem_Nbar H ht⟩
  have hlt : Nat.card (zpowers t) < Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hle (Ne.symm hA))
  rw [Nat.card_zpowers, hto, hcard] at hlt
  have : 1 < S.width - finrank (ZMod 2) (Vt S g t) := by
    by_contra hc
    push Not at hc
    have : 2 ^ (S.width - finrank (ZMod 2) (Vt S g t)) ≤ 2 ^ 1 :=
      Nat.pow_le_pow_right (by norm_num) hc
    omega
  omega

theorem timmesfeld_9_1 (hCorB : S8.TimmesfeldCorBInput) (hFacts : S8.CorBListFacts)
    (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) :
    finrank (ZMod 2) (Vt S g t) = 4 ∨
      ∃ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g ∧ x * t * x⁻¹ ∉ Nbar S g t := by
  by_cases h4 : finrank (ZMod 2) (Vt S g t) = 4
  · exact Or.inl h4
  right
  have h6 : 6 ≤ finrank (ZMod 2) (Vt S g t) := by
    have := four_le_finrank_Vt H C ht ht1 hVQ hNo
    obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
    omega
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := timmesfeld_9_1_corB hCE H hNo C ht ht1 hVQ hSp h6 hcon
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hNQ : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ
    (pairGen_of_spCase H C ht ht1 hVQ hSp) (Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp)
    hh hb
  have hX := (S45Q.hyp45Q H C).sp ht ht1 hVQ hSp h6
  have hin : S8.conjCentM S t ⊆ Nbar S g t := by
    rintro τ ⟨-, hτt, x, hxM, rfl⟩
    exact h1 x hxM hτt
  refine S8.false_of_corB hCorB hFacts hCE hIrr H hNo C
    (four_lt_width_of_spCase H hNo C ht ht1 hVQ hSp hA) ht ht1 hA
    (isPGroup_Nbar_of_spCase hCE H hNo C ht ht1 hVQ hSp) le_rfl hX.1 hX.2 hin
    (fun τ hτ n hn => hNQ.comm n hn τ (hin hτ)) ?_
  rintro τ ⟨-, hτt, x, hxM, rfl⟩ hτne
  obtain ⟨n, hn, hnτ⟩ := h2 x hxM hτt hτne
  exact ⟨n, Rbar_le_Mbar (Nbar_le_Rbar hn), hnτ⟩

end CFSG.LargeExtraspecial.S9
