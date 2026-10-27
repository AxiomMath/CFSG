module

public import CFSG.LargeExtraspecial.S9FourC
public import CFSG.LargeExtraspecial.S9FourB
public import CFSG.LargeExtraspecial.S9OneMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem card_Nbar_sp (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) :
    Nat.card (Nbar S g t) = 2 ^ (2 * (S.width - finrank (ZMod 2) (Vt S g t)) - 1) := by
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hgen := pairGen_of_spCase H C ht ht1 hVQ hSp
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ hgen hN0 hh hb
  have htt := mul_self_of_mem_Lbar S H.conj_mem ht
  have htN := self_mem_Nbar H ht
  have hn := finrank_add_two_le_width H C ht ht1 hVQ hSp hA
  have h1 := card_inf_Nbar_eq ht1 htt htN (X := ⊤) (mem_top t)
  have h2 := card_inf_Nbar_eq ht1 htt htN ht
  have h3 := finrank_NQ_eq H C ht ht1 hVQ hgen hN0 hh hb
  have h4 := card_Lbar_inf_Nbar_sp H C ht ht1 hVQ hSp
  have htop : nqSub S g t ⊤ = ⊤ := by
    rw [eq_top_iff]
    intro m _
    obtain ⟨n, rfl⟩ := nqMk_surjective m
    exact ⟨n, mem_top _, rfl⟩
  rw [htop, finrank_top, h3, top_inf_eq] at h1
  rw [h4] at h2
  obtain ⟨d, hd⟩ : ∃ d, finrank (ZMod 2) (nqSub S g t (S.Lbar g)) = d := ⟨_, rfl⟩
  rw [hd] at h1 h2
  have e : S.width - finrank (ZMod 2) (Vt S g t) = d + 1 := by
    have : 2 ^ (S.width - finrank (ZMod 2) (Vt S g t)) = 2 ^ (d + 1) := by
      rw [h2, pow_succ, mul_comm]
    exact Nat.pow_right_injective le_rfl this
  rw [h1, e, show 2 * (d + 1) - 1 = 2 * d + 1 by omega, pow_succ, mul_comm]

theorem timmesfeld_9_4_of_exists (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {x : S.O}
    (hxL : x * t * x⁻¹ ∈ S.Lbar g) (hxN : x * t * x⁻¹ ∉ Nbar S g t) :
    (finrank (ZMod 2) (Vt S g t) = 6 ∧ S.width = 11 ∧ Nat.card (Nbar S g t) = 2 ^ 9) ∨
      (finrank (ZMod 2) (Vt S g t) = 8 ∧ S.width = 17 ∧
        Nat.card (Nbar S g t) = 2 ^ 17) := by
  have hcard := card_Nbar_sp hCE H hNo C ht ht1 hVQ hSp hA
  rcases timmesfeld_9_4_count hCE H hNo C ht ht1 hVQ hSp hA hxL hxN with
    ⟨h4, h7⟩ | ⟨h6, h11⟩ | ⟨h8, h17⟩
  · exact (false_of_sp_four_seven hCE H hNo C ht ht1 hVQ hSp h4 h7).elim
  · left
    refine ⟨h6, h11, ?_⟩
    rw [hcard, h6, h11]
  · right
    refine ⟨h8, h17, ?_⟩
    rw [hcard, h8, h17]

theorem timmesfeld_9_4_of_six (hCorB : S8.TimmesfeldCorBInput) (hFacts : S8.CorBListFacts)
    (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t)
    (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)) :
    (finrank (ZMod 2) (Vt S g t) = 6 ∧ S.width = 11 ∧ Nat.card (Nbar S g t) = 2 ^ 9) ∨
      (finrank (ZMod 2) (Vt S g t) = 8 ∧ S.width = 17 ∧
        Nat.card (Nbar S g t) = 2 ^ 17) := by
  rcases timmesfeld_9_1 hCorB hFacts hCE hIrr H hNo C ht ht1 hVQ hSp hA with h4 | ⟨x, -, hxL, hxN⟩
  · omega
  · exact timmesfeld_9_4_of_exists hCE H hNo C ht ht1 hVQ hSp hA hxL hxN

end CFSG.LargeExtraspecial.S9
