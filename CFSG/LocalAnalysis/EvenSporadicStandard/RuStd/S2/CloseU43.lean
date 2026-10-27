module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseU43Fix

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Close

open Subgroup
open scoped commutatorElement

section U43Case

variable {X : Type} [Group X] [Finite X]

theorem false_of_u43
    (d : ThreeLocalData X) (kd : KernelData d)
    {N : Subgroup (X ⧸ CFSG.oddCore X)} (hN : N.Normal) (e : ↥N ≃* U43)
    (hC : ∀ x : X ⧸ CFSG.oddCore X, (∀ n ∈ N, x * n = n * x) → x = 1)
    (hodd : ∀ g : X ⧸ CFSG.oddCore X, Odd (orderOf g) → g ∈ N) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hNS := u43_nonabSimple e
  have hKt : kd.Kt.Normal := kd.Kt_normal
  have hπs := proj_surjective X
  have hNK : N ≤ kd.Kt := by
    have hM : kd.Kt ⊓ N = N := by
      rcases hNS.eq_bot_or_eq_self (kd.Kt ⊓ N) inf_le_right
          (fun a ha s hs => ⟨hKt.conj_mem s hs.1 a,
            N.mul_mem (N.mul_mem ha hs.2) (N.inv_mem ha)⟩) with h | h
      · exact absurd h (kd.inf_ne_bot hN hC)
      · exact h
    exact hM ▸ inf_le_left
  have hN1 : N.comap (proj X) ≤ kd.K := kd.comap_le hNK
  have hQcen : ⁅N.comap (proj X), N.comap (proj X)⁆ ≤ centralizer (CFSG.oddCore X : Set X) :=
    (Subgroup.commutator_mono hN1 hN1).trans kd.comm_le
  have hcardN : Nat.card N = 3265920 := by rw [Nat.card_congr e.toEquiv, card_u43]
  obtain ⟨F, -, -, hF25⟩ := exists_sylow_five_ge d (P := ⊥)
    (IsPGroup.of_card (n := 0) (by simp)) bot_le
  have hFN : F.map (proj X) ≤ N := by
    rintro _ ⟨s, hs, rfl⟩
    apply hodd
    have h1 : orderOf (proj X s) ∣ orderOf s := orderOf_map_dvd _ s
    have h2 : orderOf s ∣ 25 := by
      have := Subgroup.orderOf_dvd_natCard F hs
      rwa [hF25] at this
    exact Odd.of_dvd_nat (by decide : Odd 25) (h1.trans h2)
  have hm5 : Nat.card (F.map (proj X)) ∣ 5 := by
    have h1 : Nat.card (F.map (proj X)) ∣ 25 := by
      have := Subgroup.card_map_dvd (H := F) (proj X)
      rwa [hF25] at this
    have h2 : Nat.card (F.map (proj X)) ∣ 3265920 := by
      have := Subgroup.card_dvd_of_le hFN
      rwa [hcardN] at this
    have := Nat.dvd_gcd h1 h2
    norm_num at this
    exact this
  have hk := card_map_proj_mul F
  rw [hF25] at hk
  have h5k : 5 ∣ Nat.card (CFSG.oddCore X ⊓ F : Subgroup X) := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hm5 with h | h
    · rw [h] at hk
      rw [one_mul] at hk
      rw [hk]; norm_num
    · rw [h] at hk
      exact ⟨1, by omega⟩
  have h5O : 5 ∣ Nat.card (CFSG.oddCore X) := h5k.trans (Subgroup.card_dvd_of_le inf_le_left)
  exact d.noFive _ hQcen (fun α hα => nine_dvd_card_fix hN e hC α hα) h5O

end U43Case

end CFSG.EvenSporadicStandard.RuStd.S2.Close
