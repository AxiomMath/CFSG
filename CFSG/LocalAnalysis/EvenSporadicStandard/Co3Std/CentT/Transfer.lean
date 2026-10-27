module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup

theorem transferWitness_of_normal {X : Type} [Group X] [Finite X] {a : X} {Fus : X → Prop}
    (N : Subgroup X) [N.Normal] (ha : a * a = 1) (haN : a ∉ N) (hidx : ¬ 4 ∣ N.index)
    (hFus : ∀ w ∈ N, ¬ Fus w) : TransferWitness X a Fus := by
  have ha_ne : a ≠ 1 := fun h => haN (h ▸ N.one_mem)
  have horder : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha_ne
  have hP : IsPGroup 2 (zpowers a) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, horder, pow_one]⟩
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  refine ⟨S, hPS (Subgroup.mem_zpowers a), (S : Subgroup X) ⊓ N, inf_le_left, ?_, ?_, ?_⟩
  · have hrel : ((S : Subgroup X) ⊓ N).relIndex (S : Subgroup X) =
        N.relIndex (S : Subgroup X) := by
      rw [inf_comm]
      exact Subgroup.inf_relIndex_right N (S : Subgroup X)
    rw [hrel]
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    have hdvd_idx : N.relIndex (S : Subgroup X) ∣ N.index :=
      relIndex_dvd_index_of_normal N (S : Subgroup X)
    have hdvd_card : N.relIndex (S : Subgroup X) ∣ Nat.card (S : Subgroup X) :=
      relIndex_dvd_card N (S : Subgroup X)
    have hdvd_pow : N.relIndex (S : Subgroup X) ∣ 2 ^ n := by
      rw [← hn]; exact hdvd_card
    obtain ⟨k, _hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd_pow
    have hk_le1 : k ≤ 1 := by
      by_contra h
      have h2k : 2 ≤ k := by omega
      have h4 : 4 ∣ 2 ^ k := by
        have h := pow_dvd_pow 2 h2k
        norm_num at h
        exact h
      have h4' : 4 ∣ N.relIndex (S : Subgroup X) := by rw [hk]; exact h4
      exact hidx (h4'.trans hdvd_idx)
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · have h1 : N.relIndex (S : Subgroup X) = 1 := by rw [hk]; norm_num
      have hle : (S : Subgroup X) ≤ N := Subgroup.relIndex_eq_one.mp h1
      exact absurd (hle (hPS (Subgroup.mem_zpowers a))) haN
    · rw [hk]; norm_num
  · exact fun h => haN h.2
  · intro w hw
    exact hFus w hw.2

end CFSG.EvenSporadicStandard.Co3Std.CentT
