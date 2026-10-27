module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Two
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SH1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Set5

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y6_card_T {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    (s.R = s.T → Nat.card ↥s.T = 128) ∧ (s.R ≠ s.T → Nat.card ↥s.T = 256) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp s.sylow_T.2.1
  have hdvd : 128 ∣ Nat.card ↥s.T := by
    rw [← y6_card_R hH]
    exact Subgroup.card_dvd_of_le s.R_le_T
  have hbound : Nat.card ↥s.T ≤ 256 := by
    have h := y6_card_le_two_mul s.R_le_T (y5_T_cosets hH)
    rw [y6_card_R hH] at h
    omega
  have hn7 : 7 ≤ n := by
    have h : 2 ^ 7 ∣ 2 ^ n := by
      rw [← hn]
      simpa using hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h
  have hn8 : n ≤ 8 := by
    have h : 2 ^ n ≤ 2 ^ 8 := by
      rw [← hn]
      simpa using hbound
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  have hcases : n = 7 ∨ n = 8 := by omega
  constructor
  · intro hRT
    rw [← hRT]
    exact y6_card_R hH
  · intro hne
    have hne128 : Nat.card ↥s.T ≠ 128 := by
      intro h
      have hR128 : Nat.card ↥s.R = 128 := y6_card_R hH
      have hle : Nat.card ↥s.T ≤ Nat.card ↥s.R := by omega
      exact hne (Subgroup.eq_of_le_of_card_ge s.R_le_T hle)
    rcases hcases with h7 | h8
    · rw [hn, h7] at hne128
      exact absurd (by norm_num) hne128
    · rw [hn, h8]
      norm_num

theorem y6_card_NHA {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Nat.card ↥(normIn s.H s.fr.A) = 9 * Nat.card ↥s.T := by
  let N := normIn s.H s.fr.A
  let M := L ⊔ centIn s.H L
  have hNH : N ≤ s.H := inf_le_left
  have hMH : M ≤ s.H := s3_M_le_H s hH.hS
  have hTH : s.T ≤ s.H := s.sylow_T.1
  have hRM : s.R ≤ M := s.sylow_R.1
  have hTcard := y6_card_T hH
  by_cases hRT : s.R = s.T
  · have hNM : N ≤ M := by
      by_contra hNM
      obtain ⟨x, hxN, hxM⟩ := SetLike.not_le_iff_exists.mp hNM
      have hxH : x ∈ s.H := hNH hxN
      have hMHne : M ≠ s.H := fun h => hxM (h.symm ▸ hxH)
      have hle2 : Nat.card ↥s.H ≤ 2 * Nat.card ↥M :=
        y6_card_le_two_mul hMH (y5_H_cosets hH)
      have hrelpos : 0 < M.relIndex s.H :=
        Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card M s.H) Nat.card_pos
      have hne1 : M.relIndex s.H ≠ 1 := fun h =>
        hMHne ((Subgroup.relIndex_eq_one.mp h).antisymm hMH).symm
      have hle : M.relIndex s.H ≤ 2 := by
        have hmul : M.relIndex s.H * Nat.card ↥M ≤ 2 * Nat.card ↥M := by
          have h := Subgroup.relIndex_mul_card (H := M) (K := s.H)
          rw [inf_of_le_left hMH] at h
          rw [h]
          exact hle2
        exact Nat.le_of_mul_le_mul_right hmul Nat.card_pos
      have hMrel : M.relIndex s.H = 2 := by omega
      have hcardH : Nat.card ↥s.H = 2 * Nat.card ↥M := by
        have h := Subgroup.relIndex_mul_card (H := M) (K := s.H)
        rw [inf_of_le_left hMH, hMrel] at h
        exact h.symm
      have hHcard : Nat.card ↥s.H = s.T.relIndex s.H * Nat.card ↥s.T := by
        have h := Subgroup.relIndex_mul_card (H := s.T) (K := s.H)
        rw [inf_of_le_left hTH] at h
        exact h.symm
      have hRcard : Nat.card ↥M = s.R.relIndex M * Nat.card ↥s.R := by
        have h := Subgroup.relIndex_mul_card (H := s.R) (K := M)
        rw [inf_of_le_left hRM] at h
        exact h.symm
      have hmain : s.T.relIndex s.H * Nat.card ↥s.T
          = 2 * (s.R.relIndex M * Nat.card ↥s.R) :=
        calc s.T.relIndex s.H * Nat.card ↥s.T
            = Nat.card ↥s.H := hHcard.symm
          _ = 2 * Nat.card ↥M := hcardH
          _ = 2 * (s.R.relIndex M * Nat.card ↥s.R) := by rw [hRcard]
      have hcancel : s.T.relIndex s.H = 2 * s.R.relIndex M := by
        have h2 : s.T.relIndex s.H * Nat.card ↥s.T
            = (2 * s.R.relIndex M) * Nat.card ↥s.T := by
          rw [hmain, hRT]
          ring
        exact Nat.mul_right_cancel Nat.card_pos h2
      exact s.sylow_T.2.2 ⟨s.R.relIndex M, hcancel⟩
    have hinf : N ⊓ M = N := inf_eq_left.mpr hNM
    have h1152 : Nat.card ↥N = 1152 := by
      have h := y6_card_NHA_inf_M hH
      change Nat.card ↥(N ⊓ M) = 1152 at h
      rwa [hinf] at h
    change Nat.card ↥N = 9 * Nat.card ↥s.T
    rw [h1152, hTcard.1 hRT]
  · have hlt : s.R < s.T := lt_of_le_of_ne s.R_le_T hRT
    obtain ⟨x, hxT, hxR⟩ := SetLike.exists_of_lt hlt
    have hxN : x ∈ N := s5_T_le_NHA hH hxT
    have hxM : x ∉ M := s3_not_mem_M s hH.hS hxT hxR
    have hNMne : N ⊓ M ≠ N := fun h => hxM (Subgroup.mem_inf.mp (h.symm ▸ hxN)).2
    have hNle : Nat.card ↥N ≤ 2 * Nat.card ↥(N ⊓ M) :=
      y6_card_le_two_mul inf_le_left (by
        intro a ha b hb
        have haH : a ∈ s.H := hNH ha
        have hbH : b ∈ s.H := hNH hb
        rcases y5_H_cosets hH a haH b hbH with h | h | h
        · exact Or.inl (Subgroup.mem_inf.mpr ⟨ha, h⟩)
        · exact Or.inr (Or.inl (Subgroup.mem_inf.mpr ⟨hb, h⟩))
        · exact Or.inr (Or.inr (Subgroup.mem_inf.mpr
            ⟨Subgroup.mul_mem N (Subgroup.inv_mem N ha) hb, h⟩)))
    have h1152 : Nat.card ↥(N ⊓ M) = 1152 := y6_card_NHA_inf_M hH
    have hNle' : Nat.card ↥N ≤ 2304 := by
      have h := hNle
      rw [h1152] at h
      omega
    have hNne1152 : Nat.card ↥N ≠ 1152 := by
      intro h
      have hle : Nat.card ↥N ≤ Nat.card ↥(N ⊓ M) := by omega
      exact hNMne (Subgroup.eq_of_le_of_card_ge inf_le_left hle)
    have hN2304 : Nat.card ↥N = 2304 := by
      obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (H := N ⊓ M) (K := N) inf_le_left
      rw [h1152] at hk
      have hpos : 0 < Nat.card ↥N := Nat.card_pos
      omega
    change Nat.card ↥N = 9 * Nat.card ↥s.T
    rw [hN2304, hTcard.2 hRT]

end CFSG.OddStandard.HigherRank.YamadaG23
