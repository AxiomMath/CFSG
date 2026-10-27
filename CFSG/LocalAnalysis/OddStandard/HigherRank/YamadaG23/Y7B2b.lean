module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B1b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BAbsD

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_A_le_M6 (c : Ctx7 G L) (hb : B5Std c) : c.s.fr.A ≤ M6 c.e := by
  rw [← hb.h71.2.1.2.1]
  exact inf_le_right

theorem y7b_B_le_M7 (c : Ctx7 G L) (hb : B6Std c) : c.s.fr.B ≤ M7 c.s := by
  rw [← hb.h75.1.2.1]
  exact inf_le_right

theorem y7b_M3_le_M7 (c : Ctx7 G L) : M3 c.s ≤ M7 c.s := by
  unfold M7
  exact le_sup_right.trans le_sup_right

theorem y7b_M5_le_M7 (c : Ctx7 G L) (hb : B6Std c) : M5 c.e ≤ M7 c.s := by
  unfold M5
  exact sup_le (y7b_M3_le_M7 c) hb.h75.2.1.2.1

theorem y7b_card_M6 (c : Ctx7 G L) (hb : B5Std c) : Nat.card ↥(M6 c.e) = 2 ^ 10 := by
  have hH := hb.hH
  have hAV1 : AV1 c.e ≤ M6 c.e := by
    rw [AV1]
    exact sup_le (y7b_A_le_M6 c hb)
      ((show V1 c.e ≤ M3 c.s from inf_le_right).trans hb.h71.2.2.2.1)
  have hzV1 : c.s.fr.z ∈ V1 c.e := by
    rw [c.hV]
    exact Subgroup.subset_closure (by simp)
  have hZV1 : c.s.fr.Z ≤ V1 c.e := by
    rw [SFrame.Z]
    exact Subgroup.zpowers_le.mpr hzV1
  have hV1A : V1 c.e ⊓ c.s.fr.A = c.s.fr.Z := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxV1, hxA⟩ := Subgroup.mem_inf.mp hx
      have hxC0 : x ∈ C0 c.e := (Subgroup.mem_inf.mp hxV1).1
      have hmem : x ∈ C0 c.e ⊓ c.s.fr.A := Subgroup.mem_inf.mpr ⟨hxC0, hxA⟩
      rwa [y5_C0_inf_A hH] at hmem
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hZV1 hx, s3_Z_le_A c.s hx⟩
  have hcardZ : Nat.card ↥(c.s.fr.Z) = 2 := by
    rw [SFrame.Z, Nat.card_zpowers, (lfactsA_of_setting hH.hS hH.hZ c.s).z_order]
  have hZA : c.s.fr.Z.relIndex c.s.fr.A = 16 := by
    have h := Subgroup.relIndex_mul_card (H := c.s.fr.Z) (K := c.s.fr.A)
    rw [inf_of_le_left (s3_Z_le_A c.s), hcardZ, y56_card_A hH] at h
    omega
  have hrel : (AV1 c.e).relIndex (M6 c.e) = 16 := by
    rw [quotModIso_relIndex_eq hb.h71.2.1.2.2.2.2]
    exact hZA
  have hVnorm : V1 c.e ≤ normalizer (c.s.fr.A : Set G) := by
    have hd_cent : c.d ∈ Subgroup.centralizer (c.s.fr.A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (mul_inv_eq_iff_eq_mul.mp (y5_d_cent_A c.toCtx5 a ha)).symm
    rw [c.hV]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.le_normalizer (s3_z_mem_A c.s)
    · exact Subgroup.centralizer_le_normalizer _ hd_cent
  have hcardAV1 : Nat.card ↥(AV1 c.e) = 64 := by
    have h := card_sup_mul_card_inf_of_le_normalizer (H := V1 c.e) (K := c.s.fr.A) hVnorm
    rw [hV1A, hcardZ, y7b_card_V1 c hb, y56_card_A hH] at h
    have hsup : AV1 c.e = V1 c.e ⊔ c.s.fr.A := by rw [AV1, sup_comm]
    rw [hsup]
    omega
  have hcardM6 : Nat.card ↥(M6 c.e) = 16 * Nat.card ↥(AV1 c.e) := by
    have h := Subgroup.relIndex_mul_card (H := AV1 c.e) (K := M6 c.e)
    rw [inf_of_le_left hAV1] at h
    rw [← h, hrel]
  rw [hcardM6, hcardAV1]
  norm_num

theorem y7b_card_M7 (c : Ctx7 G L) (hb : B6Std c) : Nat.card ↥(M7 c.s) = 2 ^ 10 := by
  have hb5 := hb.toB5Std
  have hH := hb5.hH
  have hBM3_le : c.s.fr.B ⊔ M3 c.s ≤ M7 c.s :=
    sup_le (y7b_B_le_M7 c hb) (y7b_M3_le_M7 c)
  have hBH : c.s.fr.B ≤ c.s.H :=
    (s3_B_le_S c.s).trans ((s3_S_le_L c.s).trans (s3_L_le_H c.s hH.hS))
  have hFB : c.s.fr.F ≤ c.s.fr.B := y54_F_le_B hH
  have hFM3 : c.s.fr.F ≤ M3 c.s := by
    unfold M3
    exact le_sup_right
  have hBM3 : c.s.fr.B ⊓ M3 c.s = c.s.fr.F := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxB, hxM3⟩ := Subgroup.mem_inf.mp hx
      have hmem : x ∈ c.s.H ⊓ M3 c.s := Subgroup.mem_inf.mpr ⟨hBH hxB, hxM3⟩
      rwa [y54_H_inf_M3 c.toCtx5 hH] at hmem
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hFB hx, hFM3 hx⟩
  have hrel : (c.s.fr.B ⊔ M3 c.s).relIndex (M7 c.s) = 4 := by
    rw [quotModIso_relIndex_eq hb.h75.1.2.2.2]
    have h := Subgroup.relIndex_mul_card (H := c.s.fr.F) (K := c.s.fr.B)
    rw [inf_of_le_left hFB, y7b_card_F hH, y54_card_B hH] at h
    omega
  have hBnorm : c.s.fr.B ≤ normalizer (M3 c.s : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    rw [Subgroup.commutator_le]
    intro r hr m hm
    have h1 := y54_R_norm_M3 c.toCtx5 hH r (y54_B_le_R c.s hr) m hm
    have h3 := (M3 c.s).mul_mem h1 ((M3 c.s).inv_mem hm)
    simpa only [commutatorElement_def] using h3
  have hcardBM3 : Nat.card ↥(c.s.fr.B ⊔ M3 c.s) = 256 := by
    have h := card_sup_mul_card_inf_of_le_normalizer (H := c.s.fr.B) (K := M3 c.s) hBnorm
    rw [hBM3, y7b_card_F hH, y54_card_B hH, y7b_card_M3 c hb5] at h
    omega
  have hcardM7 : Nat.card ↥(M7 c.s) = 4 * Nat.card ↥(c.s.fr.B ⊔ M3 c.s) := by
    have h := Subgroup.relIndex_mul_card (H := c.s.fr.B ⊔ M3 c.s) (K := M7 c.s)
    rw [inf_of_le_left hBM3_le] at h
    rw [← h, hrel]
  rw [hcardM7, hcardBM3]
  norm_num

end CFSG.OddStandard.HigherRank.YamadaG23
