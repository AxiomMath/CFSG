module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue3

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

theorem cfg1K_of_std {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G}
    (hII : II4_4_4_center) (hq : II4_4_quat) (hdiag : IVK_diag_unique) (h19 : IVK_1_9_outer)
    (hsd : SD_facts) (hsdq : SD_sq_not_z) (hqc : Quat_centr) (hrn : Rnormal4)
    (h : Std4r1 G z S K F) :
    R1.Cfg1K G z S (S ⊓ K) (S ⊓ cSec K) F (fun s => InducesFAut s K) := by
  obtain ⟨n, hn⟩ := h.P_quat hq
  have hzP := h.z_mem_P hII
  refine
    { z_sq := h.z_sq
      z_ne := h.z_ne
      S_syl := h.S_top
      z_mem := h.z_mem_S
      z_cent := fun s hs => h.z_cent hs
      Z_cyc := h.Z_cyc
      Z_inv := fun x hx hc h2 => h.Z_inv hx hc h2
      simp := h.simple.1
      nonab := h.simple.2.1
      P_le := inf_le_left
      P_norm := fun s hs p hp => h.P_norm hs hp
      Q_le := inf_le_left
      Q_norm := fun s hs q hq => h.Q_norm hs hq
      PQ_comm := fun p hp q hq => h.comm_PQ hp hq
      PQ_inf := fun x hxP hxQ => h.PQ_inf hII hxP hxQ
      z_P := hzP
      z_Q := h.z_mem_Q hII
      P_inv := fun p hp hp2 => h.P_inv hII hp hp2
      P_centr := fun u hu hu2 hnorm => ?_
      P_exp := fun p hp => P_exp_of_quat hn p hp
      F_le := h.F_le
      Q_eq := ?_
      idx := ?_
      inv_fa := ?_
      rank3 := h.hasE8
      diag := ?_
      sd := ?_
      sdf := ?_
      rn4 := ?_
      cent_rank := ?_ }
  · obtain ⟨hc, hi⟩ := hqc G (S ⊓ K) z u n hn hzP h.z_sq h.z_ne hu hu2 (fun p hp => hnorm p hp.1)
    exact ⟨_, rfl, hc, hi⟩
  · have := h.Q_eq
    rw [h.Qz_eq, h.Rz_eq] at this
    exact this
  · have := h.index_le
    rwa [h.Pz_eq] at this
  · intro s hs hs2 hfa
    by_cases hs1 : s = 1
    · rw [hs1]; exact one_mem _
    · have := h.inv_fAut s hs (orderOf_eq_two_of_mul_self_eq_one hs2 hs1) hfa
      rwa [h.Pz_eq] at this
  · intro s hs y hy hs2 hy2 hsR hyR hfs hfy
    have hsR' : s ∉ Rz S z := by rw [h.Rz_eq]; exact hsR
    have hyR' : y ∉ Rz S z := by rw [h.Rz_eq]; exact hyR
    have := hdiag G z S K h.toStd6r1 s hs y hy hs2 hy2 hsR' hyR' hfs hfy
    rwa [h.Rz_eq] at this
  · intro y hy hy2 hyR hfy
    have hyR' : y ∉ Rz S z := by rw [h.Rz_eq]; exact hyR
    have hy1 : y ≠ 1 := fun e => hyR (e ▸ one_mem _)
    have := (h19 G z S K h.toStd6r1 y hy (orderOf_eq_two_of_mul_self_eq_one hy2 hy1) hyR' hfy).1
    rwa [h.Pz_eq] at this
  · intro y hy2 hyP hnorm hSD
    exact ⟨(hsd G (S ⊓ K) z y ⟨n, hn⟩ hzP h.z_sq h.z_ne hy2 hyP hnorm hSD).1,
      (hsd G (S ⊓ K) z y ⟨n, hn⟩ hzP h.z_sq h.z_ne hy2 hyP hnorm hSD).2,
      hsdq G (S ⊓ K) z y ⟨n, hn⟩ hzP h.z_sq h.z_ne hy2 hyP hnorm hSD⟩
  · intro hQ
    have hQ' : Qz S z ≠ zpowers z := by rw [h.Qz_eq]; exact hQ
    obtain ⟨U, hUR, hU4, hUn⟩ := hrn G z S K F h hQ'
    rw [h.Rz_eq] at hUR
    refine ⟨U, hUR, ⟨?_, hU4.2⟩, hUn⟩
    intro a ha
    have := hU4.1
    have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) a ha
    simpa [pow_two] using h2
  · intro U hUS hU4 hUn
    exact h.cent_rank hUS hU4.1 hU4.2 hUn

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
