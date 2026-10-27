module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7r

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_conj_cent_V2 (c : Ctx7 G L) (hb : B5Std c) {n y : G}
    (hn : n ∈ normIn c.s.H c.s.fr.B) (hy : ∀ v ∈ V2 c.e, y * v = v * y) :
    ∀ v ∈ V2 c.e, (n * y * n⁻¹) * v = v * (n * y * n⁻¹) := by
  intro v hv
  have hn' : n⁻¹ ∈ normIn c.s.H c.s.fr.B := (normIn c.s.H c.s.fr.B).inv_mem hn
  have hv' : n⁻¹ * v * n ∈ V2 c.e := by
    simpa using (Subgroup.mem_normalizer_iff.mp (y7b_NH_le_NV2 c hb hn') v).mp hv
  calc (n * y * n⁻¹) * v = n * (y * (n⁻¹ * v * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * v * n) * y) * n⁻¹ := by rw [hy (n⁻¹ * v * n) hv']
    _ = v * (n * y * n⁻¹) := by group

theorem y7b_trace_mem_BM (c : Ctx7 G L) (hb : B5Std c) {k : G} (hkN : k ∈ normIn L c.s.fr.B)
    (hk3 : k ^ 3 = 1)
    (hfp : ∀ u ∈ y7bBM c.s, u⁻¹ * (k * u * k⁻¹) ∈ M3 c.s → u ∈ M3 c.s) {y : G} (hy : y ∈ C7 c.s)
    (hcV : ∀ v ∈ V2 c.e, y * v = v * y) :
    y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹) ∈ y7bBM c.s := by
  have hkNH : k ∈ normIn c.s.H c.s.fr.B := ⟨s3_L_le_H c.s hb.hH.hS hkN.1, hkN.2⟩
  have hk2N : k ^ 2 ∈ normIn L c.s.fr.B := Subgroup.pow_mem (normIn L c.s.fr.B) hkN 2
  have hk2NH : k ^ 2 ∈ normIn c.s.H c.s.fr.B :=
    ⟨s3_L_le_H c.s hb.hH.hS hk2N.1, hk2N.2⟩
  have hc2 : k * y * k⁻¹ ∈ C7 c.s := (y7b_C7_normal c hb).2 k hkNH y hy
  have hc3 : k ^ 2 * y * (k ^ 2)⁻¹ ∈ C7 c.s := (y7b_C7_normal c hb).2 (k ^ 2) hk2NH y hy
  have hc2V : ∀ v ∈ V2 c.e, (k * y * k⁻¹) * v = v * (k * y * k⁻¹) :=
    y7b_conj_cent_V2 c hb hkNH hcV
  have hc3V : ∀ v ∈ V2 c.e, (k ^ 2 * y * (k ^ 2)⁻¹) * v = v * (k ^ 2 * y * (k ^ 2)⁻¹) :=
    y7b_conj_cent_V2 c hb hk2NH hcV
  have hzC7 : y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹) ∈ C7 c.s :=
    (C7 c.s).mul_mem ((C7 c.s).mul_mem hy hc2) hc3
  have hzV : ∀ v ∈ V2 c.e,
      (y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹)) * v =
        v * (y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹)) := by
    intro v hv
    calc (y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹)) * v
        = y * ((k * y * k⁻¹) * ((k ^ 2 * y * (k ^ 2)⁻¹) * v)) := by group
      _ = y * ((k * y * k⁻¹) * (v * (k ^ 2 * y * (k ^ 2)⁻¹))) := by rw [hc3V v hv]
      _ = y * (((k * y * k⁻¹) * v) * (k ^ 2 * y * (k ^ 2)⁻¹)) := by group
      _ = y * ((v * (k * y * k⁻¹)) * (k ^ 2 * y * (k ^ 2)⁻¹)) := by rw [hc2V v hv]
      _ = (y * v) * ((k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹)) := by group
      _ = (v * y) * ((k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹)) := by rw [hcV v hv]
      _ = v * (y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹)) := by group
  have hkz : k * (y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹)) * k⁻¹ =
      (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹) * y := by
    have h2 : k * (k * y * k⁻¹) * k⁻¹ = k ^ 2 * y * (k ^ 2)⁻¹ := by
      rw [pow_two, mul_inv_rev]
      group
    have h3 : k * (k ^ 2 * y * (k ^ 2)⁻¹) * k⁻¹ = y := by
      have hk : k * k ^ 2 = k ^ 3 := (pow_succ' k 2).symm
      calc k * (k ^ 2 * y * (k ^ 2)⁻¹) * k⁻¹
          = (k * k ^ 2) * y * ((k ^ 2)⁻¹ * k⁻¹) := by group
        _ = k ^ 3 * y * (k ^ 3)⁻¹ := by rw [← mul_inv_rev, hk]
        _ = y := by rw [hk3]; group
    calc k * (y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹)) * k⁻¹
        = (k * y * k⁻¹) * (k * (k * y * k⁻¹) * k⁻¹) *
            (k * (k ^ 2 * y * (k ^ 2)⁻¹) * k⁻¹) := by group
      _ = (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹) * y := by rw [h2, h3]
  have hcommBM : (y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹))⁻¹ *
      (k * (y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹)) * k⁻¹) ∈ y7bBM c.s := by
    rw [hkz]
    have heq : (y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹))⁻¹ *
        ((k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹) * y) =
        ⁅((k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹))⁻¹, y⁻¹⁆ := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact y7b_C7_comm_mem_BM c hb ((k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹))⁻¹
      ((C7 c.s).inv_mem ((C7 c.s).mul_mem hc2 hc3)) y⁻¹ ((C7 c.s).inv_mem hy)
  have hzW : y * (k * y * k⁻¹) * (k ^ 2 * y * (k ^ 2)⁻¹) ∈ y7bW c.s :=
    y7b_hfix2 c hb hkN hfp _ hzC7 (y7b_BM_le_W c hb hcommBM)
  rcases (y7b_mem_W c hb).mp hzW with ⟨w, hw, hzw | hzw⟩
  · rw [hzw]; exact hw
  · exfalso
    obtain ⟨v, hv, hvt⟩ := y7b_exists_V2_not_comm_t c hb
    have hwv : w * v = v * w := y7b_BM_cent_V2 c hb w hw v hv
    have hzv : (w * c.s.t) * v = v * (w * c.s.t) := by
      rw [← hzw]; exact hzV v hv
    have ht : c.s.t * v = v * c.s.t := by
      calc c.s.t * v = w⁻¹ * (w * (c.s.t * v)) := by group
        _ = w⁻¹ * ((w * c.s.t) * v) := by group
        _ = w⁻¹ * (v * (w * c.s.t)) := by rw [hzv]
        _ = (w⁻¹ * v * w) * c.s.t := by group
        _ = (w⁻¹ * (v * w)) * c.s.t := by group
        _ = (w⁻¹ * (w * v)) * c.s.t := by rw [← hwv]
        _ = v * c.s.t := by group
    exact absurd (commutatorElement_eq_one_iff_mul_comm.mpr ht.symm) hvt

theorem y7b_cent_V2_le_M7 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ y ∈ C7 c.s, (∀ v ∈ V2 c.e, y * v = v * y) → y ∈ M7 c.s := by
  intro y hy hcV
  obtain ⟨k, hkN, hk3, -, -, hfp, -⟩ := y7b_exists_k c hb
  have hkNH : k ∈ normIn c.s.H c.s.fr.B := ⟨s3_L_le_H c.s hb.hH.hS hkN.1, hkN.2⟩
  obtain ⟨x, hxC7, hxmem⟩ :=
    y7b_exp2_cube (Z := y7bBM c.s) (P := C7 c.s)
      ((y7b_BM_le_W c hb).trans (y7b_W_le_C7 c hb))
      (y7b_extCtx2 c hb).P_Y (y7b_C7_comm_mem_BM c hb) (y7b_C7_sq_mem_BM c hb)
      hk3 (fun u hu => (y7b_C7_normal c hb).2 k hkNH u hu)
      (fun z hz => (y7b_extCtx2 c hb).P_N k hkN z hz) hy
      (y7b_trace_mem_BM c hb hkN hk3 hfp hy hcV)
  have hxM7 : ⁅x, k⁆ ∈ M7 c.s := by
    rw [M7]
    exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hxC7 hkN)
  have hyinv : y⁻¹ ∈ M7 c.s := by
    rw [show y⁻¹ = (⁅x, k⁆)⁻¹ * (⁅x, k⁆ * y⁻¹) by group]
    exact (M7 c.s).mul_mem ((M7 c.s).inv_mem hxM7) (y7b_BM_le_M7 c hb hxmem)
  simpa using (M7 c.s).inv_mem hyinv

theorem y7b_M4_le_M7_of_R_eq_T (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R = c.s.T) :
    M4 c.e ≤ M7 c.s := by
  intro m hmM4
  refine y7b_cent_V2_le_M7 c hb m
    (y7b_X7_eq_C7_of_R_eq_T c hb hRT m (y7b_M4_le_X7 c hb hmM4)) (fun v hv => ?_)
  haveI : IsMulCommutative ↥(M4 c.e) := (hb.h72.2.1).1
  exact congrArg Subtype.val
    (mul_comm' (⟨m, hmM4⟩ : ↥(M4 c.e)) ⟨v, (Subgroup.mem_inf.mp hv).2⟩)

theorem y7b_M4_cases_M7_g (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    ∀ m ∈ M4 c.e, m ∈ M7 c.s ∨ m * c.g ∈ M7 c.s := by
  intro m hmM4
  rcases y7b_X7_cases_C7_g c hb hRT m (y7b_M4_le_X7 c hb hmM4) with hmC7 | hmgC7
  · left
    refine y7b_cent_V2_le_M7 c hb m hmC7 (fun v hv => ?_)
    haveI : IsMulCommutative ↥(M4 c.e) := (hb.h72.2.1).1
    exact congrArg Subtype.val
      (mul_comm' (⟨m, hmM4⟩ : ↥(M4 c.e)) ⟨v, (Subgroup.mem_inf.mp hv).2⟩)
  · right
    refine y7b_cent_V2_le_M7 c hb (m * c.g) hmgC7 (fun v hv => ?_)
    have hmv : m * v = v * m := by
      haveI : IsMulCommutative ↥(M4 c.e) := (hb.h72.2.1).1
      exact congrArg Subtype.val
        (mul_comm' (⟨m, hmM4⟩ : ↥(M4 c.e)) ⟨v, (Subgroup.mem_inf.mp hv).2⟩)
    have hgv : c.g * v = v * c.g := by
      calc c.g * v = (c.g * v * c.g⁻¹) * c.g := by group
        _ = v * c.g := by rw [y7b_g_cent_V2 c hb hRT v hv]
    calc (m * c.g) * v = m * (c.g * v) := by group
      _ = m * (v * c.g) := by rw [hgv]
      _ = (m * v) * c.g := by group
      _ = (v * m) * c.g := by rw [hmv]
      _ = v * (m * c.g) := by group

theorem y7b_exists_seed3 (c : Ctx7 G L) (hb : B5Std c) :
    ∃ u ∈ M7 c.s, ⁅u, c.s.t⁆ ∉ M3 c.s ∧ u ^ 2 ∈ M3 c.s ∧
      (c.s.R ≠ c.s.T → ⁅c.g, u⁆ ∈ M3 c.s) := by
  obtain ⟨u, huC7, hut, hu2, huV, hug⟩ := y7b_exists_seed2 c hb
  exact ⟨u, y7b_cent_V2_le_M7 c hb u huC7 huV, hut, hu2, hug⟩

end CFSG.OddStandard.HigherRank.YamadaG23
