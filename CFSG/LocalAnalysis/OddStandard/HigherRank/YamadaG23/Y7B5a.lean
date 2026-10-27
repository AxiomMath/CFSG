module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B2d
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B3a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7b_t_sq (c : Ctx7 G L) : c.s.t * c.s.t = 1 := by
  rw [← pow_two, ← c.s.t_order]
  exact pow_orderOf_eq_one c.s.t

private lemma y7b_mem_H_iff (c : Ctx7 G L) {x : G} :
    x ∈ c.s.H ↔ x * c.s.t = c.s.t * x := by
  change x ∈ Subgroup.centralizer ({c.s.t} : Set G) ↔ x * c.s.t = c.s.t * x
  exact Subgroup.mem_centralizer_singleton_iff

private lemma y7b_t_mem_C0 (c : Ctx7 G L) : c.s.t ∈ C0 c.e := by
  refine Subgroup.mem_inf.mpr ⟨c.e.T_le (s3_t_mem_T c.s), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_iff.mp c.s.t_mem x (s3_A_le_L c.s hx)

theorem y7b_t_not_mem_AV1 (c : Ctx7 G L) (hb : B5Std c) : c.s.t ∉ AV1 c.e := by
  intro ht
  have hAN : c.s.fr.A ≤ normalizer (V1 c.e : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    have hcomm : a * v = v * a := hb.h72.1.2.2.2.2 a (s3_A_le_S c.s ha) v hv
    simpa [hcomm] using hv
  change c.s.t ∈ c.s.fr.A ⊔ V1 c.e at ht
  obtain ⟨a, ha, v, hv, htav⟩ := (mem_sup_iff_exists_mul_of_le_normalizer hAN).mp ht
  have hAH : c.s.fr.A ≤ c.s.H :=
    (s3_A_le_S c.s).trans ((c.s.S_le_R).trans ((c.s.R_le_T).trans c.s.sylow_T.1))
  have htH : c.s.t ∈ c.s.H := by rw [y7b_mem_H_iff]
  have hvH : v ∈ c.s.H := by
    have hv_eq : v = a⁻¹ * c.s.t := by rw [htav]; group
    rw [hv_eq]
    exact c.s.H.mul_mem (c.s.H.inv_mem (hAH ha)) htH
  have hvZ : v ∈ c.s.fr.Z := by
    rw [← y7b_H_inf_V1 c hb]
    exact ⟨hvH, hv⟩
  have htA : c.s.t ∈ c.s.fr.A := by
    rw [htav]
    exact c.s.fr.A.mul_mem ha (s3_Z_le_A c.s hvZ)
  exact s3_t_not_mem_L_of_odd c.s hb.hH.hZ (s3_A_le_L c.s htA)

theorem y7b_t_not_mem_BM3 (c : Ctx7 G L) (hb : B5Std c) :
    c.s.t ∉ c.s.fr.B ⊔ M3 c.s := by
  intro ht
  have hBN : c.s.fr.B ≤ normalizer (M3 c.s : Set G) :=
    (s3_B_le_S c.s).trans ((c.s.S_le_R).trans (y7b_R_le_NM3 (s := c.s) (e := c.e) hb.hH))
  obtain ⟨b, hbB, m, hmM3, htbm⟩ := (mem_sup_iff_exists_mul_of_le_normalizer hBN).mp ht
  have hBH : c.s.fr.B ≤ c.s.H :=
    (s3_B_le_S c.s).trans ((c.s.S_le_R).trans ((c.s.R_le_T).trans c.s.sylow_T.1))
  have htH : c.s.t ∈ c.s.H := by rw [y7b_mem_H_iff]
  have hmH : m ∈ c.s.H := by
    have hm_eq : m = b⁻¹ * c.s.t := by rw [htbm]; group
    rw [hm_eq]
    exact c.s.H.mul_mem (c.s.H.inv_mem (hBH hbB)) htH
  have hmF : m ∈ c.s.fr.F := by
    rw [← y54_H_inf_M3 c.toCtx5 hb.hH]
    exact ⟨hmH, hmM3⟩
  have htB : c.s.t ∈ c.s.fr.B := by
    rw [htbm]
    exact c.s.fr.B.mul_mem hbB (y54_F_le_B hb.hH hmF)
  exact s3_t_not_mem_L_of_odd c.s hb.hH.hZ (s3_S_le_L c.s (s3_B_le_S c.s htB))

theorem y7b_exists_M6_comm_not_mem_M5 (c : Ctx7 G L) (hb : B6Std c) :
    ∃ k ∈ M6 c.e, ⁅k, c.s.t⁆ ∉ M5 c.e := by
  have hnotAB : ¬ c.s.fr.A ≤ c.s.fr.B := by
    intro hle
    have hcard : Nat.card ↥c.s.fr.A = Nat.card ↥(c.s.fr.A ⊓ c.s.fr.B) := by
      rw [inf_eq_left.mpr hle]
    rw [y56_card_A hb.hH, y7b_card_AB hb.hH] at hcard
    exact absurd hcard (by norm_num)
  obtain ⟨a, ha, haB⟩ := Set.not_subset.mp hnotAB
  have htAV1 : c.s.t ∉ AV1 c.e := y7b_t_not_mem_AV1 c hb.toB5Std
  have htC0 : c.s.t ∈ C0 c.e := y7b_t_mem_C0 c
  have htC1 : c.s.t ∈ C1 c.e := by
    change c.s.t ∈ c.s.fr.A ⊔ C0 c.e
    exact Subgroup.mem_sup_right htC0
  have hatC1 : a * c.s.t ∈ C1 c.e :=
    (C1 c.e).mul_mem (Subgroup.mem_sup_left ha) htC1
  have hat_not : a * c.s.t ∉ AV1 c.e := by
    intro h
    have haAV1 : a ∈ AV1 c.e := Subgroup.mem_sup_left ha
    have : a⁻¹ * (a * c.s.t) ∈ AV1 c.e :=
      (AV1 c.e).mul_mem ((AV1 c.e).inv_mem haAV1) h
    exact htAV1 (by simpa only [inv_mul_cancel_left] using this)
  obtain ⟨_, _, hAct⟩ := hb.h71.2.1.2.2.1
  obtain ⟨k, hkM6, hwV1⟩ := hAct c.s.t htC1 htAV1 (a * c.s.t) hatC1 hat_not
  refine ⟨k, hkM6, fun hcommM5 => ?_⟩
  let w : G := (a * c.s.t)⁻¹ * (k * c.s.t * k⁻¹)
  have hwV1' : w ∈ V1 c.e := hwV1
  have hkw : (a * c.s.t) * w = k * c.s.t * k⁻¹ := by
    change (a * c.s.t) * ((a * c.s.t)⁻¹ * (k * c.s.t * k⁻¹)) = k * c.s.t * k⁻¹
    group
  have hcomm_eq : ⁅k, c.s.t⁆ = a * (c.s.t * w * c.s.t⁻¹) := by
    rw [commutatorElement_def, ← hkw]
    group
  have htwV1 : c.s.t * w * c.s.t⁻¹ ∈ V1 c.e :=
    (y7b_comm_V1_t c hb.toB5Std w hwV1').1
  have haM5 : a ∈ M5 c.e := by
    have ha_eq : a = ⁅k, c.s.t⁆ * (c.s.t * w * c.s.t⁻¹)⁻¹ := by
      rw [hcomm_eq]; group
    rw [ha_eq]
    exact (M5 c.e).mul_mem hcommM5
      ((M5 c.e).inv_mem (y7b_V1_le_M5 c hb.toB5Std htwV1))
  have hAH : c.s.fr.A ≤ c.s.H :=
    (s3_A_le_S c.s).trans ((c.s.S_le_R).trans ((c.s.R_le_T).trans c.s.sylow_T.1))
  have haAB : a ∈ c.s.fr.A ⊓ c.s.fr.B := by
    rw [← y7b_H_inf_M5 c hb]
    exact ⟨hAH ha, haM5⟩
  exact haB (Subgroup.mem_inf.mp haAB).2

theorem y7b_exists_M7_comm_not_mem_M5 (c : Ctx7 G L) (hb : B6Std c) :
    ∃ k ∈ M7 c.s, ⁅k, c.s.t⁆ ∉ M5 c.e := by
  have hnotBA : ¬ c.s.fr.B ≤ c.s.fr.A := by
    intro hle
    have hcard : Nat.card ↥c.s.fr.B = Nat.card ↥(c.s.fr.A ⊓ c.s.fr.B) := by
      rw [inf_eq_right.mpr hle]
    rw [y54_card_B hb.hH, y7b_card_AB hb.hH] at hcard
    exact absurd hcard (by norm_num)
  obtain ⟨b, hbB, hbA⟩ := Set.not_subset.mp hnotBA
  have htBM3 : c.s.t ∉ c.s.fr.B ⊔ M3 c.s := y7b_t_not_mem_BM3 c hb.toB5Std
  have htC3 : c.s.t ∈ C3 c.s := by
    rw [y54_C3_eq_M3 c.toCtx5 hb.hH]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)
  have htBC3 : c.s.t ∈ c.s.fr.B ⊔ C3 c.s := Subgroup.mem_sup_right htC3
  have hbtBC3 : b * c.s.t ∈ c.s.fr.B ⊔ C3 c.s :=
    (c.s.fr.B ⊔ C3 c.s).mul_mem (Subgroup.mem_sup_left hbB) htBC3
  have hbt_not : b * c.s.t ∉ c.s.fr.B ⊔ M3 c.s := by
    intro h
    have hb_inv : b⁻¹ ∈ c.s.fr.B ⊔ M3 c.s :=
      Subgroup.mem_sup_left (c.s.fr.B.inv_mem hbB)
    have : b⁻¹ * (b * c.s.t) ∈ c.s.fr.B ⊔ M3 c.s :=
      (c.s.fr.B ⊔ M3 c.s).mul_mem hb_inv h
    exact htBM3 (by simpa only [inv_mul_cancel_left] using this)
  obtain ⟨_, _, hAct⟩ := hb.h75.1.2.2.1
  obtain ⟨k, hkM7, hwM3⟩ := hAct c.s.t htBC3 htBM3 (b * c.s.t) hbtBC3 hbt_not
  refine ⟨k, hkM7, fun hcommM5 => ?_⟩
  let w : G := (b * c.s.t)⁻¹ * (k * c.s.t * k⁻¹)
  have hwM3' : w ∈ M3 c.s := hwM3
  have hkw : (b * c.s.t) * w = k * c.s.t * k⁻¹ := by
    change (b * c.s.t) * ((b * c.s.t)⁻¹ * (k * c.s.t * k⁻¹)) = k * c.s.t * k⁻¹
    group
  have hcomm_eq : ⁅k, c.s.t⁆ = b * (c.s.t * w * c.s.t⁻¹) := by
    rw [commutatorElement_def, ← hkw]
    group
  have hRN : c.s.R ≤ normalizer (M3 c.s : Set G) :=
    y7b_R_le_NM3 (s := c.s) (e := c.e) hb.hH
  have htwM3 : c.s.t * w * c.s.t⁻¹ ∈ M3 c.s :=
    (Subgroup.mem_normalizer_iff.mp (hRN (s3_t_mem_R c.s)) w).mp hwM3'
  have hbM5 : b ∈ M5 c.e := by
    have hb_eq : b = ⁅k, c.s.t⁆ * (c.s.t * w * c.s.t⁻¹)⁻¹ := by
      rw [hcomm_eq]; group
    rw [hb_eq]
    refine (M5 c.e).mul_mem hcommM5 ((M5 c.e).inv_mem ?_)
    exact Subgroup.mem_sup_left htwM3
  have hBH : c.s.fr.B ≤ c.s.H :=
    (s3_B_le_S c.s).trans ((c.s.S_le_R).trans ((c.s.R_le_T).trans c.s.sylow_T.1))
  have hbAB : b ∈ c.s.fr.A ⊓ c.s.fr.B := by
    rw [← y7b_H_inf_M5 c hb]
    exact ⟨hBH hbB, hbM5⟩
  exact hbA (Subgroup.mem_inf.mp hbAB).1

end CFSG.OddStandard.HigherRank.YamadaG23
