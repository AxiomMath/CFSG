module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B2a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B2c

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y7b_AB_le_H (c : Ctx7 G L) (hb : B5Std c) :
    c.s.fr.A ⊓ c.s.fr.B ≤ c.s.H :=
  inf_le_left.trans
    (((s3_A_le_S c.s).trans (s3_S_le_L c.s)).trans (s3_L_le_H c.s hb.hH.hS))

private theorem y7b_AB_le_NV2 (c : Ctx7 G L) (hb : B5Std c) :
    c.s.fr.A ⊓ c.s.fr.B ≤ normalizer (V2 c.e : Set G) :=
  inf_le_left.trans (((s3_A_le_S c.s).trans c.s.S_le_R).trans (y7b_R_le_NV2 c hb))

private theorem y7b_V2_le_M5 (c : Ctx7 G L) (hb : B5Std c) : V2 c.e ≤ M5 c.e := by
  rw [V2, M5]
  exact inf_le_left.trans le_sup_left

private theorem y7b_EFV2_eq_sup (c : Ctx7 G L) (hb : B5Std c) :
    EFV2 c.e = (c.s.fr.A ⊓ c.s.fr.B) ⊔ V2 c.e := by
  rw [EFV2, y7b_EF_eq hb.hH]

private theorem y7b_AB_inf_V2 (c : Ctx7 G L) (hb : B5Std c) :
    (c.s.fr.A ⊓ c.s.fr.B) ⊓ V2 c.e = cen c.s.fr.B := by
  have hEAB : c.s.fr.E ≤ c.s.fr.A ⊓ c.s.fr.B := by
    rw [← y7b_EF_eq hb.hH]; exact le_sup_left
  have hFAB : c.s.fr.F ≤ c.s.fr.A ⊓ c.s.fr.B := by
    rw [← y7b_EF_eq hb.hH]; exact le_sup_right
  have hcAB : cen c.s.fr.B ≤ c.s.fr.A ⊓ c.s.fr.B := by
    rw [← y7b_E_inf_F hb.hH]
    exact le_inf (inf_le_left.trans (hEAB.trans inf_le_left))
      (inf_le_right.trans (hFAB.trans inf_le_right))
  refine le_antisymm ?_ ?_
  · rw [← y7b_H_inf_V2 c hb]
    exact le_inf (inf_le_left.trans (y7b_AB_le_H c hb)) inf_le_right
  · exact le_inf hcAB (y7b_V_le_V2 c hb)

theorem y7b_phi_M3 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ f ∈ c.s.fr.F, ∃ m ∈ M3 c.s, ⁅m, c.s.t⁆ = f := by
  intro f hf
  obtain ⟨m, hm, hmφ⟩ :=
    y54_phi_M (c := c.toCtx5) hb.hH (y54_M3_cand c.toCtx5 hb.hH) (M := M3 c.s) f hf
  exact ⟨m, hm, by simpa only [f3phi, commutatorElement_def] using hmφ⟩

theorem y7b_V2_le_EFV2 (c : Ctx7 G L) (hb : B5Std c) : V2 c.e ≤ EFV2 c.e := by
  rw [EFV2]
  exact le_sup_right

theorem y7b_EFV2_le_M5 (c : Ctx7 G L) (hb : B5Std c) : EFV2 c.e ≤ M5 c.e := by
  have hF3 : c.s.fr.F ≤ M3 c.s := by rw [M3]; exact le_sup_right
  have hV23 : V2 c.e ≤ M3 c.s := by rw [V2]; exact inf_le_left
  have hE4 : c.s.fr.E ≤ M4 c.e := y7b_E_le_M4 c hb
  rw [EFV2, M5]
  exact sup_le (sup_le (hE4.trans le_sup_right) (hF3.trans le_sup_left))
    (hV23.trans le_sup_left)

theorem y7b_card_EFV2 (c : Ctx7 G L) (hb : B5Std c) : Nat.card ↥(EFV2 c.e) = 2 ^ 6 := by
  have hcard := card_sup_mul_card_inf_of_le_normalizer
    (H := c.s.fr.A ⊓ c.s.fr.B) (K := V2 c.e) (y7b_AB_le_NV2 c hb)
  rw [y7b_AB_inf_V2 c hb, y7b_card_AB hb.hH, hb.h72.1.2.2.2.1, y7b_card_V hb.hH] at hcard
  rw [y7b_EFV2_eq_sup c hb]
  norm_num at hcard ⊢
  omega

theorem y7b_EFV2_comm_t (c : Ctx7 G L) (hb : B5Std c) :
    ∀ y ∈ EFV2 c.e, ⁅c.s.t, y⁆ ∈ V2 c.e := by
  intro y hy
  rw [y7b_EFV2_eq_sup c hb] at hy
  obtain ⟨w, hw, v, hv, rfl⟩ :=
    (mem_sup_iff_exists_mul_of_le_normalizer (y7b_AB_le_NV2 c hb)).mp hy
  have hwH : w ∈ c.s.H := y7b_AB_le_H c hb hw
  have htw : c.s.t * w = w * c.s.t :=
    Subgroup.mem_centralizer_iff.mp hwH c.s.t (by simp)
  have hNV2 : c.s.t ∈ normalizer (V2 c.e : Set G) := y7b_R_le_NV2 c hb (s3_t_mem_R c.s)
  have htv : c.s.t * v * c.s.t⁻¹ ∈ V2 c.e := (Subgroup.mem_normalizer_iff.mp hNV2 v).mp hv
  have hnv : c.s.t * v * c.s.t⁻¹ * v⁻¹ ∈ V2 c.e := (V2 c.e).mul_mem htv ((V2 c.e).inv_mem hv)
  have hwtv : w * (c.s.t * v * c.s.t⁻¹ * v⁻¹) * w⁻¹ ∈ V2 c.e :=
    (Subgroup.mem_normalizer_iff.mp (y7b_AB_le_NV2 c hb hw) _).mp hnv
  rw [commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_eq_one_iff_mul_comm.mpr htw, one_mul]
  simpa only [commutatorElement_def] using hwtv

theorem y7b_EFV2_onto (c : Ctx7 G L) (hb : B5Std c) :
    ∀ y ∈ EFV2 c.e, ∃ m ∈ M5 c.e, y⁻¹ * ⁅m, c.s.t⁆ ∈ V2 c.e := by
  intro y hy
  rw [y7b_EFV2_eq_sup c hb] at hy
  obtain ⟨w, hw, v, hv, rfl⟩ :=
    (mem_sup_iff_exists_mul_of_le_normalizer (y7b_AB_le_NV2 c hb)).mp hy
  obtain ⟨e, he, f, hf, rfl⟩ := (y7b_mem_EF hb.hH).mp hw
  obtain ⟨m₁, hm₁, hφ₁⟩ := y7b_phi_M4 c hb e he
  obtain ⟨m₂, hm₂, hφ₂⟩ := y7b_phi_M3 c hb f hf
  have hm₂M5 : m₂ ∈ M5 c.e := by
    change m₂ ∈ M3 c.s ⊔ M4 c.e
    exact Subgroup.mem_sup_left hm₂
  have heM5 : e ∈ M5 c.e := by
    change e ∈ M3 c.s ⊔ M4 c.e
    exact Subgroup.mem_sup_right (y7b_E_le_M4 c hb he)
  have heM6 : e ∈ M6 c.e := y7b_M5_le_M6 c hb heM5
  have hfM5 : f ∈ M5 c.e := by
    change f ∈ M3 c.s ⊔ M4 c.e
    exact Subgroup.mem_sup_left (by rw [M3]; exact Subgroup.mem_sup_right hf)
  have hfM6 : f ∈ M6 c.e := y7b_M5_le_M6 c hb hfM5
  have hm₁M5 : m₁ ∈ M5 c.e := by
    change m₁ ∈ M3 c.s ⊔ M4 c.e
    exact Subgroup.mem_sup_right hm₁
  have hceV2 : ⁅m₂, e⁆ ∈ V2 c.e :=
    y7b_V1_le_V2 c hb ((y7b_M5_comm_sq c hb).1 m₂ hm₂M5 e heM5)
  refine ⟨m₂ * m₁, (M5 c.e).mul_mem hm₂M5 hm₁M5, ?_⟩
  have heq : ⁅m₂ * m₁, c.s.t⁆ = (⁅m₂, e⁆ * e) * f := by
    rw [commutatorElement_mul_left_eq_conj_mul, hφ₁, hφ₂, commutatorElement_def]
    group
  rw [heq]
  have hconj_e : e⁻¹ * ⁅m₂, e⁆ * e ∈ V2 c.e := by
    have h1 := y7b_M6_norm_V2 c hb e⁻¹ ((M6 c.e).inv_mem heM6) ⁅m₂, e⁆ hceV2
    simpa using h1
  have hconj_f : f⁻¹ * (e⁻¹ * ⁅m₂, e⁆ * e) * f ∈ V2 c.e := by
    have h1 := y7b_M6_norm_V2 c hb f⁻¹ ((M6 c.e).inv_mem hfM6) _ hconj_e
    simpa using h1
  have htot : v⁻¹ * (f⁻¹ * (e⁻¹ * ⁅m₂, e⁆ * e) * f) ∈ V2 c.e :=
    (V2 c.e).mul_mem ((V2 c.e).inv_mem hv) hconj_f
  convert htot using 1
  group

theorem y7b_mem_EFV2 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ m ∈ M5 c.e, ⁅c.s.t, m⁆ ∈ V2 c.e → m ∈ EFV2 c.e := by
  have htt : c.s.t * c.s.t = 1 := by
    rw [← pow_two, ← c.s.t_order]
    exact pow_orderOf_eq_one c.s.t
  have htR : c.s.t ∈ c.s.R := s3_t_mem_R c.s
  have htM : ∀ m ∈ M5 c.e, c.s.t * m * c.s.t⁻¹ ∈ M5 c.e :=
    fun m hm => (Subgroup.mem_normalizer_iff.mp (y7b_R_le_NM5 c hb htR) m).mp hm
  have htV : ∀ v ∈ V2 c.e, c.s.t * v * c.s.t⁻¹ ∈ V2 c.e :=
    fun v hv => (Subgroup.mem_normalizer_iff.mp (y7b_R_le_NV2 c hb htR) v).mp hv
  have hMc : ∀ m ∈ M5 c.e, ∀ n ∈ M5 c.e, ⁅m, n⁆ ∈ V2 c.e :=
    fun m hm n hn => y7b_V1_le_V2 c hb ((y7b_M5_comm_sq c hb).1 m hm n hn)
  have hMsq : ∀ m ∈ M5 c.e, m ^ 2 ∈ V2 c.e :=
    fun m hm => y7b_V1_le_V2 c hb ((y7b_M5_comm_sq c hb).2 m hm)
  have hcard : (V2 c.e).relIndex (M5 c.e) = ((V2 c.e).relIndex (EFV2 c.e)) ^ 2 := by
    have h1 : (V2 c.e).relIndex (M5 c.e) = 2 ^ 4 := by
      have h := Subgroup.relIndex_mul_card (H := V2 c.e) (K := M5 c.e)
      rw [inf_of_le_left (y7b_V2_le_M5 c hb), hb.h72.1.2.2.2.1, y7b_card_M5 c hb] at h
      norm_num at h ⊢
      omega
    have h2 : (V2 c.e).relIndex (EFV2 c.e) = 2 ^ 2 := by
      have h := Subgroup.relIndex_mul_card (H := V2 c.e) (K := EFV2 c.e)
      rw [inf_of_le_left (y7b_V2_le_EFV2 c hb), hb.h72.1.2.2.2.1, y7b_card_EFV2 c hb] at h
      norm_num at h ⊢
      omega
    rw [h1, h2]
    norm_num
  exact mem_of_comm_mem_of_relIndex_sq htt (y7b_V2_le_M5 c hb) hMc hMsq htM htV
    (y7b_V2_le_EFV2 c hb) (y7b_EFV2_le_M5 c hb) (y7b_EFV2_comm_t c hb)
    (y7b_EFV2_onto c hb) hcard

end CFSG.OddStandard.HigherRank.YamadaG23
