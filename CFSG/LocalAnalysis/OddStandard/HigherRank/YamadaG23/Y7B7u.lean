module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7s

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_g_mem_NH (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    c.g ∈ normIn c.s.H c.s.fr.B := by
  have hg1 : c.g * c.g = 1 := y7b_g_mul_self c hb hRT
  have hginv : c.g⁻¹ = c.g := inv_eq_of_mul_eq_one_right hg1
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (s3_comm_t_of_mem_T c.s (c.g_spec hRT).1)
  · have hF_le_B : c.s.fr.F ≤ c.s.fr.B := y54_F_le_B hb.hH
    have hforward : ∀ b ∈ c.s.fr.B, c.g * b * c.g⁻¹ ∈ c.s.fr.B := by
      intro b hbB
      have hbN : b ∈ normIn L c.s.fr.B :=
        Subgroup.mem_inf.mpr
          ⟨f3_B_le_L c.s hbB, (Subgroup.le_normalizer (H := c.s.fr.B)) hbB⟩
      have hcomm : ⁅c.g, b⁆ ∈ c.s.fr.F := y7b_g_comm_NL c hb hRT b hbN
      rw [show c.g * b * c.g⁻¹ = ⁅c.g, b⁆ * b by
        rw [commutatorElement_def]; group]
      exact (c.s.fr.B).mul_mem (hF_le_B hcomm) hbB
    refine Subgroup.mem_normalizer_iff.mpr (fun b => ⟨hforward b, ?_⟩)
    intro hb
    have h2 := hforward (c.g * b * c.g⁻¹) hb
    have heq : c.g * (c.g * b * c.g⁻¹) * c.g⁻¹ = b := by
      rw [hginv]
      calc c.g * (c.g * b * c.g) * c.g = (c.g * c.g) * b * (c.g * c.g) := by group
        _ = b := by rw [hg1]; group
    rwa [heq] at h2

theorem y7b_H_inf_M7 (c : Ctx7 G L) (hb : B5Std c) : c.s.H ⊓ M7 c.s = c.s.fr.B := by
  have hB_le_H : c.s.fr.B ≤ c.s.H :=
    (s3_B_le_S c.s).trans ((s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS))
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxH, hxM7⟩ := Subgroup.mem_inf.mp hx
    have hxC7 : x ∈ C7 c.s := y7b_M7_le_C7 c hb hxM7
    have hxX7 : x ∈ X7 c.s := y7b_C7_le_X7 c hb hxC7
    have hxX0 : x ∈ y7bX0 c.s := by
      rw [y7b_X0_iff c hb hxX7]
      have h1 : ⁅x, c.s.t⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hxH)
      rw [h1]
      exact (M3 c.s).one_mem
    have hxW : x ∈ y7bW c.s := by
      have h : x ∈ C7 c.s ⊓ y7bX0 c.s := Subgroup.mem_inf.mpr ⟨hxC7, hxX0⟩
      rwa [y7b_C7_inf_X0 c hb] at h
    have hxBM : x ∈ y7bBM c.s := by
      have h : x ∈ M7 c.s ⊓ y7bW c.s := Subgroup.mem_inf.mpr ⟨hxM7, hxW⟩
      rwa [y7b_M7_inf_W c hb] at h
    have h : x ∈ c.s.H ⊓ y7bBM c.s := Subgroup.mem_inf.mpr ⟨hxH, hxBM⟩
    rwa [y7b_H_inf_BM c hb] at h
  · intro x hx
    exact Subgroup.mem_inf.mpr
      ⟨hB_le_H hx, y7b_BM_le_M7 c hb (Subgroup.mem_sup_left hx)⟩

theorem y7b_X_eq_NM7 (c : Ctx7 G L) (hb : B5Std c) :
    y7bX c.s = normIn c.s.H c.s.fr.B ⊔ M7 c.s := by
  refine le_antisymm ?_ ?_
  · rw [y7b_X_eq_Xp c hb]
    refine sup_le (sup_le le_sup_left ?_) ?_
    · intro m hm
      exact Subgroup.mem_sup_right (y7b_BM_le_M7 c hb (Subgroup.mem_sup_right hm))
    · intro m hm
      by_cases hRT : c.s.R = c.s.T
      · exact Subgroup.mem_sup_right (y7b_M4_le_M7_of_R_eq_T c hb hRT hm)
      · rcases y7b_M4_cases_M7_g c hb hRT m hm with hm7 | hmg
        · exact Subgroup.mem_sup_right hm7
        · have hg : c.g⁻¹ ∈ normIn c.s.H c.s.fr.B :=
            (normIn c.s.H c.s.fr.B).inv_mem (y7b_g_mem_NH c hb hRT)
          have heq : m = (m * c.g) * c.g⁻¹ := by group
          rw [heq]
          exact (normIn c.s.H c.s.fr.B ⊔ M7 c.s).mul_mem
            (Subgroup.mem_sup_right hmg) (Subgroup.mem_sup_left hg)
  · exact sup_le (y7b_N_le_X c hb)
      ((y7b_M7_le_C7 c hb).trans ((y7b_C7_le_X7 c hb).trans (y7b_X7_le_X c)))

theorem y7b_actsTrans (c : Ctx7 G L) (hb : B5Std c) :
    ActsTransOutside (M7 c.s) (c.s.fr.B ⊔ C3 c.s) (M3 c.s) (c.s.fr.B ⊔ M3 c.s) := by
  have hM7_le_X : M7 c.s ≤ y7bX c.s :=
    (y7b_M7_le_C7 c hb).trans ((y7b_C7_le_X7 c hb).trans (y7b_X7_le_X c))
  refine ⟨hM7_le_X.trans inf_le_left, hM7_le_X.trans inf_le_right, ?_⟩
  intro u huW huX v hvW hvX
  obtain ⟨w, hw, hu | hu⟩ := (y7b_mem_W c hb).mp huW
  · exact absurd (by rw [hu]; exact hw) huX
  obtain ⟨w', hw', hv | hv⟩ := (y7b_mem_W c hb).mp hvW
  · exact absurd (by rw [hv]; exact hw') hvX
  have haMem : w⁻¹ * w' ∈ y7bBM c.s :=
    (y7bBM c.s).mul_mem ((y7bBM c.s).inv_mem hw) hw'
  obtain ⟨k, hkM7, hm2⟩ := y7b_theta_onto_M7 c hb (w⁻¹ * w') haMem
  refine ⟨k, hkM7, ?_⟩
  have hkX7 : k ∈ X7 c.s := y7b_C7_le_X7 c hb (y7b_M7_le_C7 c hb hkM7)
  have hm1 : ⁅k, w⁆ ∈ M3 c.s := ((y7b_mem_X7 c hb).mp hkX7).2 w hw
  have hkw : k * w * k⁻¹ = ⁅k, w⁆ * w := by rw [commutatorElement_def]; group
  have hkt : k * c.s.t * k⁻¹ =
      (w⁻¹ * w') * ((w⁻¹ * w')⁻¹ * ⁅k, c.s.t⁆) * c.s.t := by
    rw [commutatorElement_def]; group
  have hmain : v⁻¹ * (k * u * k⁻¹) =
      c.s.t⁻¹ * ((w'⁻¹ * ⁅k, w⁆ * w') * ((w⁻¹ * w')⁻¹ * ⁅k, c.s.t⁆)) * c.s.t := by
    have hsplit : k * (w * c.s.t) * k⁻¹ = (k * w * k⁻¹) * (k * c.s.t * k⁻¹) := by group
    rw [hu, hv, hsplit, hkw, hkt]
    group
  have hw'M3 : w'⁻¹ * ⁅k, w⁆ * w' ∈ M3 c.s := by
    have hw'W : w'⁻¹ ∈ y7bW c.s := (y7bW c.s).inv_mem (y7b_BM_le_W c hb hw')
    simpa using (Subgroup.mem_normalizer_iff.mp (y7b_W_le_NM3 c hb hw'W) ⁅k, w⁆).mp hm1
  have hm3 : (w⁻¹ * w')⁻¹ * ⁅k, c.s.t⁆ ∈ M3 c.s := hm2
  have hprod : (w'⁻¹ * ⁅k, w⁆ * w') * ((w⁻¹ * w')⁻¹ * ⁅k, c.s.t⁆) ∈ M3 c.s :=
    (M3 c.s).mul_mem hw'M3 hm3
  have htW : c.s.t⁻¹ ∈ y7bW c.s := (y7bW c.s).inv_mem (y7b_t_mem_W c hb)
  have hconj : c.s.t⁻¹ * ((w'⁻¹ * ⁅k, w⁆ * w') * ((w⁻¹ * w')⁻¹ * ⁅k, c.s.t⁆)) * c.s.t ∈
      M3 c.s := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp (y7b_W_le_NM3 c hb htW)
        ((w'⁻¹ * ⁅k, w⁆ * w') * ((w⁻¹ * w')⁻¹ * ⁅k, c.s.t⁆))).mp hprod
  rwa [hmain]

end CFSG.OddStandard.HigherRank.YamadaG23
