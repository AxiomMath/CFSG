module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFusion33
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Aut1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52Dec
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52Excl
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52Sec

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y56_d_mem_C2 {c : Ctx5 G L} (hH : F33Hyp c.s c.e) : c.d ∈ c.s.C₂ := by
  rcases y52_dec hH with h | ⟨hRT, h⟩
  · exact h
  · exact absurd h (y52_excl hH hRT)

theorem y56_B_le_C2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.B ≤ s.C₂ :=
  (le_sup_left : s.fr.B ≤ f3P s).trans (f3_P_le_C₂ hH)

theorem y56_t_mem_C2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.t ∈ s.C₂ :=
  f3_P_le_C₂ hH (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))

theorem y56_Q_le_C2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    e4Q s ≤ s.C₂ :=
  sup_le ((y56_E_le_B hH).trans (y56_B_le_C2 hH))
    (Subgroup.zpowers_le.mpr (y56_t_mem_C2 hH))

theorem y56_conjClass_C2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    conjClass s.C₂ s.t = s.tCoset (cen s.fr.B) :=
  (fact33_of hH).2.2.2.1

theorem y56_C2_cent_V {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.C₂, ∀ v ∈ cen s.fr.B, x * v * x⁻¹ = v := by
  intro x hx v hv
  have h : x * v = v * x :=
    (Subgroup.mem_centralizer_iff.mp (f3_C₂_le_Y hH hx).2 v hv).symm
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem y56_NB_norm_C2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ n ∈ normIn s.H s.fr.B, ∀ x ∈ s.C₂, n * x * n⁻¹ ∈ s.C₂ :=
  fun n hn x hx => f3_C₂_normal hH n (f3_N_le_X s hn) x hx

theorem y56_C2_comm (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ x ∈ c.s.C₂, ∀ y ∈ c.s.C₂, ⁅x, y⁆ ∈ cen c.s.fr.B :=
  y52_comm_mem hH (y56_d_mem_C2 hH)

theorem y56_C2_sq (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ x ∈ c.s.C₂, x ^ 2 ∈ cen c.s.fr.B :=
  y52_sq_mem hH (y56_d_mem_C2 hH)

theorem y56_C2_inf_X0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.C₂ ⊓ e4X0 s = e4Q s := by
  have htt : s.t * s.t = 1 := by
    rw [← pow_two, ← s.t_order]; exact pow_orderOf_eq_one s.t
  apply le_antisymm
  · intro x hx
    obtain ⟨hxC, hxX0⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxH, hxcent⟩ := Subgroup.mem_inf.mp hxX0
    have hxP : x ∈ f3P s := by
      rw [← f3_H_inf_C₂ hH]
      exact ⟨hxH, hxC⟩
    rcases f3_mem_P x hxP with hxB | ⟨b, hb, hxeq⟩
    · have hbE : x ∈ s.fr.E := by
        rw [← y56_centIn_L_E hH]
        exact Subgroup.mem_inf.mpr ⟨f3_B_le_L s hxB, hxcent⟩
      exact Subgroup.mem_sup_left hbE
    · have hxb : b = x * s.t := by rw [hxeq, mul_assoc, htt, mul_one]
      have hbcent : b ∈ Subgroup.centralizer (s.fr.E : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        have hxf : f * x = x * f := Subgroup.mem_centralizer_iff.mp hxcent f hf
        have htx : s.t * f = f * s.t := (y56_t_comm_E s f hf).symm
        calc f * b = f * (x * s.t) := by rw [hxb]
          _ = (f * x) * s.t := by group
          _ = (x * f) * s.t := by rw [hxf]
          _ = x * (f * s.t) := by group
          _ = x * (s.t * f) := by rw [htx]
          _ = (x * s.t) * f := by group
          _ = b * f := by rw [hxb]
      have hbE : b ∈ s.fr.E := by
        rw [← y56_centIn_L_E hH]
        exact Subgroup.mem_inf.mpr ⟨f3_B_le_L s hb, hbcent⟩
      rw [hxeq]
      exact (e4Q s).mul_mem (Subgroup.mem_sup_left hbE)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  · have hE_C2 : s.fr.E ≤ s.C₂ := (y56_E_le_B hH).trans (y56_B_le_C2 hH)
    have hE_H : s.fr.E ≤ s.H := (y56_E_le_L s).trans (s3_L_le_H s hH.hS)
    haveI : IsMulCommutative ↥s.fr.E :=
      IsMulCommutative.of_comm fun a b => Subtype.ext (y56_E_comm hH a a.2 b b.2)
    have hE_cent : s.fr.E ≤ Subgroup.centralizer (s.fr.E : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
    have ht_H : s.t ∈ s.H := by
      show s.t ∈ Subgroup.centralizer ({s.t} : Set G)
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have ht_cent : s.t ∈ Subgroup.centralizer (s.fr.E : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun f hf => y56_t_comm_E s f hf)
    exact sup_le (le_inf hE_C2 (le_inf hE_H hE_cent))
      (le_inf (Subgroup.zpowers_le.mpr (y56_t_mem_C2 hH))
        (Subgroup.zpowers_le.mpr ⟨ht_H, ht_cent⟩))

end CFSG.OddStandard.HigherRank.YamadaG23
