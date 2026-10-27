module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53T1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Iso
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54One
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54K3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y54_B_le_R (s : Setting3 G L) : s.fr.B ≤ s.R :=
  (s3_B_le_S s).trans s.S_le_R

theorem y54_R_le_NB {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.R ≤ normIn s.H s.fr.B :=
  s.R_le_T.trans (f3_T_le_N hH)

theorem y54_R_le_N {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.R ≤ f4N s := by
  have htH : s.t ∈ s.H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htN : s.t ∈ Subgroup.normalizer (s.fr.F : Set G) :=
    Subgroup.centralizer_le_normalizer (s.fr.F : Set G) <| by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact y54_t_comm_F s f hf
  rw [y5_R_eq hH]
  exact sup_le ((y54_S_le_N hH).trans (y54_NL_le_N hH))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨htH, htN⟩))

theorem y54_N_norm_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ n ∈ f4N c.s, ∀ m ∈ M3 c.s, n * m * n⁻¹ ∈ M3 c.s := by
  intro n hn m hm
  obtain ⟨n₁, hn₁, x, hx, rfl⟩ := y54_N_eq hH n hn
  obtain ⟨-, hMY, hMN, -, -⟩ := y54_M3_cand c hH
  have hxM : x * m * x⁻¹ ∈ M3 c.s :=
    y54_M_normal (c := c) hH (y54_M3_cand c hH) x (y54_X0_le_Y hH hx) m hm
  have h := hMN n₁ hn₁ (x * m * x⁻¹) hxM
  have h' : n₁ * x * m * (n₁ * x)⁻¹ = n₁ * (x * m * x⁻¹) * n₁⁻¹ := by group
  rw [h']
  exact h

theorem y54_R_norm_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ r ∈ c.s.R, ∀ m ∈ M3 c.s, r * m * r⁻¹ ∈ M3 c.s :=
  fun r hr m hm => y54_N_norm_M3 c hH r (y54_R_le_N hH hr) m hm

theorem y54_R_norm_M2 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ r ∈ c.s.R, ∀ m ∈ M2 c.s, r * m * r⁻¹ ∈ M2 c.s :=
  fun r hr m hm => y54_M2_inv hH r (y54_R_le_NB hH hr) m hm

theorem y54_R_inf_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    c.s.R ⊓ M3 c.s = c.s.fr.F := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxR, hxM3⟩ := Subgroup.mem_inf.mp hx
    have hxH : x ∈ c.s.H := (c.s.R_le_T.trans c.s.sylow_T.1) hxR
    rw [← y54_H_inf_M3 c hH]
    exact ⟨hxH, hxM3⟩
  · intro x hx
    exact Subgroup.mem_inf.mpr
      ⟨y54_B_le_R c.s (y54_F_le_B hH hx), (y54_M3_cand c hH).1 hx⟩

theorem y54_R_inf_M2 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    c.s.R ⊓ M2 c.s = c.s.fr.B := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxR, hxM2⟩ := Subgroup.mem_inf.mp hx
    have hxH : x ∈ c.s.H := (c.s.R_le_T.trans c.s.sylow_T.1) hxR
    have hxC2 : x ∈ c.s.C₂ := y54_M2_le_C2 c hH hxM2
    have hxHC : x ∈ c.s.H ⊓ c.s.C₂ := ⟨hxH, hxC2⟩
    rw [f3_H_inf_C₂ hH] at hxHC
    rcases f3_mem_P (s := c.s) x hxHC with hxB | ⟨b, hb, hxbt⟩
    · exact hxB
    · exfalso
      have hbM2 : b ∈ M2 c.s := y54_B_le_M2 c.s hb
      have htM2 : c.s.t ∈ M2 c.s := by
        have h := (M2 c.s).mul_mem ((M2 c.s).inv_mem hbM2) hxM2
        rwa [hxbt, inv_mul_cancel_left] at h
      exact y54_t_notin_M2 c hH htM2
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨y54_B_le_R c.s hx, y54_B_le_M2 c.s hx⟩

theorem y54_M3_relIndex (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    c.s.fr.F.relIndex (M3 c.s) = 8 := by
  obtain ⟨hn, hbody⟩ := y54_secProp c hH
  obtain ⟨φ, -⟩ := hbody
  haveI := hn
  calc c.s.fr.F.relIndex (M3 c.s)
      = Nat.card (↥(M3 c.s) ⧸ (c.s.fr.F).subgroupOf (M3 c.s)) := rfl
    _ = Nat.card ↥c.s.fr.F := Nat.card_congr φ.toEquiv
    _ = 2 ^ 3 := (y54_F_isE3 hH).2
    _ = 8 := by norm_num

theorem y54_M2_relIndex (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    c.s.fr.B.relIndex (M2 c.s) = 4 := by
  have hF_B : c.s.fr.F ≤ c.s.fr.B := y54_F_le_B hH
  have hB_M2 : c.s.fr.B ≤ M2 c.s := y54_B_le_M2 c.s
  have hF_K : c.s.fr.F ≤ centIn (M2 c.s) c.s.fr.F := y54_F_le_K hH
  have hK : centIn (M2 c.s) c.s.fr.F ≤ M2 c.s := inf_le_left
  have hFB : c.s.fr.F.relIndex c.s.fr.B = 4 := by
    have h := Subgroup.relIndex_mul_card (H := c.s.fr.F) (K := c.s.fr.B)
    rw [inf_of_le_left hF_B] at h
    rw [y54_card_B hH, (y54_F_isE3 hH).2] at h
    norm_num at h
    omega
  have hrelK : (centIn (M2 c.s) c.s.fr.F).relIndex (M2 c.s)
      = c.s.fr.F.relIndex c.s.fr.B := by
    have h := relIndex_sup_of_normalizes (T := centIn (M2 c.s) c.s.fr.F)
      (C := c.s.fr.B) (y54_K_norm_B c hH)
    rw [← y54_M2_eq_KB c hH, y54_K_inf_B hH] at h
    exact h
  have h1 := Subgroup.relIndex_mul_relIndex (H := c.s.fr.F) (K := c.s.fr.B) (L := M2 c.s)
    hF_B hB_M2
  have h2 := Subgroup.relIndex_mul_relIndex (H := c.s.fr.F)
    (K := centIn (M2 c.s) c.s.fr.F) (L := M2 c.s) hF_K hK
  have hEq : c.s.fr.F.relIndex c.s.fr.B * c.s.fr.B.relIndex (M2 c.s)
      = c.s.fr.F.relIndex c.s.fr.B * 4 := by
    calc c.s.fr.F.relIndex c.s.fr.B * c.s.fr.B.relIndex (M2 c.s)
        = c.s.fr.F.relIndex (M2 c.s) := h1
      _ = c.s.fr.F.relIndex (centIn (M2 c.s) c.s.fr.F)
            * (centIn (M2 c.s) c.s.fr.F).relIndex (M2 c.s) := h2.symm
      _ = 4 * c.s.fr.F.relIndex c.s.fr.B := by rw [y54_K_relIndex c hH, hrelK]
      _ = c.s.fr.F.relIndex c.s.fr.B * 4 := mul_comm _ _
  exact Nat.eq_of_mul_eq_mul_left (by rw [hFB]; norm_num) hEq

theorem y54_M2_le_R3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : M2 c.s ≤ R3 c.s := by
  rw [y54_M2_eq_KB c hH]
  exact sup_le ((y54_K_le_M3 c hH).trans le_sup_right)
    ((y54_B_le_R c.s).trans le_sup_left)

theorem y54_R2_le_R3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : R2 c.s ≤ R3 c.s := by
  change c.s.R ⊔ M2 c.s ≤ c.s.R ⊔ M3 c.s
  refine sup_le le_sup_left ?_
  exact y54_M2_le_R3 c hH

theorem y54_R2_relIndex (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    (R2 c.s).relIndex (R3 c.s) = 2 := by
  have hR2 : c.s.R.relIndex (R2 c.s) = 4 := by
    have h := relIndex_sup_of_normalizes (T := c.s.R) (C := M2 c.s) (y54_R_norm_M2 c hH)
    rw [y54_R_inf_M2 c hH] at h
    exact h.trans (y54_M2_relIndex c hH)
  have hR3 : c.s.R.relIndex (R3 c.s) = 8 := by
    have h := relIndex_sup_of_normalizes (T := c.s.R) (C := M3 c.s) (y54_R_norm_M3 c hH)
    rw [y54_R_inf_M3 c hH, y54_M3_relIndex c hH] at h
    exact h
  have hmul := Subgroup.relIndex_mul_relIndex (H := c.s.R) (K := R2 c.s) (L := R3 c.s)
    le_sup_left (y54_R2_le_R3 c hH)
  have h : 4 * (R2 c.s).relIndex (R3 c.s) = 8 := by
    rw [← hR2, ← hR3]
    exact hmul
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
