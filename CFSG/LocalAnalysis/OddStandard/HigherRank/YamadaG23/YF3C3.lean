module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3C2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3AbsT

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem f3_P_le_T (s : Setting3 G L) : f3P s ≤ s.T := by
  refine sup_le ?_ ?_
  · have hBS : s.fr.B ≤ s.fr.S := by
      rw [SFrame.B, centIn]
      exact inf_le_left
    exact hBS.trans (s3_S_le_T s)
  · rw [Subgroup.zpowers_le]
    exact s3_t_mem_T s

theorem f3_T_le_X {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) : s.T ≤ s.X :=
  (f3_T_le_N hH).trans (f3_N_le_X s)

theorem f3_T_norm_C₂ {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.T, ∀ c ∈ s.C₂, x * c * x⁻¹ ∈ s.C₂ :=
  fun x hx c hc => f3_C₂_normal hH x (f3_T_le_X hH hx) c hc

theorem f3_T_inf_C₂ {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.T ⊓ s.C₂ = f3P s := by
  refine le_antisymm ?_ (le_inf (f3_P_le_T s) (f3_P_le_C₂ hH))
  intro x hx
  obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxH : x ∈ s.H := s.sylow_T.1 hxT
  have hx' : x ∈ s.H ⊓ s.C₂ := ⟨hxH, hxC⟩
  rwa [f3_H_inf_C₂ hH] at hx'

theorem f3_mem_T₂ {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.T₂, ∃ τ ∈ s.T, ∃ c ∈ s.C₂, x = τ * c :=
  mem_sup_of_normalizes (f3_T_norm_C₂ hH)

theorem f3_T1_fix_z {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ e.T₁, x * s.fr.z * x⁻¹ = s.fr.z :=
  fun x hx => s3_conj_z s (lfactsA_of_setting hH.hS hH.hZ s) e hH.h32 hx

theorem f3_T2_fix_z {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.T₂, x * s.fr.z * x⁻¹ = s.fr.z := by
  intro x hx
  obtain ⟨τ, hτ, c, hc, rfl⟩ := f3_mem_T₂ hH x hx
  obtain ⟨w, -, hzV, -⟩ := f3_V_elems hH
  have hcz : c * s.fr.z * c⁻¹ = s.fr.z := by
    have hcent : c ∈ centralizer (cen s.fr.B : Set G) :=
      (Subgroup.mem_inf.mp (f3_C₂_le_Y hH hc)).2
    have hcomm : c * s.fr.z = s.fr.z * c :=
      (Subgroup.mem_centralizer_iff.mp hcent s.fr.z hzV).symm
    rw [hcomm]
    group
  calc τ * c * s.fr.z * (τ * c)⁻¹
      = τ * (c * s.fr.z * c⁻¹) * τ⁻¹ := by group
    _ = τ * s.fr.z * τ⁻¹ := by rw [hcz]
    _ = s.fr.z := f3_T1_fix_z hH τ (e.T_le hτ)

theorem f3_T_sylow_N {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    IsSylowIn 2 (f3N s) s.T := by
  refine ⟨f3_T_le_N hH, s.sylow_T.2.1, ?_⟩
  intro hdvd
  have hmul := Subgroup.relIndex_mul_relIndex (H := s.T) (K := f3N s) (L := s.H)
    (f3_T_le_N hH) (show f3N s ≤ s.H from inf_le_left)
  have hdvd' : 2 ∣ s.T.relIndex (f3N s) * (f3N s).relIndex s.H :=
    dvd_mul_of_dvd_left hdvd _
  rw [hmul] at hdvd'
  exact s.sylow_T.2.2 hdvd'

theorem f3_T_relIndex_T₂ {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.T.relIndex s.T₂ = 4 := by
  change s.T.relIndex (s.T ⊔ s.C₂) = 4
  rw [relIndex_sup_of_normalizes (f3_T_norm_C₂ hH), f3_T_inf_C₂ hH, f3_P_relIndex_C₂ hH]

theorem f3_c9 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    IsSylowIn 2 s.X s.T₂ := by
  have hCN : s.C₂ ⊓ f3N s ≤ s.T := by
    intro x hx
    obtain ⟨hxC, hxN⟩ := Subgroup.mem_inf.mp hx
    have hxN' : x ∈ s.H ⊓ normalizer (s.fr.B : Set G) := hxN
    have hxH : x ∈ s.H := hxN'.1
    have hx' : x ∈ s.H ⊓ s.C₂ := ⟨hxH, hxC⟩
    rw [f3_H_inf_C₂ hH] at hx'
    exact f3_P_le_T s hx'
  change IsSylowIn 2 s.X (s.T ⊔ s.C₂)
  exact sylow_sup_of_normal (X := s.X) (C := s.C₂) (N := f3N s) (T := s.T)
    (f3_C₂_le_X hH) (f3_N_le_X s) (f3_C₂_normal hH) (f3_C₂_isPGroup hH)
    (f3_X_eq_C₂N hH) (f3_T_sylow_N hH) hCN

theorem f3_c8 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) : e.T₁ ≤ s.T₂ := by
  change e.T₁ ≤ s.T ⊔ s.C₂
  exact le_sup_of_sylow (X := s.X) (C := s.C₂) (T := s.T) (T₁ := e.T₁)
    (f3_C₂_le_X hH) (f3_C₂_normal hH) (f3_C₂_isPGroup hH)
    (show IsSylowIn 2 s.X (s.T ⊔ s.C₂) from f3_c9 hH) (f3_T1_le_X hH)
    e.sylow.2.1 e.T_le

end CFSG.OddStandard.HigherRank.YamadaG23
