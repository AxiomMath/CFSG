module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Cosets
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Frame
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5FrameB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Dihed
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3C3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y52_mem_P_of_mem_R {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {x : G} (hxR : x ∈ s.R) (hxc : ∀ v ∈ cen s.fr.B, v * x = x * v) : x ∈ f3P s := by
  have hxR' : x ∈ s.T ⊓ (L ⊔ centIn s.H L) := by rwa [s3_R_eq s hH.hS] at hxR
  rw [f3_centIn_H_L hH] at hxR'
  obtain ⟨ℓ, hℓL, i, hx⟩ := y5_mem_L_sup_t s hxR'.2
  have hle : (cen s.fr.B : Set G) ⊆ (L : Set G) :=
    fun w hw => f3_B_le_L s (Subgroup.mem_inf.mp hw).1
  have htC : s.t ∈ Subgroup.centralizer (cen s.fr.B : Set G) :=
    Subgroup.centralizer_le hle s.t_mem
  have hℓ : ℓ = x * (s.t ^ i)⁻¹ := by rw [hx]; group
  have hℓC : ℓ ∈ Subgroup.centralizer (cen s.fr.B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hcomm : Commute v s.t := Subgroup.mem_centralizer_iff.mp htC v hv
    have htiv : v * (s.t ^ i)⁻¹ = (s.t ^ i)⁻¹ * v := (hcomm.zpow_right i).inv_right.eq
    rw [hℓ]
    calc v * (x * (s.t ^ i)⁻¹) = (v * x) * (s.t ^ i)⁻¹ := by group
      _ = (x * v) * (s.t ^ i)⁻¹ := by rw [hxc v hv]
      _ = x * (v * (s.t ^ i)⁻¹) := by group
      _ = x * ((s.t ^ i)⁻¹ * v) := by rw [htiv]
      _ = (x * (s.t ^ i)⁻¹) * v := by group
  have hℓB : ℓ ∈ s.fr.B := by
    have hmem : ℓ ∈ centIn L (cen s.fr.B) := Subgroup.mem_inf.mpr ⟨hℓL, hℓC⟩
    rwa [f3_centIn_L_V hH] at hmem
  rw [hx]
  exact Subgroup.mul_mem_sup hℓB (Subgroup.zpow_mem_zpowers s.t i)

theorem y52_dec {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    c.d ∈ c.s.C₂ ∨ (c.s.R ≠ c.s.T ∧ c.g * c.d ∈ c.s.C₂) := by
  obtain ⟨τ, hτT, x, hxC, hd⟩ := f3_mem_T₂ hH c.d (f3_c8 hH (y5_d_mem_T1 c))
  have hVd : ∀ v ∈ cen c.s.fr.B, v * c.d = c.d * v := by
    intro v hv
    exact (mul_inv_eq_iff_eq_mul.mp (y5_d_cent_A c v (y5_V_le_A hH hv))).symm
  have hVx : ∀ v ∈ cen c.s.fr.B, v * x = x * v := by
    intro v hv
    have hcent : x ∈ Subgroup.centralizer (cen c.s.fr.B : Set G) :=
      (Subgroup.mem_inf.mp (f3_C₂_le_Y hH hxC)).2
    exact Subgroup.mem_centralizer_iff.mp hcent v hv
  have hτ : τ = c.d * x⁻¹ := by rw [hd]; group
  have hVτ : ∀ v ∈ cen c.s.fr.B, v * τ = τ * v := by
    intro v hv
    have hvx : v * x⁻¹ = x⁻¹ * v := (show Commute v x from hVx v hv).inv_right.eq
    rw [hτ]
    calc v * (c.d * x⁻¹) = (v * c.d) * x⁻¹ := by group
      _ = (c.d * v) * x⁻¹ := by rw [hVd v hv]
      _ = c.d * (v * x⁻¹) := by group
      _ = c.d * (x⁻¹ * v) := by rw [hvx]
      _ = (c.d * x⁻¹) * v := by group
  by_cases hτR : τ ∈ c.s.R
  · left
    rw [hd]
    exact Subgroup.mul_mem _ (f3_P_le_C₂ hH (y52_mem_P_of_mem_R hH hτR hVτ)) hxC
  · right
    have hRT : c.s.R ≠ c.s.T := fun h => hτR (h ▸ hτT)
    obtain ⟨hgT, hgR, hact, hg2, -⟩ := c.g_spec hRT
    have hVg : ∀ v ∈ cen c.s.fr.B, v * c.g = c.g * v := by
      intro v hv
      exact (mul_inv_eq_iff_eq_mul.mp (y5_g_cent_V hH hg2 hact v hv)).symm
    have hgτR : c.g⁻¹ * τ ∈ c.s.R := by
      rcases y5_T_cosets hH c.g hgT τ hτT with h | h | h
      · exact absurd h hgR
      · exact absurd h hτR
      · exact h
    have hVgτ : ∀ v ∈ cen c.s.fr.B, v * (c.g⁻¹ * τ) = (c.g⁻¹ * τ) * v := by
      intro v hv
      have hvg : v * c.g⁻¹ = c.g⁻¹ * v := (show Commute v c.g from hVg v hv).inv_right.eq
      calc v * (c.g⁻¹ * τ) = (v * c.g⁻¹) * τ := by group
        _ = (c.g⁻¹ * v) * τ := by rw [hvg]
        _ = c.g⁻¹ * (v * τ) := by group
        _ = c.g⁻¹ * (τ * v) := by rw [hVτ v hv]
        _ = (c.g⁻¹ * τ) * v := by group
    have hgτC : c.g⁻¹ * τ ∈ c.s.C₂ := f3_P_le_C₂ hH (y52_mem_P_of_mem_R hH hgτR hVgτ)
    have hginv : c.g⁻¹ = c.g := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hg2
    refine ⟨hRT, ?_⟩
    have hgd : c.g⁻¹ * c.d ∈ c.s.C₂ := by
      rw [hd, ← mul_assoc]
      exact Subgroup.mul_mem _ hgτC hxC
    rwa [hginv] at hgd

end CFSG.OddStandard.HigherRank.YamadaG23
