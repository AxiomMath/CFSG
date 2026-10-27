module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJKer
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFR
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Hyp

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private theorem y4_Sσ_eq_sup {Γ : Type} [Group Γ] (fr : Frame Γ) :
    fr.Sσ = fr.S ⊔ Subgroup.closure {fr.σ} := by
  have hset : ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀, fr.σ} : Set Γ) =
      ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀} : Set Γ) ∪ {fr.σ} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_empty_iff_false]
    tauto
  change Subgroup.closure ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀, fr.σ} : Set Γ) =
    fr.S ⊔ Subgroup.closure {fr.σ}
  rw [hset, Subgroup.closure_union]
  rfl

theorem y4_T_le_St (hH : F33Hyp s e) (hRT : s.R = s.T) : s.T ≤ s.fr.S ⊔ zpowers s.t := by
  intro x hx
  obtain ⟨y, hyS, h | h⟩ := s3_R_cases s hH.hS hH.h31 x (by rw [hRT]; exact hx)
  · rw [h]
    exact Subgroup.mem_sup_left hyS
  · rw [h]
    exact Subgroup.mul_mem_sup hyS (Subgroup.mem_zpowers s.t)

theorem y4_T_le_Sgt (hH : F33Hyp s e) (hRT : s.R ≠ s.T) {g : G} (hgT : g ∈ s.T)
    (hgσ : ActsAs L g s.fr'.σ) : s.T ≤ s.fr.S ⊔ zpowers g ⊔ zpowers s.t := by
  intro x hx
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hH.hS
  have hxN : x ∈ normalizer (L : Set G) := s3_T_le_N s hH.hS hx
  have hgN : g ∈ normalizer (L : Set G) := s3_T_le_N s hH.hS hgT
  have hgN' : zpowers g ≤ normalizer (L : Set G) := Subgroup.zpowers_le.mpr hgN
  let α : MulAut (L ⧸ center L) := jHom L ⟨x, hxN⟩
  have hαacts : ActsAs L x α := jHom_actsAs L ⟨x, hxN⟩
  have hαT : α ∈ jSub L s.T := (mem_jSub L).mpr ⟨x, hx, hαacts⟩
  rw [s3_jSub_T s hH.hS hH.hOut hRT] at hαT
  have hzp : jSub L (zpowers g) = Subgroup.closure {s.fr'.σ} := by
    rw [Subgroup.zpowers_eq_closure]
    have h := jSub_closure_of_actsAs ({g} : Set G)
      (fun y hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hgN)
      (fun _ => s.fr'.σ)
      (fun y hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hgσ)
    simpa using h
  have hSσ : s.fr'.Sσ = jSub L (s.fr.S ⊔ zpowers g) := by
    rw [jSub_sup (s3_S_le_N s) hgN', s3_jSub_S s, hzp, y4_Sσ_eq_sup]
  rw [hSσ] at hαT
  obtain ⟨y, hy, hyα⟩ := (mem_jSub L).mp hαT
  have hyT : y ∈ s.T := (sup_le (s3_S_le_T s) (Subgroup.zpowers_le.mpr hgT)) hy
  have hc : y⁻¹ * x ∈ s.T ⊓ centralizer (L : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨s.T.mul_mem (s.T.inv_mem hyT) hx, ?_⟩
    apply (actsAs_one_iff L).mp
    have h1 : ActsAs L (y⁻¹ * x) (α⁻¹ * α) := actsAs_mul L (actsAs_inv L hyα) hαacts
    simpa using h1
  rw [s3_T_inf_centralizer s hH.h31] at hc
  rw [show x = y * (y⁻¹ * x) by group]
  exact Subgroup.mul_mem_sup hy hc

end CFSG.OddStandard.HigherRank.YamadaG23
