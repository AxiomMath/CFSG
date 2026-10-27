module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4A

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y6b_mem_F_t_of_actsAs_inner (c : Ctx5 G L) (hH : F33Hyp c.s c.e) {x : G}
    (hx : x ∈ centIn c.s.H c.s.fr.F) {α : MulAut (L ⧸ center L)} (hαx : ActsAs L x α)
    (hα : α ∈ innerAut (L ⧸ center L)) : x ∈ c.s.fr.F ⊔ zpowers c.s.t := by
  have hxM : x ∈ L ⊔ centIn c.s.H L := by
    by_contra hxM
    exact s3_outer_of_not_mem_M c.s hH.hS hx.1 hxM hαx hα
  have h := y5_cent_inf_M (s := c.s) (e := c.e) hH (V := c.s.fr.F) (y54_F_le_L c.s) x hx hxM
  rwa [y54_centIn_L_F hH] at h

theorem y6b_cent_H_F_le_E (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    centIn c.s.H c.s.fr.F ≤ y6bE c := by
  intro x hx
  obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxF : ∀ f ∈ c.s.fr.F, x * f = f * x :=
    fun f hf => (Subgroup.mem_centralizer_iff.mp hxC f hf).symm
  have hN : c.s.H ≤ normalizer (L : Set G) := s3_H_le_N c.s hH.hS
  let α := jOn L hN ⟨x, hxH⟩
  have hαx : ActsAs L x α := jOn_actsAs L hN ⟨x, hxH⟩
  by_cases hαinn : α ∈ innerAut (L ⧸ center L)
  · exact (sup_le (y6b_F_le_E c) le_sup_right)
      (y6b_mem_F_t_of_actsAs_inner c hH hx hαx hαinn)
  · have hgH : c.g ∈ c.s.H := c.s.sylow_T.1 (y6b_g_mem_T c hRT)
    have hgC : c.g ∈ centralizer (c.s.fr.F : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun f hf => (y6b_g_comm_F c hH hRT f hf).symm)
    let β := jOn L hN ⟨c.g, hgH⟩
    have hβg : ActsAs L c.g β := jOn_actsAs L hN ⟨c.g, hgH⟩
    have hβOut : β ∉ innerAut (L ⧸ center L) :=
      s3_outer_of_not_mem_M c.s hH.hS hgH (y6b_g_not_mem_M c hH hRT) hβg
    have hβinvOut : β⁻¹ ∉ innerAut (L ⧸ center L) :=
      fun h => hβOut (by simpa using Subgroup.inv_mem _ h)
    have hαβ : α * β⁻¹ ∈ innerAut (L ⧸ center L) :=
      (Subgroup.mul_mem_iff_of_index_two hH.hOut).mpr (iff_of_false hαinn hβinvOut)
    have hyH : x * c.g⁻¹ ∈ c.s.H := c.s.H.mul_mem hxH (c.s.H.inv_mem hgH)
    have hyC : x * c.g⁻¹ ∈ centralizer (c.s.fr.F : Set G) :=
      Subgroup.mul_mem _ hxC ((centralizer (c.s.fr.F : Set G)).inv_mem hgC)
    have hyF : x * c.g⁻¹ ∈ centIn c.s.H c.s.fr.F := Subgroup.mem_inf.mpr ⟨hyH, hyC⟩
    have hyE : x * c.g⁻¹ ∈ y6bE c :=
      (sup_le (y6b_F_le_E c) le_sup_right)
        (y6b_mem_F_t_of_actsAs_inner c hH hyF (actsAs_mul L hαx (actsAs_inv L hβg)) hαβ)
    have hgE : c.g ∈ y6bE c := y6b_E16_le_E c (y6b_g_mem_E16 c)
    have hxeq : x = (x * c.g⁻¹) * c.g := by group
    rw [hxeq]
    exact Subgroup.mul_mem _ hyE hgE

end CFSG.OddStandard.HigherRank.YamadaG23
