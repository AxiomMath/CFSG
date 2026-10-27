module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Dihed
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrBasic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y54_d_cent_F (c : Ctx5 G L) : ∀ f ∈ c.s.fr.F, c.d * f * c.d⁻¹ = f := by
  intro f hf
  exact y5_d_cent_A c f (s3_F_le_A c.s hf)

theorem y54_z_mem_F (s : Setting3 G L) : s.fr.z ∈ s.fr.F := by
  rw [SFrame.F]
  exact Subgroup.subset_closure (by simp)

theorem y54_z_ne_one {c : Ctx5 G L} (hH : F33Hyp c.s c.e) : c.s.fr.z ≠ 1 := by
  intro h
  have hz := s3_z_order c.s (lfactsA_of_setting hH.hS hH.hZ c.s)
  rw [h, orderOf_one] at hz
  norm_num at hz

theorem y54_d_mem_X {c : Ctx5 G L} (hH : F33Hyp c.s c.e) : c.d ∈ f4X c.s := by
  have hP : (c.s.fr.F ⊔ zpowers c.s.t : Subgroup G) =
      Subgroup.closure ((c.s.fr.F : Set G) ∪ {c.s.t}) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure]
  change c.d ∈ Subgroup.normalizer ((c.s.fr.F ⊔ zpowers c.s.t : Subgroup G) : Set G)
  rw [hP, Subgroup.mem_set_normalizer_iff]
  have hfwd : ∀ p ∈ (Subgroup.closure ((c.s.fr.F : Set G) ∪ {c.s.t}) : Set G),
      c.d * p * c.d⁻¹ ∈ Subgroup.closure ((c.s.fr.F : Set G) ∪ {c.s.t}) := by
    intro p hp
    induction hp using Subgroup.closure_induction with
    | mem x hx =>
        rcases hx with hxF | hxt
        · rw [y54_d_cent_F c x hxF]
          exact Subgroup.subset_closure (Or.inl hxF)
        · rw [Set.mem_singleton_iff] at hxt
          rw [hxt, y5_dtd (c := c) hH]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl (y54_z_mem_F c.s)))
            (Subgroup.subset_closure (Or.inr rfl))
    | one => simpa using Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
        rw [show c.d * (x * y) * c.d⁻¹ =
          (c.d * x * c.d⁻¹) * (c.d * y * c.d⁻¹) by group]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih =>
        rw [show c.d * x⁻¹ * c.d⁻¹ = (c.d * x * c.d⁻¹)⁻¹ by group]
        exact Subgroup.inv_mem _ ih
  intro p
  constructor
  · exact hfwd p
  · intro hp
    have h := hfwd (c.d * p * c.d⁻¹) hp
    have hd : c.d * c.d = 1 := by rw [← pow_two]; exact y5_d_sq c
    have hconj : c.d * (c.d * p * c.d⁻¹) * c.d⁻¹ = p := by
      calc c.d * (c.d * p * c.d⁻¹) * c.d⁻¹
          = (c.d * c.d) * p * (c.d * c.d)⁻¹ := by group
        _ = p := by rw [hd]; group
    rwa [hconj] at h

theorem y54_d_mem_Y {c : Ctx5 G L} (hH : F33Hyp c.s c.e) : c.d ∈ f4Y c.s := by
  show c.d ∈ f4X c.s ⊓ Subgroup.centralizer (c.s.fr.F : Set G)
  refine Subgroup.mem_inf.mpr ⟨y54_d_mem_X hH, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have h := y54_d_cent_F c f hf
  calc f * c.d = (c.d * f * c.d⁻¹) * c.d := by rw [h]
    _ = c.d * f := by group

theorem y54_phi_d {c : Ctx5 G L} (hH : F33Hyp c.s c.e) : f3phi c.s c.d = c.s.fr.z := by
  change c.d * c.s.t * c.d⁻¹ * c.s.t⁻¹ = c.s.fr.z
  rw [y5_dtd (c := c) hH]
  group

theorem y54_S_fix_d {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    ∀ x ∈ c.s.fr.S, ⁅x, c.d⁆ ∈ c.s.fr.F := by
  intro x hx
  have hxT1 : x ∈ c.e.T₁ := c.e.T_le (s3_S_le_T c.s hx)
  rcases y5_T1_conj_d (c := c) hH x hxT1 with h | h
  · rw [commutatorElement_def, h]
    simpa using c.s.fr.F.one_mem
  · rw [commutatorElement_def, h]
    simpa using y54_z_mem_F c.s

end CFSG.OddStandard.HigherRank.YamadaG23
