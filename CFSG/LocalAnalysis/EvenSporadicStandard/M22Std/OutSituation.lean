module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutRest4

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.ABGLocalTools
  CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L} {Q : Sylow 2 G} {x : G} {L1 : Subgroup G}

theorem OuterSituation.isConj_z_mul
    (hS : OuterSituation G L z t T₁ F tb Q x L1) {b : G} (hb : b ∈ L) (hb2 : b * b = 1)
    (hb1 : b ≠ 1) : IsConj z (z * b) := by
  obtain ⟨c, hc, hbc⟩ := oneClass_of_isSporadic hS.sporadic hS.data.t_mem_L hb hS.data.cfg.t_sq
    hb2 hS.data.cfg.t_ne hb1
  refine isConj_iff.2 ⟨c * x, ?_⟩
  have hzc : z * c = c * z := hS.one.z_comm c hc
  calc c * x * z * (c * x)⁻¹ = c * (x * z * x⁻¹) * c⁻¹ := by group
    _ = c * (z * t) * c⁻¹ := by rw [hS.x_z]
    _ = (c * z) * t * c⁻¹ := by group
    _ = (z * c) * t * c⁻¹ := by rw [hzc]
    _ = z * (c * t * c⁻¹) := by group
    _ = z * b := by rw [hbc]

end CFSG.EvenSporadicStandard.M22Std
