module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBFrameData
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardCoverLevi

public section

namespace CFSG.ComponentClassification.GS79bSec5

open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial FieldFourCover LinearFlag
open CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.OddStandard.Seitz77
open CFSG.LieType.Chevalley (SL2 uSL HSL WSL)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type*} [Group G]

structure CoverFrame (A V : Subgroup G) (K : Type) [Field K] where
  ρ : SpecialLinearGroup (Fin 3) K →* G
  range_eq : ρ.range = A
  ker_le : ρ.ker ≤ center (SpecialLinearGroup (Fin 3) K)
  map_unipAll : (unipAll K).map ρ = V

namespace CoverFrame

variable {A V : Subgroup G} {K : Type} [Field K]

theorem injective_comp_subtype (F : CoverFrame A V K) :
    Function.Injective (F.ρ.comp (unipAll K).subtype) := by
  refine (injective_iff_map_eq_one (F.ρ.comp (unipAll K).subtype)).mpr ?_
  intro u hu
  have hscal : (u : SpecialLinearGroup (Fin 3) K) ∈ scalars 3 K := by
    rw [scalars_eq_center]
    exact F.ker_le hu
  have hbot : (u : SpecialLinearGroup (Fin 3) K) ∈
      (⊥ : Subgroup (SpecialLinearGroup (Fin 3) K)) := by
    have hmem : (u : SpecialLinearGroup (Fin 3) K) ∈ unitriangular 3 K ⊓ scalars 3 K := by
      rw [← unipAll_eq_unitriangular]
      exact ⟨u.property, hscal⟩
    rwa [unitriangular_inf_scalars] at hmem
  exact Subtype.ext (Subgroup.mem_bot.mp hbot)

variable [Finite K] [CharP K 2]

@[expose] noncomputable def toFrameData (F : CoverFrame A V K) : FrameData A V K where
  ψ := F.ρ.comp (unipAll K).subtype
  rad i := (![unipOne K, unipTwo K] i).map F.ρ
  leviData i := LeviData.ofCover F.ρ F.range_eq F.ker_le i
  ψ_injective := F.injective_comp_subtype
  map_top_ψ := by
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype, F.map_unipAll]
  ι_zero_apply _ := rfl
  ι_one_apply _ := rfl
  lev_zero_uSL := by
    intro s
    rw [LeviData.ofCover_lev, MonoidHom.comp_apply, levi_zero, Frame.leviOne_uSL]
    rfl
  lev_one_uSL := by
    intro s
    rw [LeviData.ofCover_lev, MonoidHom.comp_apply, levi_one, Frame.leviTwo_uSL]
    rfl
  braid := by
    simp only [LeviData.ofCover_lev, MonoidHom.comp_apply, ← map_mul, levi_zero, levi_one,
      Frame.leviOne_leviTwo_braid]
  sup_lev_range := by
    have h0 : (LeviData.ofCover F.ρ F.range_eq F.ker_le 0).lev.range =
        (leviOne K).range.map F.ρ := by
      rw [LeviData.ofCover_lev, MonoidHom.range_comp, levi_zero]
    have h1 : (LeviData.ofCover F.ρ F.range_eq F.ker_le 1).lev.range =
        (leviTwo K).range.map F.ρ := by
      rw [LeviData.ofCover_lev, MonoidHom.range_comp, levi_one]
    rw [h0, h1, ← Subgroup.map_sup, Frame.range_leviOne, Frame.range_leviTwo, sup_comm,
      CFSG.ClassicalInvolution.WeakCT.B12_sup_B23, ← MonoidHom.range_eq_map, F.range_eq]
  isQuasisimple := isQuasisimple_of_range_eq_of_ker_le_center F.ρ F.range_eq F.ker_le

end CoverFrame

end CFSG.ComponentClassification.GS79bSec5

end
