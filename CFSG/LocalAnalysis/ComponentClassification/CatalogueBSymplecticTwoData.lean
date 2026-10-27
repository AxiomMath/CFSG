module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagExtension

public section

namespace CFSG.ComponentClassification.CatalogueBSymplecticTwo

open Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher

section Image

variable {G : Type*} [Group G]

theorem map_toMonoidHom_one (M : Subgroup G) : M.map (1 : MulAut G).toMonoidHom = M :=
  Subgroup.map_id M

theorem map_toMonoidHom_mul (α β : MulAut G) (M : Subgroup G) :
    M.map (α * β).toMonoidHom = (M.map β.toMonoidHom).map α.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem image_map_toMonoidHom_mul (α β : MulAut G) (X : Set (Subgroup G)) :
    (fun M => M.map (α * β).toMonoidHom) '' X =
      (fun M => M.map α.toMonoidHom) '' ((fun M => M.map β.toMonoidHom) '' X) := by
  rw [Set.image_image]
  exact Set.image_congr fun M _ => map_toMonoidHom_mul α β M

theorem image_map_toMonoidHom_inv_of_image_eq {α : MulAut G} {X : Set (Subgroup G)}
    (h : (fun M => M.map α.toMonoidHom) '' X = X) :
    (fun M => M.map α⁻¹.toMonoidHom) '' X = X := by
  conv_lhs => rw [← h]
  rw [← image_map_toMonoidHom_mul, inv_mul_cancel]
  simp only [map_toMonoidHom_one, Set.image_id']

end Image

variable (K : Type) [Field K]

@[expose] def pointParabolics : Set (Subgroup (StatedProj (StatedSp 2 K))) :=
  {M | ∃ L : Submodule K (Fin 2 ⊕ Fin 2 → K), finrank K L = 1 ∧ M = projStabilizer 2 K L}

@[expose] def planeParabolics : Set (Subgroup (StatedProj (StatedSp 2 K))) :=
  {M | ∃ W : Submodule K (Fin 2 ⊕ Fin 2 → K), IsTotallyIsotropic (pairedSympForm K 2) W ∧
    finrank K W = 2 ∧ M = projStabilizer 2 K W}

abbrev incidenceGraph (p : ℕ) : SimpleGraph (spExtremalParabolics 2 K p) :=
  LinearFlag.parabolicGraph (StatedProj (StatedSp 2 K)) p

@[expose] def typeKernel : Subgroup (MulAut (StatedProj (StatedSp 2 K))) where
  carrier := {α | (fun M => M.map α.toMonoidHom) '' pointParabolics K = pointParabolics K}
  one_mem' := by
    change (fun M => M.map (1 : MulAut (StatedProj (StatedSp 2 K))).toMonoidHom) ''
      pointParabolics K = pointParabolics K
    simp only [map_toMonoidHom_one, Set.image_id']
  mul_mem' {α β} hα hβ := by
    change (fun M => M.map (α * β).toMonoidHom) '' pointParabolics K = pointParabolics K
    rw [image_map_toMonoidHom_mul, hβ, hα]
  inv_mem' {α} hα := image_map_toMonoidHom_inv_of_image_eq hα

variable {K}

theorem mem_typeKernel {α : MulAut (StatedProj (StatedSp 2 K))} :
    α ∈ typeKernel K ↔
      (fun M => M.map α.toMonoidHom) '' pointParabolics K = pointParabolics K :=
  Iff.rfl

theorem mem_typeKernel_of_forall {α : MulAut (StatedProj (StatedSp 2 K))}
    (h₁ : ∀ M ∈ pointParabolics K, M.map α.toMonoidHom ∈ pointParabolics K)
    (h₂ : ∀ M ∈ pointParabolics K, M.map α⁻¹.toMonoidHom ∈ pointParabolics K) :
    α ∈ typeKernel K := by
  refine Set.Subset.antisymm ?_ fun M hM => ⟨M.map α⁻¹.toMonoidHom, h₂ M hM, ?_⟩
  · rintro _ ⟨M, hM, rfl⟩
    exact h₁ M hM
  · change (M.map α⁻¹.toMonoidHom).map α.toMonoidHom = M
    rw [← map_toMonoidHom_mul, mul_inv_cancel, map_toMonoidHom_one]

end CFSG.ComponentClassification.CatalogueBSymplecticTwo
