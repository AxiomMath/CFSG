module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM22
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

@[expose] def slMap (σ : F ≃+* F) : MulAut SL(2, F) where
  toFun := Matrix.SpecialLinearGroup.map (σ : F →+* F)
  invFun := Matrix.SpecialLinearGroup.map (σ.symm : F →+* F)
  left_inv b := Subtype.ext (by ext i j; simp)
  right_inv b := Subtype.ext (by ext i j; simp)
  map_mul' := map_mul _

theorem fieldSp_longBlock (σ : F ≃+* F) (k : Fin 2) (b : SL(2, F)) :
    fieldSp 2 F σ (longBlock F 2 k b) = longBlock F 2 k (slMap σ b) := by
  apply mat_injective
  rw [mat_apply, coe_fieldSp, ← mat_apply, mat_longBlock_eq_bd, mat_longBlock_eq_bd, bd_map]
  congr 1
  funext k'
  split_ifs
  · rfl
  · exact Matrix.map_one _ (map_zero σ) (map_one σ)

theorem fieldSp_longInv (σ : F ≃+* F) (k : Fin 2) :
    fieldSp 2 F σ (longInv F 2 k) = longInv F 2 k := by
  apply mat_injective
  rw [mat_apply, coe_fieldSp, ← mat_apply, mat_longInv_map]

theorem fieldSp_negOne (σ : F ≃+* F) : fieldSp 2 F σ (negOne F) = negOne F := by
  rw [negOne, map_mul, fieldSp_longInv, fieldSp_longInv]

theorem map_fieldSp_L (σ : F ≃+* F) (k : Fin 2) :
    (longRootSp2 F 2 k).map (fieldSp 2 F σ).toMonoidHom = longRootSp2 F 2 k := by
  ext x
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨slMap σ b, (fieldSp_longBlock σ k b).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨longBlock F 2 k ((slMap σ).symm b), ⟨_, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, fieldSp_longBlock, MulEquiv.apply_symm_apply]

variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}

namespace Frame

@[expose] def planeImages (ψ : StatedSp 2 F →* Y) : Set (Subgroup Y) :=
  {J | ∃ P, IsHyperbolicPlane P ∧ J = (planeGroup P).map ψ}

@[expose] noncomputable def twist (fr : Frame F Y Φ A A' z') (ρ : F ≃+* F) :
    Frame F Y (planeImages (fr.ψ.comp (fieldSp 2 F ρ).toMonoidHom)) A A' z' where
  ψ := fr.ψ.comp (fieldSp 2 F ρ).toMonoidHom
  surj y := by
    obtain ⟨x, rfl⟩ := fr.surj y
    exact ⟨(fieldSp 2 F ρ).symm x, by simp⟩
  ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, fr.ker, mem_spScalars_iff,
      mem_spScalars_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro (h | h)
      · left
        exact (fieldSp 2 F ρ).injective (by rw [h, map_one])
      · right
        exact (fieldSp 2 F ρ).injective (by rw [h, fieldSp_negOne])
    · rintro (rfl | rfl)
      · left
        exact map_one _
      · right
        exact fieldSp_negOne ρ
  hA := by
    rw [← Subgroup.map_map, map_fieldSp_L]
    exact fr.hA
  hA' := by
    rw [← Subgroup.map_map, map_fieldSp_L]
    exact fr.hA'
  hz := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, fieldSp_longInv]
    exact fr.hz
  mem _ hJ := hJ
  mem' P hP := ⟨P, hP, rfl⟩

theorem twist_ψ (fr : Frame F Y Φ A A' z') (ρ : F ≃+* F) (x : StatedSp 2 F) :
    (fr.twist ρ).ψ x = fr.ψ (fieldSp 2 F ρ x) := rfl

theorem twist_ψ_longBlock (fr : Frame F Y Φ A A' z') (ρ : F ≃+* F) (k : Fin 2) (b : SL(2, F)) :
    fr.ψ (longBlock F 2 k b) = (fr.twist ρ).ψ (longBlock F 2 k ((slMap ρ).symm b)) := by
  rw [twist_ψ, fieldSp_longBlock, MulEquiv.apply_symm_apply]

end Frame

end CFSG.ClassicalInvolution.Asc77.C5O.M
