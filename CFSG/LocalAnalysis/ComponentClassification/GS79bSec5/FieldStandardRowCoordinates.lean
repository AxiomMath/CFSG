module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals

public section

open Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.LocalAnalysis.EvenBN.LinearThree

namespace CFSG.ComponentClassification.GS79bSec5

universe u

@[expose] noncomputable def rowSLHom (F : Type) [Field F] :
    Multiplicative (Fin 2 → F) →* Matrix.SpecialLinearGroup (Fin 3) F where
  toFun v := unipU F (-(Multiplicative.toAdd v) 1) 0 (Multiplicative.toAdd v 0)
  map_one' := by simp [unipU_zero]
  map_mul' v w := by
    simp only [toAdd_mul, Pi.add_apply]
    rw [unipU_mul]
    simp
    ring_nf

theorem rowSLHom_range (F : Type) [Field F] :
    (rowSLHom F).range = unipOne F := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨-(Multiplicative.toAdd v) 1, Multiplicative.toAdd v 0, rfl⟩
  · rintro ⟨a, c, rfl⟩
    refine ⟨Multiplicative.ofAdd ![c, -a], ?_⟩
    simp [rowSLHom]

theorem proj_comp_rowSLHom (F : Type) [Field F] :
    (proj 3 F).comp (rowSLHom F) = radCoord F 0 := by
  ext v
  exact radCoord_zero_apply v

theorem leviOne_conj_rowSLHom {F : Type} [Field F]
    (B : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Multiplicative (Fin 2 → F)) :
    leviOne F B * rowSLHom F v * (leviOne F B)⁻¹ =
      rowSLHom F (Multiplicative.ofAdd
        ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v)) := by
  let a : F := -(Multiplicative.toAdd v) 1
  let c : F := Multiplicative.toAdd v 0
  have h := leviOne_mul_unipU B a c
  change leviOne F B * unipU F a 0 c * (leviOne F B)⁻¹ =
    unipU F (-(Multiplicative.toAdd (Multiplicative.ofAdd
      ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v))) 1) 0
      (Multiplicative.toAdd (Multiplicative.ofAdd
        ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd v)) 0)
  rw [toAdd_ofAdd]
  rw [mul_inv_eq_iff_eq_mul.2 h]
  congr 1 <;> simp [a, c, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem torSLZero_conj_rowSLHom {F : Type} [Field F]
    (l : Fˣ) (v : Multiplicative (Fin 2 → F)) :
    torSLZero F l * rowSLHom F v * (torSLZero F l)⁻¹ =
      rowSLHom F (Multiplicative.ofAdd
        (((l : F) ^ 3) • Multiplicative.toAdd v)) := by
  let a : F := -(Multiplicative.toAdd v) 1
  let c : F := Multiplicative.toAdd v 0
  have h := torSL_zero_mul_unipU l a c
  change torSLZero F l * unipU F a 0 c = unipU F ((l : F) ^ 3 * a) 0
    ((l : F) ^ 3 * c) * torSLZero F l at h
  change torSLZero F l * unipU F a 0 c * (torSLZero F l)⁻¹ =
    unipU F (-(Multiplicative.toAdd (Multiplicative.ofAdd
      (((l : F) ^ 3) • Multiplicative.toAdd v))) 1) 0
      (Multiplicative.toAdd (Multiplicative.ofAdd
        (((l : F) ^ 3) • Multiplicative.toAdd v)) 0)
  rw [toAdd_ofAdd]
  rw [mul_inv_eq_iff_eq_mul.2 h]
  congr 1; simp [a, Pi.smul_apply]

@[expose] noncomputable def literalRowEquiv
    {G : Type u} [Group G] {F : Type} [Field F]
    (A : Subgroup G)
    (e : (A ⧸ Subgroup.center A) ≃* projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        proj 3 F) :
    Multiplicative (Fin 2 → F) ≃*
      ((unipOne F).map (A.subtype.comp φ)) := by
  let π : A →* projectiveSL 3 F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))
  let ιA : Multiplicative (Fin 2 → F) →* A := φ.comp (rowSLHom F)
  let ιG : Multiplicative (Fin 2 → F) →* G := A.subtype.comp ιA
  have hπιA : π.comp ιA = radCoord F 0 := by
    ext v
    have h := DFunLike.congr_fun hφproj (rowSLHom F v)
    change ((e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ)
      (rowSLHom F v) = radCoord F 0 v
    rw [h]
    exact DFunLike.congr_fun (proj_comp_rowSLHom F) v
  have hιA_inj : Function.Injective ιA := by
    intro v w h
    apply radCoord_injective 0
    have hπ := congrArg (fun z : A => π z) h
    rwa [show π (ιA v) = radCoord F 0 v from DFunLike.congr_fun hπιA v,
      show π (ιA w) = radCoord F 0 w from DFunLike.congr_fun hπιA w] at hπ
  have hιG_inj : Function.Injective ιG := A.subtype_injective.comp hιA_inj
  have hιA_range : ιA.range = (unipOne F).map φ := by
    dsimp only [ιA]
    rw [MonoidHom.range_comp, rowSLHom_range]
  have hιG_range : ιG.range = (unipOne F).map (A.subtype.comp φ) := by
    dsimp only [ιG]
    rw [MonoidHom.range_comp, hιA_range, Subgroup.map_map]
  exact (MonoidHom.ofInjective hιG_inj).trans (MulEquiv.subgroupCongr hιG_range)

theorem literalRowEquiv_apply
    {G : Type u} [Group G] {F : Type} [Field F]
    (A : Subgroup G)
    (e : (A ⧸ Subgroup.center A) ≃* projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        proj 3 F)
    (v : Multiplicative (Fin 2 → F)) :
    (literalRowEquiv A e φ hφproj v : G) =
      A.subtype (φ (unipU F (-(Multiplicative.toAdd v) 1) 0
        (Multiplicative.toAdd v 0))) := by
  simp only [literalRowEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply, MonoidHom.comp_apply]
  rfl

end CFSG.ComponentClassification.GS79bSec5

end
