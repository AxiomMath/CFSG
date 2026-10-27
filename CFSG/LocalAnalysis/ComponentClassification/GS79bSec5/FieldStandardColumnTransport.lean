module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowOddComplement
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.GraphAutomorphism

public noncomputable section

open Matrix Subgroup

namespace CFSG.ComponentClassification.GS79bSec5

universe u

open CFSG.LocalAnalysis.ComponentInitial

theorem map_unipOne_typeAGraphAutomorphism (F : Type) [Field F] :
    (FieldFourCover.unipOne F).map
        (SpecialLinearGroup.typeAGraphAutomorphism 2 F).toMonoidHom =
      FieldFourCover.unipTwo F := by
  have key : ∀ a c : F, SpecialLinearGroup.typeAGraphAutomorphism 2 F
      (FieldFourCover.unipU F a 0 c) = FieldFourCover.unipU F 0 a (-c) := by
    intro a c
    have hdec : FieldFourCover.unipU F a 0 c =
        SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) a *
          SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) c := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [FieldFourCover.coe_unipU, SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
          Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]
    rw [hdec, map_mul, SpecialLinearGroup.typeAGraphAutomorphism_transvection_of_ne,
      SpecialLinearGroup.typeAGraphAutomorphism_transvection_of_ne]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [FieldFourCover.coe_unipU, SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
        Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply, Fin.rev] <;> norm_num
  ext g
  constructor
  · rintro ⟨x, ⟨a, c, rfl⟩, rfl⟩
    exact ⟨a, -c, (key a c).symm⟩
  · rintro ⟨b, c, rfl⟩
    exact ⟨FieldFourCover.unipU F b 0 (-c), ⟨b, -c, rfl⟩, by simp [key]⟩

theorem exists_column_standard_cover {H : Type*} [Group H] {F : Type} [Field F]
    (e : (H ⧸ Subgroup.center H) ≃* LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* H) (hφsurj : Function.Surjective φ)
    (hφproj : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))).comp φ =
      LinearFlag.proj 3 F) :
    ∃ (e' : (H ⧸ Subgroup.center H) ≃* LinearFlag.projectiveSL 3 F)
      (φ' : Matrix.SpecialLinearGroup (Fin 3) F →* H),
      Function.Surjective φ' ∧
      (e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))).comp φ' =
        LinearFlag.proj 3 F ∧
      (FieldFourCover.unipOne F).map φ' = (FieldFourCover.unipTwo F).map φ := by
  refine ⟨e.trans (LinearFlag.descendAut 3 F
      (SpecialLinearGroup.typeAGraphAutomorphism 2 F)).symm,
    φ.comp (SpecialLinearGroup.typeAGraphAutomorphism 2 F).toMonoidHom,
    hφsurj.comp (SpecialLinearGroup.typeAGraphAutomorphism 2 F).surjective, ?_, ?_⟩
  · ext g
    have h := DFunLike.congr_fun hφproj (SpecialLinearGroup.typeAGraphAutomorphism 2 F g)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h ⊢
    rw [MulEquiv.trans_apply, h, MulEquiv.symm_apply_eq, LinearFlag.descendAut_proj]
  · rw [← Subgroup.map_map, map_unipOne_typeAGraphAutomorphism]

theorem isSylowOf_centralizer_column_of_standard
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hF : 16 ≤ Nat.card F)
    (A : Subgroup G)
    (hA : CFSG.Open.standardComponentIsStandard A)
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃* LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφsurj : Function.Surjective φ)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        LinearFlag.proj 3 F)
    (hcyc : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S)
    (t : G) (ht : orderOf t = 2)
    (htC : t ∈ Subgroup.centralizer (A : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf 2
      ((FieldFourCover.unipTwo F).map (A.subtype.comp φ) ⊔ Subgroup.zpowers t)
      (Subgroup.centralizer
        (((FieldFourCover.unipTwo F).map (A.subtype.comp φ) ⊔ Subgroup.zpowers t :
          Subgroup G) : Set G)) := by
  obtain ⟨e', φ', hsurj', hproj', hmap⟩ := exists_column_standard_cover e φ hφsurj hφproj
  have hE : (FieldFourCover.unipOne F).map (A.subtype.comp φ') =
      (FieldFourCover.unipTwo F).map (A.subtype.comp φ) := by
    rw [← Subgroup.map_map, hmap, Subgroup.map_map]
  have key := (exists_characteristic_odd_complement_of_standard_row hnonab hF A hA hZ e' φ'
    hsurj' hproj' hcyc t ht htC).2.2.1
  rw [hE] at key
  exact key

end CFSG.ComponentClassification.GS79bSec5
