module

public import CFSG.GH74.KGroups.U33
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSingerAffine
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelDefs

public section

namespace CFSG.EvenSmallLie.Child3

open Subgroup

section Source

variable {Y : Type} [Group Y] (D : Subgroup Y) [D.Normal]

@[expose] def srcAut (a : Y) : MulAut D := MulAut.conjNormal a

theorem srcAut_apply (a : Y) (d : D) : ((srcAut D a d : D) : Y) = a * d * a⁻¹ :=
  MulAut.conjNormal_apply a d

variable {D}

theorem srcAut_sq {a : Y} (ha : orderOf a = 2) : srcAut D a ^ 2 = 1 := by
  rw [srcAut, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]

theorem srcAut_ne_one (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : orderOf a = 2) :
    srcAut D a ≠ 1 := by
  intro h1
  have hmem : a ∈ centralizer (D : Set Y) := by
    rw [mem_centralizer_iff]
    intro d hd
    have h2 := srcAut_apply D a ⟨d, hd⟩
    rw [h1, MulAut.one_apply] at h2
    calc d * a = (a * d * a⁻¹) * a := by rw [← h2]
      _ = a * d := by group
  rw [hCD, mem_bot] at hmem
  rw [hmem, orderOf_one] at ha
  exact absurd ha (by norm_num)

theorem srcAut_apply_of_mem {a : Y} {J : Subgroup Y} (hJa : J ≤ centralizer {a}) (d : D)
    (hd : (d : Y) ∈ J) : srcAut D a d = d := by
  apply Subtype.ext
  rw [srcAut_apply]
  have h := mem_centralizer_singleton_iff.1 (hJa hd)
  rw [← h, mul_inv_cancel_right]

end Source

theorem not_isSolvable_of_GL3 {J : Type*} [Group J] (ψ : J ≃* GL (Fin 3) (ZMod 2)) :
    ¬ Group.IsSolvable J := by
  intro hJ
  have : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
    CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger.isSimpleGroup_GL_three_zmod_two
  have hs : Group.IsSolvable (GL (Fin 3) (ZMod 2)) :=
    Group.isSolvable_of_surjective (f := ψ.toMonoidHom) ψ.surjective
  obtain ⟨x, y, hxy⟩ :=
    CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger.exists_mul_ne_mul_GL_three_zmod_two
  exact hxy (IsSimpleGroup.comm_iff_isSolvable.2 hs x y)

theorem false_of_U33 {Y : Type} [Group Y] {D : Subgroup Y}
    [D.Normal] (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : orderOf a = 2)
    {J : Subgroup Y} (hJD : J ≤ D) (hJa : J ≤ centralizer {a}) (ψ : J ≃* GL (Fin 3) (ZMod 2))
    (e : D ≃* CFSG.GH74.KGroups.U33.QP.originalSubgroup) : False := by
  have hsol := CFSG.GH74.KGroups.U33.fixed_solvable e (srcAut D a) (srcAut_sq ha)
    (srcAut_ne_one hCD ha) (J.subgroupOf D)
    (fun d hd => srcAut_apply_of_mem hJa d (mem_subgroupOf.1 hd))
  have hJ : Group.IsSolvable J :=
    Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hJD).toMonoidHom)
      (subgroupOfEquivOfLe hJD).surjective
  exact not_isSolvable_of_GL3 ψ hJ

theorem false_of_lieModel_U33
    {Y : Type} [Group Y] {D : Subgroup Y} [D.Normal]
    (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : orderOf a = 2) {J : Subgroup Y}
    (hJD : J ≤ D) (hJa : J ≤ centralizer {a}) (ψ : J ≃* GL (Fin 3) (ZMod 2))
    (hT : CFSG.Blueprint.LieModel D .PSU 3 3 1) : False := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hT
  exact false_of_U33 hCD ha hJD hJa ψ e

theorem excluded_psu33 :
    ExcludedLie .PSU 3 3 1 := by
  intro Y _ _ D a J h hT
  have := h.normal
  obtain ⟨ψ⟩ := h.gl3
  exact false_of_lieModel_U33 h.centralizer_eq h.orderOf_eq h.le h.le_centralizer ψ hT

end CFSG.EvenSmallLie.Child3
