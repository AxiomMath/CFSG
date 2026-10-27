module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpFig20Fam

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}
  {F : Fam a α} {θ : G → G'}

theorem cp_fam_apply_x (h : F5Std a z) (hθ : IsTheta a F θ) {b x : G} (hxA : IsConj a x)
    (hb : b ∈ orb2A a a) (hbx : b ∈ orb2A a x) (ℬ : Fam b (F.app b)) : ℬ.app x x = θ x := by
  have hbG : b ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) hb
  have hbxG : b ∈ Gx x := h.mem_Gx_of_orb2A hxA hbx
  have hxb : x ∈ Gx b := mem_Gx.2 (mem_Gx.1 hbxG).symm
  have hxInv : x ∈ InvIn (Gx b) := ⟨hxb, h.orderOf_eq_two (Or.inl hxA)⟩
  rw [ℬ.restrict x hxInv x (mem_Gxy.2 ⟨hxb, self_mem_Gx x⟩)]
  exact (hθ.eq_app x hxA b ⟨mem_Gxy.2 ⟨hbG, hbxG⟩, h.orderOf_eq_two (Or.inl hb.1)⟩).symm

theorem cp_fam_prod_typed (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (hθ : IsTheta a F θ) {b x u v : G} (hb : b ∈ orb2A a a) (ℬ : Fam b (F.app b))
    (hx : x ∈ InvIn (Gx b)) (hu : u ∈ Gx x) (hv : v ∈ Gx x) (huv : IsConj a (u * v)) :
    IsConj a' (ℬ.app x u * ℬ.app x v) := by
  obtain ⟨hb', hβ⟩ := cp_beta_b h h' hα hθ hb
  rw [← (ℬ.iso x hx).map_mul u hu v hv]
  exact Fam.typed h h' hb.1 hb' hβ ℬ hx ((Gx x).mul_mem hu hv) huv

theorem cp_fig20_swap {b x : G} {β : G → G'} (hbb : b * b = 1) (hbx : b ∈ Gx x)
    (ℬ ℬ' : Fam b β)
    (hu : (∀ u ∈ Gx x, ℬ.app x u = ℬ'.app x u) ∨
      ∀ u ∈ Gx x, ℬ.app x u = ℬ'.app x (b * u * b⁻¹)) {v : G} (hv : v ∈ Gx x) {w : G'}
    (hw : w = ℬ'.app x v ∨ w = ℬ'.app x (b * v * b⁻¹)) :
    w = ℬ.app x v ∨ w = ℬ.app x (b * v * b⁻¹) := by
  have hvb : b * v * b⁻¹ ∈ Gx x := (Gx x).mul_mem ((Gx x).mul_mem hbx hv) ((Gx x).inv_mem hbx)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hbvb : b * (b * v * b⁻¹) * b⁻¹ = v := by
    rw [hbi]
    calc b * (b * v * b) * b = (b * b) * v * (b * b) := by group
      _ = v := by rw [hbb]; group
  rcases hu with hu | hu
  · rcases hw with hw | hw
    · exact Or.inl (hw.trans (hu v hv).symm)
    · exact Or.inr (hw.trans (hu _ hvb).symm)
  · rcases hw with hw | hw
    · refine Or.inr (hw.trans ?_)
      rw [hu _ hvb, hbvb]
    · exact Or.inl (hw.trans (hu v hv).symm)

theorem cp_ne_of_isConj_mul (h' : F5Std a' z') {u v : G'} (hu : IsConj a' u)
    (huv : IsConj a' (u * v)) : u ≠ v := by
  rintro rfl
  rw [cp_mul_self_eq_one h' (Or.inl hu)] at huv
  exact cp_ne_one_of_orderOf_eq_two h'.typ.orderOf_a (isConj_one_left.1 huv)

theorem cp_dihedral_yb {b y : G} (hbb : b * b = 1) (hyy : y * y = 1)
    (hzz : (b * y) ^ 2 * (b * y) ^ 2 = 1) :
    y * (b * y * b⁻¹) = (b * y) ^ 2 ∧ b * y * b⁻¹ * y = (b * y) ^ 2 ∧
      b * y * b⁻¹ * (b * y * b⁻¹) = 1 := by
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hzi : ((b * y) ^ 2)⁻¹ = (b * y) ^ 2 := inv_eq_of_mul_eq_one_right hzz
  refine ⟨?_, ?_, ?_⟩
  · have e : ((b * y) ^ 2)⁻¹ = y * (b * y * b⁻¹) := by
      rw [← inv_pow, mul_inv_rev, hyi, hbi]
      simp only [pow_two, mul_assoc]
    exact e.symm.trans hzi
  · rw [hbi]
    simp only [pow_two, mul_assoc]
  · calc b * y * b⁻¹ * (b * y * b⁻¹) = b * (y * y) * b⁻¹ := by group
      _ = 1 := by rw [hyy]; group

end CFSG.EvenSporadicStandard.HNRecog.Section4
