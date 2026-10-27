module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import TauCeti.Algebra.Group.Subgroup.Map

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G]

theorem normalizer_le_normalizer_of_characteristic {C R : Subgroup G} (hCR : C ≤ R)
    (hC : (C.subgroupOf R).Characteristic) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  intro g hg
  let φ : MulAut R := Subgroup.normalizerMonoidHom R ⟨g, hg⟩
  have hfix : (C.subgroupOf R).map φ.toMonoidHom = C.subgroupOf R :=
    (Subgroup.characteristic_iff_map_eq.mp hC) φ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  calc
    C.map (MulAut.conj g).toMonoidHom
        = ((C.subgroupOf R).map R.subtype).map (MulAut.conj g).toMonoidHom := by
          rw [Subgroup.map_subgroupOf_eq_of_le hCR]
    _ = (C.subgroupOf R).map ((MulAut.conj g).toMonoidHom.comp R.subtype) := by
          rw [Subgroup.map_map]
    _ = (C.subgroupOf R).map (R.subtype.comp φ.toMonoidHom) := rfl
    _ = ((C.subgroupOf R).map φ.toMonoidHom).map R.subtype := by
          rw [Subgroup.map_map]
    _ = (C.subgroupOf R).map R.subtype := by rw [hfix]
    _ = C := Subgroup.map_subgroupOf_eq_of_le hCR

theorem map_conj_eq_of_characteristic {R C : Subgroup G} (hCR : C ≤ R)
    (hC : (C.subgroupOf R).Characteristic) {a b : G}
    (h : R.map (MulAut.conj a).toMonoidHom = R.map (MulAut.conj b).toMonoidHom) :
    C.map (MulAut.conj a).toMonoidHom = C.map (MulAut.conj b).toMonoidHom := by
  have hnorm : b⁻¹ * a ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc
      R.map (MulAut.conj (b⁻¹ * a)).toMonoidHom
          = (R.map (MulAut.conj a).toMonoidHom).map
              (MulAut.conj b⁻¹).toMonoidHom := by
            rw [Subgroup.map_conj_map_conj]
      _ = (R.map (MulAut.conj b).toMonoidHom).map
              (MulAut.conj b⁻¹).toMonoidHom := by rw [h]
      _ = R := by
            rw [Subgroup.map_conj_map_conj, inv_mul_cancel]
            simp [MulAut.one_def, MulEquiv.toMonoidHom_refl]
  have hCnorm : b⁻¹ * a ∈ Subgroup.normalizer (C : Set G) :=
    normalizer_le_normalizer_of_characteristic hCR hC hnorm
  have hfix : C.map (MulAut.conj (b⁻¹ * a)).toMonoidHom = C :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hCnorm
  calc
    C.map (MulAut.conj a).toMonoidHom
        = (C.map (MulAut.conj (b⁻¹ * a)).toMonoidHom).map
            (MulAut.conj b).toMonoidHom := by
          rw [Subgroup.map_conj_map_conj, mul_inv_cancel_left]
    _ = C.map (MulAut.conj b).toMonoidHom := by rw [hfix]

end CFSG.GroupTheory
