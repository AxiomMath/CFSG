module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B513Norm
public import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem sec5b517_mem_conj {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rwa [h]
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

private def sec5b517_restrictIso (φ : G ≃* G) (X X' : Subgroup G)
    (h : X.map φ.toMonoidHom = X') : X ≃* X' :=
  (MulEquiv.subgroupMap φ X).trans (MulEquiv.subgroupCongr h)

private theorem sec5b517_inSubgroup_layer_map (φ : G ≃* G) (X X' : Subgroup G)
    (h : X.map φ.toMonoidHom = X') :
    CFSG.inSubgroup CFSG.layer X' = (CFSG.inSubgroup CFSG.layer X).map φ.toMonoidHom := by
  have key := CFSG.WholeGroup.layer_map_mulEquiv (sec5b517_restrictIso φ X X' h)
  unfold CFSG.inSubgroup
  rw [← key, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem sec5b517_centralizer_singleton_conj (u g : G) :
    (centralizer ({u} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
      centralizer ({g⁻¹ * u * g} : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    calc g⁻¹ * y * g * (g⁻¹ * u * g) = g⁻¹ * (y * u) * g := by group
      _ = g⁻¹ * (u * y) * g := by rw [hy]
      _ = g⁻¹ * u * g * (g⁻¹ * y * g) := by group
  · intro hx
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · calc g * x * g⁻¹ * u = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by rw [hx]
        _ = u * (g * x * g⁻¹) := by group
    · group

theorem sec5b517_conjugate_conjugate (X : Subgroup G) (g g' : G) :
    CFSG.conjugate (CFSG.conjugate X g) g' = CFSG.conjugate X (g * g') := by
  rw [CFSG.conjugate, CFSG.conjugate, CFSG.conjugate, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  group

theorem sec5b517_conjugate_inf (X Y : Subgroup G) (g : G) :
    CFSG.conjugate (X ⊓ Y) g = CFSG.conjugate X g ⊓ CFSG.conjugate Y g := by
  ext x
  simp only [sec5b517_mem_conj, Subgroup.mem_inf]

theorem sec5b517_conjugate_one (X : Subgroup G) : CFSG.conjugate X 1 = X := by
  ext x
  rw [sec5b517_mem_conj]
  simp

theorem sec5b517_inSubgroup_layer_conjugate (X : Subgroup G) (g : G) :
    CFSG.inSubgroup CFSG.layer (CFSG.conjugate X g) =
      CFSG.conjugate (CFSG.inSubgroup CFSG.layer X) g := by
  exact sec5b517_inSubgroup_layer_map (MulAut.conj g⁻¹) X (CFSG.conjugate X g) rfl

theorem sec5b517_centralizer_conj (d g : G) :
    centralizer ({g⁻¹ * d * g} : Set G) = CFSG.conjugate (centralizer ({d} : Set G)) g := by
  rw [CFSG.conjugate]
  exact (sec5b517_centralizer_singleton_conj d g).symm

theorem sec5b517_layerC5_conj (d g : G) :
    layerC5 (g⁻¹ * d * g) = CFSG.conjugate (layerC5 d) g := by
  unfold layerC5
  rw [sec5b517_centralizer_conj d g]
  exact sec5b517_inSubgroup_layer_conjugate (centralizer ({d} : Set G)) g

theorem sec5b517_twoRes_cov {z g : G} (hg : g ∈ centralizer ({z} : Set G)) (d : G) :
    twoRes (centralizer ({z} : Set G) ⊓ layerC5 (g⁻¹ * d * g)) =
      CFSG.conjugate (twoRes (centralizer ({z} : Set G) ⊓ layerC5 d)) g := by
  have hz : CFSG.conjugate (centralizer ({z} : Set G)) g = centralizer ({z} : Set G) :=
    (sec5b513_conjugate_eq_iff (H := centralizer ({z} : Set G)) (g := g)).mpr
      (Subgroup.le_normalizer hg)
  have harg : centralizer ({z} : Set G) ⊓ CFSG.conjugate (layerC5 d) g =
      CFSG.conjugate (centralizer ({z} : Set G) ⊓ layerC5 d) g := by
    rw [sec5b517_conjugate_inf, hz]
  rw [sec5b517_layerC5_conj]
  rw [harg]
  exact sec5b513_twoRes_conjugate (centralizer ({z} : Set G) ⊓ layerC5 d) g

end CFSG.OddStandard.SmallF3.Omega
