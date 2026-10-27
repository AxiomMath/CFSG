module

public import CFSG.GH74.GLS.Stage2.Local.Defs
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelLT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

theorem layer_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.layer A).map e.toMonoidHom = CFSG.layer B :=
  CFSG.WholeGroup.layer_map_mulEquiv e

theorem centralizer_map_equiv {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (z : G) :
    (Subgroup.centralizer ({z} : Set G)).map Φ.toMonoidHom =
      Subgroup.centralizer ({Φ z} : Set H) := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    show Φ y * Φ z = Φ z * Φ y
    rw [← map_mul, ← map_mul, hy]
  · intro hx
    refine ⟨Φ.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx

@[expose] noncomputable def centralizerEquiv {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (z : G) :
    ↥(Subgroup.centralizer ({z} : Set G)) ≃* ↥(Subgroup.centralizer ({Φ z} : Set H)) :=
  (MulEquiv.subgroupMap Φ _).trans (MulEquiv.subgroupCongr (centralizer_map_equiv Φ z))

@[simp] theorem coe_centralizerEquiv {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (z : G)
    (x : ↥(Subgroup.centralizer ({z} : Set G))) :
    ((centralizerEquiv Φ z x : ↥(Subgroup.centralizer ({Φ z} : Set H))) : H) = Φ (x : G) :=
  rfl

theorem subtype_comp_centralizerEquiv {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (z : G) :
    (Subgroup.centralizer ({Φ z} : Set H)).subtype.comp (centralizerEquiv Φ z).toMonoidHom =
      Φ.toMonoidHom.comp (Subgroup.centralizer ({z} : Set G)).subtype := by
  ext x
  rfl

theorem layerTimesSylow_map {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (z : G)
    (S : Subgroup G) :
    (layerTimesSylow z S).map Φ.toMonoidHom = layerTimesSylow (Φ z) (S.map Φ.toMonoidHom) := by
  unfold layerTimesSylow
  rw [Subgroup.map_sup]
  congr 1
  rw [Subgroup.map_map, ← layer_map_equiv (centralizerEquiv Φ z), Subgroup.map_map,
    subtype_comp_centralizerEquiv]

theorem oddCore_map {G H : Type} [Group G] [Group H] (Φ : G ≃* H) (z : G) :
    (OddCore z).map Φ.toMonoidHom = OddCore (Φ z) := by
  unfold OddCore pPrimeCoreOf
  rw [Subgroup.map_map, ← CFSG.pPrimeCore_map_iso 2 (centralizerEquiv Φ z), Subgroup.map_map,
    subtype_comp_centralizerEquiv]

@[expose] noncomputable def barEquiv {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (z : G) :
    CentralizerBar z ≃* CentralizerBar (Φ z) :=
  QuotientGroup.congr _ _ (centralizerEquiv Φ z)
    (CFSG.pPrimeCore_map_iso 2 (centralizerEquiv Φ z))

theorem barEquiv_mk {G H : Type} [Group G] [Group H] (Φ : G ≃* H) (z : G)
    (x : ↥(Subgroup.centralizer ({z} : Set G))) :
    barEquiv Φ z (toBar z x) = toBar (Φ z) (centralizerEquiv Φ z x) :=
  rfl

theorem subgroupOf_cen_map {G H : Type} [Group G] [Group H] (Φ : G ≃* H) (z : G) (X : Subgroup G) :
    (X.subgroupOf (Cen z)).map (centralizerEquiv Φ z).toMonoidHom =
      (X.map Φ.toMonoidHom).subgroupOf (Cen (Φ z)) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x : G), hx, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    have hxc : x ∈ Cen z := by
      have hy := y.2
      rw [← hxy] at hy
      have := (Subgroup.mem_map_iff_mem (f := Φ.toMonoidHom) Φ.injective).1
        ((centralizer_map_equiv Φ z).symm ▸ hy : Φ.toMonoidHom x ∈ (Cen z).map Φ.toMonoidHom)
      exact this
    refine ⟨⟨x, hxc⟩, hx, Subtype.ext hxy⟩

theorem barOf_map {G H : Type} [Group G] [Group H] (Φ : G ≃* H) (z : G) (X : Subgroup G) :
    (barOf z X).map (barEquiv Φ z).toMonoidHom = barOf (Φ z) (X.map Φ.toMonoidHom) := by
  unfold barOf
  rw [Subgroup.map_map, ← subgroupOf_cen_map, Subgroup.map_map]
  rfl

theorem oPrimeResidual_map_equiv {A B : Type*} [Group A] [Group B] (p : ℕ) (e : A ≃* B) :
    (oPrimeResidual p A).map e.toMonoidHom = oPrimeResidual p B := by
  unfold oPrimeResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  · rintro ⟨k, hk⟩
    refine ⟨e.symm y, ⟨k, ?_⟩, by simp⟩
    apply e.injective
    rw [map_pow, map_one, MulEquiv.apply_symm_apply, hk]

theorem oPrimeResidual_barEquiv {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (z : G) :
    (oPrimeResidual 2 (CentralizerBar z)).map (barEquiv Φ z).toMonoidHom =
      oPrimeResidual 2 (CentralizerBar (Φ z)) :=
  oPrimeResidual_map_equiv 2 (barEquiv Φ z)

theorem layerBarAt_of_equiv {G H : Type} [Group G] [Group H] (Φ : G ≃* H) (z : G) (S : Subgroup G)
    (h : layerTimesSylow (Φ z) (S.map Φ.toMonoidHom) ⊓ OddCore (Φ z) = ⊥ ∧
      barOf (Φ z) (layerTimesSylow (Φ z) (S.map Φ.toMonoidHom)) =
        oPrimeResidual 2 (CentralizerBar (Φ z))) :
    layerTimesSylow z S ⊓ OddCore z = ⊥ ∧
      barOf z (layerTimesSylow z S) = oPrimeResidual 2 (CentralizerBar z) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · have hmap : (layerTimesSylow z S ⊓ OddCore z).map Φ.toMonoidHom = ⊥ := by
      rw [Subgroup.map_inf _ _ _ Φ.injective, layerTimesSylow_map, oddCore_map, h1]
    exact (Subgroup.map_eq_bot_iff_of_injective _ Φ.injective).1 hmap
  · apply Subgroup.map_injective (f := (barEquiv Φ z).toMonoidHom) (barEquiv Φ z).injective
    rw [barOf_map, layerTimesSylow_map, h2, oPrimeResidual_barEquiv]

end CFSG.GH74.GLS.Stage2.Final.ModelLT
