module

public import CFSG.Holt.H78.Data

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]
  {G' : Type*} [Group G'] {Ω' : Type*} [MulAction G' Ω']

section Injective

variable {f : G →* G'} {e : Ω ≃ Ω'}

theorem mem_longInv_map_iff (hf : Function.Injective f)
    (he : ∀ (g : G) (ω : Ω), e (g • ω) = f g • e ω) (g : G) :
    f g ∈ longInv G' Ω' ↔ g ∈ longInv G Ω := by
  rw [mem_longInv, mem_longInv, orderOf_injective f hf g]
  exact and_congr_right fun _ =>
    (e.existsUnique_congr fun ω => by rw [← he, e.apply_eq_iff_eq]).symm

theorem map_jHull_of_injective (hf : Function.Injective f)
    (he : ∀ (g : G) (ω : Ω), e (g • ω) = f g • e ω) (hJ : longInv G' Ω' ⊆ f.range) :
    (jHull G Ω).map f = jHull G' Ω' := by
  rw [jHull, jHull, MonoidHom.map_closure]
  congr 1
  ext g'
  refine ⟨?_, fun hg' => ?_⟩
  · rintro ⟨g, hg, rfl⟩
    exact (mem_longInv_map_iff hf he g).mpr hg
  · obtain ⟨g, rfl⟩ := hJ hg'
    exact ⟨g, (mem_longInv_map_iff hf he g).mp hg', rfl⟩

variable (f e) in
@[expose] noncomputable def hullEquivOfInjective (hf : Function.Injective f)
    (he : ∀ (g : G) (ω : Ω), e (g • ω) = f g • e ω) (hJ : longInv G' Ω' ⊆ f.range) :
    jHull G Ω ≃* jHull G' Ω' :=
  ((jHull G Ω).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr (map_jHull_of_injective hf he hJ))

@[simp] theorem coe_hullEquivOfInjective_apply (hf : Function.Injective f)
    (he : ∀ (g : G) (ω : Ω), e (g • ω) = f g • e ω) (hJ : longInv G' Ω' ⊆ f.range)
    (h : jHull G Ω) : (hullEquivOfInjective f e hf he hJ h : G') = f h :=
  rfl

end Injective

section HullEquiv

variable {ψ : jHull G Ω ≃* jHull G' Ω'} {e : Ω ≃ Ω'}

theorem coe_mem_longInv_hullEquiv_iff
    (he : ∀ (h : jHull G Ω) (ω : Ω), e ((h : G) • ω) = (ψ h : G') • e ω) (h : jHull G Ω) :
    (ψ h : G') ∈ longInv G' Ω' ↔ (h : G) ∈ longInv G Ω :=
  (mem_longInv_map_iff (f := (jHull G' Ω').subtype.comp ψ.toMonoidHom)
    ((jHull G' Ω').subtype_injective.comp ψ.injective) he h).trans mem_longInv_subgroup_iff

theorem map_jOddCore_hullEquiv (ψ : jHull G Ω ≃* jHull G' Ω') :
    ((jOddCore G Ω).subgroupOf (jHull G Ω)).map ψ.toMonoidHom =
      (jOddCore G' Ω').subgroupOf (jHull G' Ω') := by
  rw [jOddCore_subgroupOf_jHull, jOddCore_subgroupOf_jHull]
  exact CFSG.pPrimeCore_map_iso 2 ψ

theorem coe_mem_jOddCore_hullEquiv_iff (h : jHull G Ω) :
    (ψ h : G') ∈ jOddCore G' Ω' ↔ (h : G) ∈ jOddCore G Ω := by
  change ψ h ∈ (jOddCore G' Ω').subgroupOf (jHull G' Ω') ↔
    h ∈ (jOddCore G Ω).subgroupOf (jHull G Ω)
  rw [← map_jOddCore_hullEquiv ψ, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem mem_orbit_jOddCore_hullEquiv_iff
    (he : ∀ (h : jHull G Ω) (ω : Ω), e ((h : G) • ω) = (ψ h : G') • e ω) (x y : Ω) :
    e x ∈ orbit (jOddCore G' Ω') (e y) ↔ x ∈ orbit (jOddCore G Ω) y := by
  constructor
  · rintro ⟨⟨o', ho'⟩, hxy⟩
    set k : jHull G' Ω' := ⟨o', jOddCore_le_jHull ho'⟩
    have hk : ((ψ.symm k : jHull G Ω) : G) ∈ jOddCore G Ω := by
      rw [← coe_mem_jOddCore_hullEquiv_iff (ψ := ψ), MulEquiv.apply_symm_apply]
      exact ho'
    refine ⟨⟨_, hk⟩, e.injective ?_⟩
    change e (((ψ.symm k : jHull G Ω) : G) • y) = e x
    rw [he, MulEquiv.apply_symm_apply]
    exact hxy
  · rintro ⟨⟨o, ho⟩, rfl⟩
    refine ⟨⟨(ψ ⟨o, jOddCore_le_jHull ho⟩ : G'), (coe_mem_jOddCore_hullEquiv_iff _).mpr ho⟩, ?_⟩
    change (ψ ⟨o, jOddCore_le_jHull ho⟩ : G') • e y = e (o • y)
    rw [← he]

theorem coe_mem_jOrbitKernel_hullEquiv_iff
    (he : ∀ (h : jHull G Ω) (ω : Ω), e ((h : G) • ω) = (ψ h : G') • e ω) (h : jHull G Ω) :
    (ψ h : G') ∈ jOrbitKernel G' Ω' ↔ (h : G) ∈ jOrbitKernel G Ω := by
  rw [mem_jOrbitKernel_iff, mem_jOrbitKernel_iff]
  refine ⟨fun hk => ⟨h.2, fun ω => ?_⟩, fun hk => ⟨(ψ h).2, fun ω' => ?_⟩⟩
  · rw [← mem_orbit_jOddCore_hullEquiv_iff he, he]
    exact hk.2 (e ω)
  · rw [← e.apply_symm_apply ω', ← he, mem_orbit_jOddCore_hullEquiv_iff he]
    exact hk.2 _

end HullEquiv

section HullMap

variable (ψ : jHull G Ω ≃* jHull G' Ω')

@[expose] def hullMap (A : Subgroup G) : Subgroup G' :=
  ((A.subgroupOf (jHull G Ω)).map ψ.toMonoidHom).map (jHull G' Ω').subtype

variable {ψ}

theorem mem_hullMap {A : Subgroup G} {g' : G'} :
    g' ∈ hullMap ψ A ↔ ∃ h : jHull G Ω, (h : G) ∈ A ∧ (ψ h : G') = g' := by
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨ψ h, ⟨h, hh, rfl⟩, rfl⟩

@[simp] theorem coe_mem_hullMap_iff {A : Subgroup G} (h : jHull G Ω) :
    (ψ h : G') ∈ hullMap ψ A ↔ (h : G) ∈ A := by
  rw [mem_hullMap]
  refine ⟨fun ⟨k, hk, hkh⟩ => ?_, fun hh => ⟨h, hh, rfl⟩⟩
  rwa [← ψ.injective (Subtype.ext hkh)]

theorem hullMap_le_jHull (A : Subgroup G) : hullMap ψ A ≤ jHull G' Ω' :=
  Subgroup.map_subtype_le _

theorem hullMap_mono {A B : Subgroup G} (hAB : A ≤ B) : hullMap ψ A ≤ hullMap ψ B := by
  intro g' hg'
  obtain ⟨h, hh, rfl⟩ := mem_hullMap.mp hg'
  exact (coe_mem_hullMap_iff h).mpr (hAB hh)

theorem hullMap_le_iff {A : Subgroup G} {S : Subgroup G'} :
    hullMap ψ A ≤ S ↔ ∀ h : jHull G Ω, (h : G) ∈ A → (ψ h : G') ∈ S := by
  refine ⟨fun hA h hh => hA ((coe_mem_hullMap_iff h).mpr hh), fun hA g' hg' => ?_⟩
  obtain ⟨h, hh, rfl⟩ := mem_hullMap.mp hg'
  exact hA h hh

theorem hullMap_eq_of_forall {A : Subgroup G} {A' : Subgroup G'} (hA' : A' ≤ jHull G' Ω')
    (hAA' : ∀ h : jHull G Ω, (ψ h : G') ∈ A' ↔ (h : G) ∈ A) : hullMap ψ A = A' := by
  ext g'
  rw [mem_hullMap]
  refine ⟨fun ⟨h, hh, hg'⟩ => hg' ▸ (hAA' h).mpr hh, fun hg' => ?_⟩
  refine ⟨ψ.symm ⟨g', hA' hg'⟩, (hAA' _).mp ?_, ?_⟩
  · rw [MulEquiv.apply_symm_apply]
    exact hg'
  · rw [MulEquiv.apply_symm_apply]

theorem hullMap_jHull : hullMap ψ (jHull G Ω) = jHull G' Ω' :=
  hullMap_eq_of_forall le_rfl fun h => ⟨fun _ => h.2, fun _ => (ψ h).2⟩

theorem hullMap_jOddCore : hullMap ψ (jOddCore G Ω) = jOddCore G' Ω' :=
  hullMap_eq_of_forall jOddCore_le_jHull coe_mem_jOddCore_hullEquiv_iff

theorem hullMap_bot : hullMap ψ (⊥ : Subgroup G) = ⊥ :=
  hullMap_eq_of_forall bot_le fun h => by simp

theorem hullMap_jOrbitKernel {e : Ω ≃ Ω'}
    (he : ∀ (h : jHull G Ω) (ω : Ω), e ((h : G) • ω) = (ψ h : G') • e ω) :
    hullMap ψ (jOrbitKernel G Ω) = jOrbitKernel G' Ω' :=
  hullMap_eq_of_forall jOrbitKernel_le_jHull (coe_mem_jOrbitKernel_hullEquiv_iff he)

private theorem coe_mem_pull_iff {S : Subgroup G'} (h : jHull G Ω) :
    (h : G) ∈ (S.comap ((jHull G' Ω').subtype.comp ψ.toMonoidHom)).map (jHull G Ω).subtype ↔
      (ψ h : G') ∈ S := by
  refine ⟨fun ⟨k, hk, hkh⟩ => ?_, fun hh => ⟨h, hh, rfl⟩⟩
  obtain rfl : k = h := Subtype.ext hkh
  exact hk

private theorem le_pull {A : Subgroup G} (hA : A ≤ jHull G Ω) {S : Subgroup G'}
    (hAS : hullMap ψ A ≤ S) :
    A ≤ (S.comap ((jHull G' Ω').subtype.comp ψ.toMonoidHom)).map (jHull G Ω).subtype :=
  fun g hg => (coe_mem_pull_iff (h := ⟨g, hA hg⟩)).mpr (hullMap_le_iff.mp hAS _ hg)

private theorem hullMap_le_of_le_pull {A : Subgroup G} {S : Subgroup G'}
    (hA : A ≤ (S.comap ((jHull G' Ω').subtype.comp ψ.toMonoidHom)).map (jHull G Ω).subtype) :
    hullMap ψ A ≤ S :=
  hullMap_le_iff.mpr fun h hh => (coe_mem_pull_iff h).mp (hA hh)

theorem hullMap_sup {A B : Subgroup G} (hA : A ≤ jHull G Ω) (hB : B ≤ jHull G Ω) :
    hullMap ψ (A ⊔ B) = hullMap ψ A ⊔ hullMap ψ B :=
  le_antisymm
    (hullMap_le_of_le_pull (sup_le (le_pull hA le_sup_left) (le_pull hB le_sup_right)))
    (sup_le (hullMap_mono le_sup_left) (hullMap_mono le_sup_right))

theorem hullMap_iSup {ι : Sort*} {A : ι → Subgroup G} (hA : ∀ i, A i ≤ jHull G Ω) :
    hullMap ψ (⨆ i, A i) = ⨆ i, hullMap ψ (A i) :=
  le_antisymm
    (hullMap_le_of_le_pull (iSup_le fun i =>
      le_pull (hA i) (le_iSup (fun i => hullMap ψ (A i)) i)))
    (iSup_le fun i => hullMap_mono (le_iSup A i))

theorem hullMap_zpowers (h : jHull G Ω) :
    hullMap ψ (Subgroup.zpowers (h : G)) = Subgroup.zpowers (ψ h : G') := by
  refine le_antisymm (hullMap_le_iff.mpr fun k hk => ?_)
    (Subgroup.zpowers_le.mpr ((coe_mem_hullMap_iff h).mpr (Subgroup.mem_zpowers _)))
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hk
  obtain rfl : k = h ^ n := Subtype.ext (by rw [Subgroup.coe_zpow, hn])
  rw [map_zpow, Subgroup.coe_zpow]
  exact Subgroup.zpow_mem_zpowers _ n

theorem relIndex_hullMap {A B : Subgroup G} (hA : A ≤ jHull G Ω) (hB : B ≤ jHull G Ω) :
    (hullMap ψ A).relIndex (hullMap ψ B) = A.relIndex B := by
  have hΦ : Function.Injective ((jHull G' Ω').subtype.comp ψ.toMonoidHom) :=
    (jHull G' Ω').subtype_injective.comp ψ.injective
  rw [hullMap, hullMap, Subgroup.map_map, Subgroup.map_map,
    Subgroup.relIndex_map_map_of_injective _ _ hΦ,
    ← Subgroup.relIndex_map_map_of_injective _ _ (jHull G Ω).subtype_injective,
    Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_of_le_left hA,
    inf_of_le_left hB]

theorem le_normalizer_hullMap {A : Subgroup G}
    (hA : jHull G Ω ≤ Subgroup.normalizer (A : Set G)) :
    jHull G' Ω' ≤ Subgroup.normalizer (hullMap ψ A : Set G') := by
  intro g' hg'
  obtain ⟨k, hk⟩ : ∃ k : jHull G Ω, ψ k = ⟨g', hg'⟩ := ⟨ψ.symm _, ψ.apply_symm_apply _⟩
  have hconj : ∀ l : jHull G Ω, g' * (ψ l : G') * g'⁻¹ = (ψ (k * l * k⁻¹) : G') := fun l => by
    rw [map_mul, map_mul, map_inv, hk]
    rfl
  have hkA := Subgroup.mem_normalizer_iff.mp (hA k.2)
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨l, hl, rfl⟩ := mem_hullMap.mp hx
    rw [hconj, coe_mem_hullMap_iff]
    exact (hkA l).mp hl
  · have hxH : x ∈ jHull G' Ω' := by
      have h1 := (jHull G' Ω').mul_mem
        ((jHull G' Ω').mul_mem (inv_mem hg') (hullMap_le_jHull A hx)) hg'
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h1
    obtain ⟨l, rfl⟩ : ∃ l : jHull G Ω, (ψ l : G') = x :=
      ⟨ψ.symm ⟨x, hxH⟩, by rw [MulEquiv.apply_symm_apply]⟩
    rw [hconj, coe_mem_hullMap_iff] at hx
    exact (coe_mem_hullMap_iff l).mpr ((hkA l).mpr hx)

theorem factorImage_hullMap {X : Type*} (L : Subgroup G) (ρ : jHull G Ω →* Equiv.Perm X) :
    factorImage G' Ω' (hullMap ψ L) (ρ.comp ψ.symm.toMonoidHom) = factorImage G Ω L ρ := by
  ext x
  rw [mem_factorImage, mem_factorImage]
  constructor
  · rintro ⟨h', hh', rfl⟩
    refine ⟨ψ.symm h', ?_, rfl⟩
    rwa [← coe_mem_hullMap_iff (ψ := ψ), MulEquiv.apply_symm_apply]
  · rintro ⟨h, hh, rfl⟩
    refine ⟨ψ h, (coe_mem_hullMap_iff h).mpr hh, ?_⟩
    simp

end HullMap

namespace HoltData

@[expose] def transport (D : HoltData G Ω) (ψ : jHull G Ω ≃* jHull G' Ω') (e : Ω ≃ Ω')
    (he : ∀ (h : jHull G Ω) (ω : Ω), e ((h : G) • ω) = (ψ h : G') • e ω) :
    HoltData G' Ω' where
  ι := D.ι
  Ψc := D.Ψc
  coord ω' := D.coord (e.symm ω')
  ρ i := (D.ρ i).comp ψ.symm.toMonoidHom
  L i := hullMap ψ (D.L i)
  t := (ψ D.tHull : G')
  t_mem := (coe_mem_longInv_hullEquiv_iff he D.tHull).mpr D.t_mem
  coord_eq_iff ω₁ ω₂ := by
    rw [D.coord_eq_iff, ← mem_orbit_jOddCore_hullEquiv_iff he, e.apply_symm_apply,
      e.apply_symm_apply]
  coord_surjective := D.coord_surjective.comp e.symm.surjective
  coord_smul h' ω' i := by
    have hω : e.symm ((h' : G') • ω') = ((ψ.symm h' : jHull G Ω) : G) • e.symm ω' := by
      rw [e.symm_apply_eq, he, MulEquiv.apply_symm_apply, e.apply_symm_apply]
    rw [hω, D.coord_smul]
    rfl
  L_le _ := hullMap_le_jHull _
  oddCore_le i := hullMap_jOddCore (ψ := ψ) ▸ hullMap_mono (D.oddCore_le i)
  le_normalizer i := le_normalizer_hullMap (D.le_normalizer i)
  le_ker i j hij h' hh' := by
    have hh : ((ψ.symm h' : jHull G Ω) : G) ∈ D.L i := by
      rw [← coe_mem_hullMap_iff (ψ := ψ), MulEquiv.apply_symm_apply]
      exact hh'
    exact D.le_ker i j hij hh
  inf_ker i := by
    ext h'
    obtain ⟨h, rfl⟩ := ψ.surjective h'
    have hk := SetLike.ext_iff.mp (D.inf_ker i) h
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, MonoidHom.mem_ker] at hk ⊢
    rw [coe_mem_hullMap_iff, coe_mem_jOddCore_hullEquiv_iff, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hk
  factor i := by
    rw [factorImage_hullMap]
    exact D.factor i
  sup_eq := by
    rw [← hullMap_jOddCore (ψ := ψ), ← hullMap_iSup D.L_le, ← hullMap_zpowers,
      ← hullMap_sup jOddCore_le_jHull (iSup_le D.L_le),
      ← hullMap_sup (sup_le jOddCore_le_jHull (iSup_le D.L_le))
        (Subgroup.zpowers_le.mpr D.tHull.2), D.sup_eq, hullMap_jHull]
  inner i hi := by
    rw [factorImage_hullMap] at hi ⊢
    have h1 : ∀ p, ψ.symm ⟨(ψ D.tHull : G'), p⟩ = D.tHull := fun p => by
      rw [show (⟨(ψ D.tHull : G'), p⟩ : jHull G' Ω') = ψ D.tHull from Subtype.ext rfl,
        MulEquiv.symm_apply_apply]
    convert D.inner i hi using 1
    exact congrArg (D.ρ i) (h1 _)
  ker_outer h := by
    simp only [factorImage_hullMap] at h
    rw [← hullMap_jOrbitKernel he, ← hullMap_jOddCore (ψ := ψ), D.ker_outer h]
  ker_inner h := by
    simp only [factorImage_hullMap] at h
    obtain ⟨h1, h2⟩ := D.ker_inner h
    refine ⟨?_, fun hO => ?_⟩
    · rw [← hullMap_jOddCore (ψ := ψ), ← hullMap_iSup D.L_le, ← hullMap_jOrbitKernel he,
        ← hullMap_sup jOddCore_le_jHull (iSup_le D.L_le),
        ← hullMap_sup (sup_le jOddCore_le_jHull (iSup_le D.L_le)) jOrbitKernel_le_jHull]
      exact (coe_mem_hullMap_iff D.tHull).mpr h1
    · rw [← hullMap_jOddCore (ψ := ψ), ← hullMap_jOrbitKernel he,
        relIndex_hullMap jOddCore_le_jHull jOrbitKernel_le_jHull]
      refine h2 fun hO' => hO ?_
      rw [← hullMap_jOddCore (ψ := ψ), hO', hullMap_bot]

variable (D : HoltData G Ω) (ψ : jHull G Ω ≃* jHull G' Ω') (e : Ω ≃ Ω')
  (he : ∀ (h : jHull G Ω) (ω : Ω), e ((h : G) • ω) = (ψ h : G') • e ω)

@[simp] theorem transport_ι : (D.transport ψ e he).ι = D.ι := rfl

@[simp] theorem transport_Ψc (i : D.ι) : (D.transport ψ e he).Ψc i = D.Ψc i := rfl

theorem transport_coord (ω' : Ω') : (D.transport ψ e he).coord ω' = D.coord (e.symm ω') := rfl

theorem transport_coord_apply (ω : Ω) : (D.transport ψ e he).coord (e ω) = D.coord ω := by
  rw [transport_coord, e.symm_apply_apply]

@[simp] theorem transport_M (i : D.ι) : (D.transport ψ e he).M i = D.M i :=
  factorImage_hullMap _ _

variable {f : G →* G'} {e : Ω ≃ Ω'}

@[expose] noncomputable def map (D : HoltData G Ω) (hf : Function.Injective f)
    (he : ∀ (g : G) (ω : Ω), e (g • ω) = f g • e ω) (hJ : longInv G' Ω' ⊆ f.range) :
    HoltData G' Ω' :=
  D.transport (hullEquivOfInjective f e hf he hJ) e fun h ω => he h ω

@[expose] noncomputable def comap (D' : HoltData G' Ω') (hf : Function.Injective f)
    (he : ∀ (g : G) (ω : Ω), e (g • ω) = f g • e ω) (hJ : longInv G' Ω' ⊆ f.range) :
    HoltData G Ω :=
  D'.transport (hullEquivOfInjective f e hf he hJ).symm e.symm fun h' ω' => by
    rw [Equiv.symm_apply_eq, he, ← coe_hullEquivOfInjective_apply hf he hJ,
      MulEquiv.apply_symm_apply, e.apply_symm_apply]

@[expose] noncomputable def congr (D : HoltData G Ω) (φ : G ≃* G') (e : Ω ≃ Ω')
    (he : ∀ (g : G) (ω : Ω), e (g • ω) = φ g • e ω) : HoltData G' Ω' :=
  D.map (f := φ.toMonoidHom) φ.injective he fun g' _ => ⟨φ.symm g', φ.apply_symm_apply g'⟩

@[expose] noncomputable def restrict (D : HoltData G Ω) {K : Subgroup G}
    (hK : jHull G Ω ≤ K) : HoltData K Ω :=
  D.comap (f := K.subtype) (e := Equiv.refl Ω) K.subtype_injective (fun _ _ => rfl)
    fun g hg => ⟨⟨g, hK (mem_jHull_of_mem_longInv hg)⟩, rfl⟩

@[expose] noncomputable def ofRestrict {K : Subgroup G} (D : HoltData K Ω)
    (hK : jHull G Ω ≤ K) : HoltData G Ω :=
  D.map (f := K.subtype) (e := Equiv.refl Ω) K.subtype_injective (fun _ _ => rfl)
    fun g hg => ⟨⟨g, hK (mem_jHull_of_mem_longInv hg)⟩, rfl⟩

section Fields

variable (hf : Function.Injective f) (he : ∀ (g : G) (ω : Ω), e (g • ω) = f g • e ω)
  (hJ : longInv G' Ω' ⊆ f.range)

@[simp] theorem map_M (D : HoltData G Ω) (i : D.ι) : (D.map hf he hJ).M i = D.M i :=
  D.transport_M _ _ _ i

theorem map_coord_apply (D : HoltData G Ω) (ω : Ω) : (D.map hf he hJ).coord (e ω) = D.coord ω :=
  D.transport_coord_apply _ _ _ ω

@[simp] theorem comap_M (D' : HoltData G' Ω') (i : D'.ι) : (D'.comap hf he hJ).M i = D'.M i :=
  D'.transport_M _ _ _ i

end Fields

@[simp] theorem congr_M (D : HoltData G Ω) (φ : G ≃* G') (e : Ω ≃ Ω')
    (he : ∀ (g : G) (ω : Ω), e (g • ω) = φ g • e ω) (i : D.ι) : (D.congr φ e he).M i = D.M i :=
  D.map_M (f := φ.toMonoidHom) φ.injective he _ i

theorem congr_coord_apply (D : HoltData G Ω) (φ : G ≃* G') (e : Ω ≃ Ω')
    (he : ∀ (g : G) (ω : Ω), e (g • ω) = φ g • e ω) (ω : Ω) :
    (D.congr φ e he).coord (e ω) = D.coord ω :=
  D.map_coord_apply (f := φ.toMonoidHom) φ.injective he _ ω

variable {K : Subgroup G} (hK : jHull G Ω ≤ K)

@[simp] theorem restrict_M (D : HoltData G Ω) (i : D.ι) : (D.restrict hK).M i = D.M i :=
  D.comap_M (f := K.subtype) (e := Equiv.refl Ω) K.subtype_injective (fun _ _ => rfl) _ i

@[simp] theorem ofRestrict_M (D : HoltData K Ω) (i : D.ι) : (D.ofRestrict hK).M i = D.M i :=
  D.map_M (f := K.subtype) (e := Equiv.refl Ω) K.subtype_injective (fun _ _ => rfl) _ i

end HoltData

theorem holtStructure_iff_of_jHull_le {K : Subgroup G} (hK : jHull G Ω ≤ K) :
    HoltStructure G Ω ↔ HoltStructure K Ω :=
  ⟨fun ⟨D⟩ => ⟨D.restrict hK⟩, fun ⟨D⟩ => ⟨D.ofRestrict hK⟩⟩

theorem holtStructure_iff_jHull : HoltStructure G Ω ↔ HoltStructure (jHull G Ω) Ω :=
  holtStructure_iff_of_jHull_le le_rfl

end CFSG.Holt.H78
