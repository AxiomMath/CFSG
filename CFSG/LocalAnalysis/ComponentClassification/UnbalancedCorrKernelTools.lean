module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSimpleQuotient
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def pLayerCoreActionKernel (Y : Type*) [Group Y] : Subgroup Y :=
  UnbalancedLayer.coreActionKernel (pLayer Y 2)

instance pLayerCoreActionKernel_normal (Y : Type*) [Group Y] [Finite Y] :
    (pLayerCoreActionKernel Y).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEn : (pLayer Y 2).Normal := by
    have : (pLayer Y 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    infer_instance
  have hON : ∀ y : Y, y ∈ normalizer
      (((pPrimeCore 2 ↥(pLayer Y 2)).map (pLayer Y 2).subtype : Subgroup Y) : Set Y) := by
    intro y
    apply UnbalancedGS.normalizer_le_normalizer_map_of_characteristic (pLayer Y 2)
      (pPrimeCore 2 ↥(pLayer Y 2))
    rw [normalizer_eq_top_iff.mpr hEn]
    exact mem_top y
  refine ⟨fun g hg y => ?_⟩
  obtain ⟨-, hgE⟩ := UnbalancedLayer.mem_coreActionKernel.mp hg
  refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨?_, fun e he => ?_⟩
  · rw [normalizer_eq_top_iff.mpr hEn]
    exact mem_top _
  · have he' : y⁻¹ * e * y ∈ pLayer Y 2 := by
      have := hEn.conj_mem e he y⁻¹
      rwa [inv_inv] at this
    have h1 := hgE _ he'
    have h2 := (mem_normalizer_iff.mp (hON y) _).mp h1
    rwa [show y * ((y⁻¹ * e * y)⁻¹ * g⁻¹ * (y⁻¹ * e * y) * g) * y⁻¹ =
      e⁻¹ * (y * g * y⁻¹)⁻¹ * e * (y * g * y⁻¹) by group] at h2

omit [Finite G] in
theorem mem_center_of_commutator_mem_center {Y : Type*} [Group Y] [Group.IsPerfect Y] {x : Y}
    (h : ∀ y : Y, x⁻¹ * y⁻¹ * x * y ∈ center Y) : x ∈ center Y := by
  let f : Y →* Y := (MulAut.conj x⁻¹).toMonoidHom
  have hfy : ∀ y : Y, f y = x⁻¹ * y * x⁻¹⁻¹ := fun y => rfl
  have hf : ∀ y : Y, y⁻¹ * f y ∈ center Y := by
    intro y
    have h1 := inv_mem (h y)
    rw [hfy, inv_inv]
    rwa [show (x⁻¹ * y⁻¹ * x * y)⁻¹ = y⁻¹ * (x⁻¹ * y * x) by group] at h1
  have hid := PerfectAutomorphisms.hom_eq_id_of_central_displacement f hf
  rw [mem_center_iff]
  intro y
  have h2 : f y = y := by rw [hid]; rfl
  rw [hfy] at h2
  calc y * x = x * (x⁻¹ * y * x⁻¹⁻¹) := by group
    _ = x * y := by rw [h2]

omit [Finite G] in
theorem mem_fusionZStar_of_commutator_mem {Y : Type*} [Group Y] [Group.IsPerfect Y] {x : Y}
    (h : ∀ y : Y, x⁻¹ * y⁻¹ * x * y ∈ CFSG.Open.fusionZStar Y) :
    x ∈ CFSG.Open.fusionZStar Y := by
  set O := CFSG.Open.fusionOddCore Y
  have : Group.IsPerfect (Y ⧸ O) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  show QuotientGroup.mk' O x ∈ center (Y ⧸ O)
  apply mem_center_of_commutator_mem_center
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O q
  have h1 : QuotientGroup.mk' O (x⁻¹ * y⁻¹ * x * y) ∈ center (Y ⧸ O) := h y
  simpa only [map_mul, map_inv] using h1

omit [Finite G] in
theorem mem_coreActionKernel_of_zstar {V : Subgroup G} (hV : ⁅V, V⁆ = V) {g : G}
    (hg : g ∈ normalizer (V : Set G))
    (hz : ∀ v ∈ V, v⁻¹ * g⁻¹ * v * g ∈ (CFSG.Open.fusionZStar ↥V).map V.subtype) :
    g ∈ UnbalancedLayer.coreActionKernel V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥V := Subgroup.isPerfect_iff.mpr hV
  refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨hg, fun v hv => ?_⟩
  let φ : MulAut ↥V := V.normalizerMonoidHom ⟨g⁻¹, inv_mem hg⟩
  have hφ : ∀ u : V, ((φ u : V) : G) = g⁻¹ * u * g := fun u => by
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  set O := CFSG.Open.fusionOddCore ↥V with hOdef
  have hOeq : O = pPrimeCore 2 ↥V := UnbalancingLocal.fusionOddCore_eq_pPrimeCore ↥V
  have hOφ : O.map φ.toMonoidHom = O := by
    rw [hOeq]
    exact pPrimeCore_map_iso 2 φ
  let σ : (↥V ⧸ O) ≃* (↥V ⧸ O) := QuotientGroup.congr O O φ hOφ
  have hσ : ∀ u : V, σ (u : ↥V ⧸ O) = ((φ u : V) : ↥V ⧸ O) := fun u =>
    QuotientGroup.congr_mk _ _ _ _ u
  have : Group.IsPerfect (↥V ⧸ O) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  have hcen : ∀ q : ↥V ⧸ O, q⁻¹ * σ.toMonoidHom q ∈ center (↥V ⧸ O) := by
    intro q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective O q
    have h1 : (u : G)⁻¹ * g⁻¹ * u * g ∈ (CFSG.Open.fusionZStar ↥V).map V.subtype := hz u u.2
    obtain ⟨w, hw, hwu⟩ := mem_map.mp h1
    have hw' : w = u⁻¹ * φ u := Subtype.ext (by
      rw [show ((w : V) : G) = V.subtype w from rfl, hwu, coe_mul, coe_inv, hφ]
      group)
    rw [hw'] at hw
    have h2 : QuotientGroup.mk' O (u⁻¹ * φ u) ∈ center (↥V ⧸ O) := hw
    rw [map_mul, map_inv] at h2
    show (QuotientGroup.mk' O u)⁻¹ * σ (QuotientGroup.mk' O u) ∈ center (↥V ⧸ O)
    rw [QuotientGroup.mk'_apply, hσ]
    exact h2
  have hid := PerfectAutomorphisms.hom_eq_id_of_central_displacement σ.toMonoidHom hcen
  have h3 : σ ((⟨v, hv⟩ : V) : ↥V ⧸ O) = ((⟨v, hv⟩ : V) : ↥V ⧸ O) := by
    have := DFunLike.congr_fun hid ((⟨v, hv⟩ : V) : ↥V ⧸ O)
    exact this
  rw [hσ] at h3
  have h4 : (⟨v, hv⟩ : V)⁻¹ * φ ⟨v, hv⟩ ∈ O := QuotientGroup.eq.mp h3.symm
  rw [hOeq] at h4
  refine ⟨_, h4, ?_⟩
  rw [coe_subtype, coe_mul, coe_inv, hφ]
  group

theorem quotient_commute_iff {Y : Type*} [Group Y] {N : Subgroup Y} [N.Normal] (v h : Y) :
    QuotientGroup.mk' N v * QuotientGroup.mk' N h = QuotientGroup.mk' N h * QuotientGroup.mk' N v ↔
      v⁻¹ * h⁻¹ * v * h ∈ N := by
  set θ := QuotientGroup.mk' N
  constructor
  · intro h1
    have h2 : θ (v⁻¹ * h⁻¹ * v * h) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc (θ v)⁻¹ * (θ h)⁻¹ * θ v * θ h = (θ v)⁻¹ * (θ h)⁻¹ * (θ v * θ h) := by group
        _ = 1 := by rw [h1]; group
    exact (QuotientGroup.eq_one_iff _).mp h2
  · intro h1
    have h2 : θ (v⁻¹ * h⁻¹ * v * h) = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc θ v * θ h = θ h * θ v * ((θ v)⁻¹ * (θ h)⁻¹ * θ v * θ h) := by group
      _ = θ h * θ v := by rw [h2, mul_one]

omit [Finite G] in
theorem mem_centralizer_map_iff {Y V : Subgroup G} {N : Subgroup ↥Y} [N.Normal] (hVY : V ≤ Y)
    (hYV : Y ≤ normalizer (V : Set G)) (hV : ⁅V, V⁆ = V)
    (hON : (pPrimeCore 2 ↥V).map V.subtype ≤ N.map Y.subtype)
    (hVN : V ⊓ N.map Y.subtype = (CFSG.Open.fusionZStar ↥V).map V.subtype) (h : Y) :
    QuotientGroup.mk' N h ∈ centralizer (((V.subgroupOf Y).map (QuotientGroup.mk' N) :
      Subgroup (↥Y ⧸ N)) : Set (↥Y ⧸ N)) ↔ (h : G) ∈ UnbalancedLayer.coreActionKernel V := by
  constructor
  · intro hc
    apply mem_coreActionKernel_of_zstar hV (hYV h.2)
    intro v hv
    have h1 : QuotientGroup.mk' N ⟨v, hVY hv⟩ ∈ (V.subgroupOf Y).map (QuotientGroup.mk' N) :=
      mem_map_of_mem _ (show (⟨v, hVY hv⟩ : Y) ∈ V.subgroupOf Y from hv)
    have h2 := (quotient_commute_iff (N := N) ⟨v, hVY hv⟩ h).mp ((mem_centralizer_iff.mp hc) _ h1)
    have h4 : v⁻¹ * (h : G)⁻¹ * v * h ∈ V ⊓ N.map Y.subtype := by
      refine mem_inf.mpr ⟨?_, ⟨_, h2, rfl⟩⟩
      have h5 := (mem_normalizer_iff.mp (inv_mem (hYV h.2)) v).mp hv
      rw [inv_inv] at h5
      rw [show v⁻¹ * (h : G)⁻¹ * v * h = v⁻¹ * ((h : G)⁻¹ * v * h) by group]
      exact mul_mem (inv_mem hv) h5
    rwa [hVN] at h4
  · intro hk
    obtain ⟨-, hkV⟩ := UnbalancedLayer.mem_coreActionKernel.mp hk
    rw [mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨n, hn, hnv⟩ := hON (hkV (v : G) hv)
    have hn' : n = v⁻¹ * h⁻¹ * v * h := Subtype.ext (by
      rw [show ((n : Y) : G) = Y.subtype n from rfl, hnv]
      simp)
    exact (quotient_commute_iff v h).mpr (hn' ▸ hn)

omit [Finite G] in
theorem map_inf_centralizer_eq_bot {Y V : Subgroup G} {N : Subgroup ↥Y} [N.Normal]
    (hVY : V ≤ Y) (hV : ⁅V, V⁆ = V)
    (hVN : V ⊓ N.map Y.subtype = (CFSG.Open.fusionZStar ↥V).map V.subtype) :
    (V.subgroupOf Y).map (QuotientGroup.mk' N) ⊓ centralizer (((V.subgroupOf Y).map
      (QuotientGroup.mk' N) : Subgroup (↥Y ⧸ N)) : Set (↥Y ⧸ N)) = ⊥ := by
  have : Group.IsPerfect ↥V := Subgroup.isPerfect_iff.mpr hV
  rw [eq_bot_iff]
  rintro _ ⟨⟨v, hv, rfl⟩, hc⟩
  rw [mem_bot]
  have hvZ : (⟨v, hv⟩ : V) ∈ CFSG.Open.fusionZStar ↥V := by
    apply mem_fusionZStar_of_commutator_mem
    intro u
    have h1 : QuotientGroup.mk' N ⟨u, hVY u.2⟩ ∈ (V.subgroupOf Y).map (QuotientGroup.mk' N) :=
      mem_map_of_mem _ (show (⟨u, hVY u.2⟩ : Y) ∈ V.subgroupOf Y from u.2)
    have h2 := (mem_centralizer_iff.mp hc) _ h1
    have h3 := (quotient_commute_iff (N := N) v ⟨u, hVY u.2⟩).mp h2.symm
    have h4 : (v : G)⁻¹ * (u : G)⁻¹ * v * u ∈ V ⊓ N.map Y.subtype :=
      mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem (inv_mem hv) (inv_mem u.2)) hv) u.2, ⟨_, h3, rfl⟩⟩
    rw [hVN] at h4
    obtain ⟨w, hw, hwu⟩ := h4
    have hw' : w = (⟨v, hv⟩ : V)⁻¹ * u⁻¹ * ⟨v, hv⟩ * u := Subtype.ext (by
      rw [show ((w : V) : G) = V.subtype w from rfl, hwu]
      simp)
    rwa [hw'] at hw
  have hvN : (v : G) ∈ V ⊓ N.map Y.subtype := by
    rw [hVN]
    exact ⟨⟨v, hv⟩, hvZ, rfl⟩
  obtain ⟨n, hn, hnv⟩ := (mem_inf.mp hvN).2
  have hn' : n = v := Subtype.ext hnv
  rw [← hn']
  exact (QuotientGroup.eq_one_iff _).mpr hn

end CFSG.ComponentClassification.UnbalancedCorr
