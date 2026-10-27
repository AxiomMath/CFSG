module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped commutatorElement

variable {A G : Type} [Group A] [Group G]

private lemma conj_map_eq (f : A →* G) (k c : A) :
    f (k * c * k⁻¹) = f k * f c * (f k)⁻¹ := by
  simp only [map_mul, map_inv]

theorem map_Gx_of_injective {f : A →* G} (hf : Function.Injective f) (c : A) :
    (Gx c).map f = Gx (f c) ⊓ f.range := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨mem_Gx.mpr ?_, ⟨k, rfl⟩⟩
    rw [← map_mul, ← map_mul, mem_Gx.mp hk]
  · rintro ⟨hx1, hx2⟩
    obtain ⟨k, rfl⟩ := hx2
    refine Subgroup.mem_map.mpr ⟨k, mem_Gx.mpr (hf ?_), rfl⟩
    rw [map_mul, map_mul]
    exact mem_Gx.mp hx1

theorem map_inf_Gx_of_injective {f : A →* G} (hf : Function.Injective f) (K : Subgroup A) (c : A) :
    K.map f ⊓ Gx (f c) = (K ⊓ Gx c).map f := by
  ext x
  constructor
  · rintro ⟨hxK, hxc⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hxK
    refine Subgroup.mem_map.mpr ⟨k, ⟨hk, mem_Gx.mpr (hf ?_)⟩, rfl⟩
    rw [map_mul, map_mul]
    exact mem_Gx.mp hxc
  · rintro ⟨k, ⟨hkK, hkc⟩, rfl⟩
    refine ⟨Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩, mem_Gx.mpr ?_⟩
    rw [← map_mul, ← map_mul, mem_Gx.mp hkc]

theorem isConjOrbit_map_iff {f : A →* G} (hf : Function.Injective f) (K : Subgroup A) (S : Set A) :
    IsConjOrbit (K.map f) (f '' S) ↔ IsConjOrbit K S := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro k hk c hc
      obtain ⟨c', hc', hc'eq⟩ :=
        h.conj_mem (f k) (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩) (f c) ⟨c, hc, rfl⟩
      have hEq : f (k * c * k⁻¹) = f c' := (conj_map_eq f k c).trans hc'eq.symm
      rw [hf hEq]
      exact hc'
    · obtain ⟨x, hx⟩ := h.nonempty
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨c, hc⟩
    · intro c hc c' hc'
      obtain ⟨k, hk, hk_eq⟩ :=
        h.transitive (f c) ⟨c, hc, rfl⟩ (f c') ⟨c', hc', rfl⟩
      obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hk
      exact ⟨k₀, hk₀, hf ((conj_map_eq f k₀ c).trans hk_eq)⟩
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro k hk c hc
      obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hk
      obtain ⟨c₀, hc₀, rfl⟩ := hc
      exact ⟨k₀ * c₀ * k₀⁻¹, h.conj_mem k₀ hk₀ c₀ hc₀, conj_map_eq f k₀ c₀⟩
    · obtain ⟨c, hc⟩ := h.nonempty
      exact ⟨f c, ⟨c, hc, rfl⟩⟩
    · intro c hc c' hc'
      obtain ⟨c₀, hc₀, rfl⟩ := hc
      obtain ⟨c₀', hc₀', rfl⟩ := hc'
      obtain ⟨k₀, hk₀, hk_eq⟩ := h.transitive c₀ hc₀ c₀' hc₀'
      exact ⟨f k₀, Subgroup.mem_map.mpr ⟨k₀, hk₀, rfl⟩, by rw [← conj_map_eq, hk_eq]⟩

theorem isOrbitPartition_map_iff {ι : Type} {f : A →* G} (hf : Function.Injective f) (K : Subgroup A)
    (S : Set A) (P : ι → Set A) :
    IsOrbitPartition (K.map f) (f '' S) (fun i => f '' P i) ↔ IsOrbitPartition K S P := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i c hc
      have hmem : f c ∈ f '' S := h.subset i ⟨c, hc, rfl⟩
      obtain ⟨c', hc', heq⟩ := hmem
      rw [← hf heq]
      exact hc'
    · intro c hc
      obtain ⟨i, hi⟩ := h.cover (f c) ⟨c, hc, rfl⟩
      obtain ⟨c', hc', heq⟩ := hi
      exact ⟨i, by rwa [hf heq] at hc'⟩
    · intro i j hij
      rw [← Set.disjoint_image_iff hf]
      exact h.disjoint i j hij
    · intro i
      exact (isConjOrbit_map_iff hf K (P i)).mp (h.orbit i)
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      exact Set.image_mono (h.subset i)
    · rintro c ⟨c₀, hc₀, rfl⟩
      obtain ⟨i, hi⟩ := h.cover c₀ hc₀
      exact ⟨i, ⟨c₀, hi, rfl⟩⟩
    · intro i j hij
      rw [Set.disjoint_image_iff hf]
      exact h.disjoint i j hij
    · intro i
      exact (isConjOrbit_map_iff hf K (P i)).mpr (h.orbit i)

theorem stabCard_map_iff {ι : Type} {f : A →* G} (hf : Function.Injective f) (K : Subgroup A)
    (P : ι → Set A) (n : ι → ℕ) :
    StabCard (K.map f) (fun i => f '' P i) n ↔ StabCard K P n := by
  constructor
  · intro h i c hc
    have h1 := h i (f c) ⟨c, hc, rfl⟩
    rw [map_inf_Gx_of_injective hf K c, Subgroup.card_map_of_injective hf] at h1
    exact h1
  · intro h i c hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    have h1 := h i c₀ hc₀
    rw [map_inf_Gx_of_injective hf K c₀, Subgroup.card_map_of_injective hf]
    exact h1

theorem derivedOf_map_of_injective {f : A →* G} (hf : Function.Injective f) (K : Subgroup A) :
    derivedOf (K.map f) = (derivedOf K).map f := by
  simp only [derivedOf, Subgroup.map_subtype_commutator]
  rw [Subgroup.map_commutator]

theorem pCoreOf_map_of_injective {f : A →* G} (hf : Function.Injective f) (K : Subgroup A) :
    CFSG.Open.pCoreOf 2 (K.map f) = (CFSG.Open.pCoreOf 2 K).map f := by
  let e : ↥K ≃* ↥(K.map f) := Subgroup.equivMapOfInjective K f hf
  have hcomp : (K.map f).subtype.comp e.toMonoidHom = f.comp K.subtype := by
    ext x
    rfl
  simp only [CFSG.Open.pCoreOf]
  rw [← CFSG.pCore_map_iso 2 e, Subgroup.map_map, hcomp, ← Subgroup.map_map]

theorem centerOf_map_of_injective {f : A →* G} (hf : Function.Injective f) (K : Subgroup A) :
    centerOf (K.map f) = (centerOf K).map f := by
  ext x
  constructor
  · intro hx
    simp only [centerOf, Subgroup.mem_inf] at hx
    obtain ⟨hxK, hxC⟩ := hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hxK
    refine Subgroup.mem_map.mpr ⟨k, ?_, rfl⟩
    simp only [centerOf, Subgroup.mem_inf]
    refine ⟨hk, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := (Subgroup.mem_centralizer_iff.mp hxC) (f y)
      (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
    rw [← map_mul, ← map_mul] at h1
    exact hf h1
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    simp only [centerOf, Subgroup.mem_inf] at hk
    obtain ⟨hkK, hkC⟩ := hk
    simp only [centerOf, Subgroup.mem_inf]
    refine ⟨Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    have h1 := (Subgroup.mem_centralizer_iff.mp hkC) y₀ hy₀
    rw [← map_mul, ← map_mul, h1]

theorem conj_mem_derivedOf_of_mem_normalizer {L : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ derivedOf L) :
    c * t * c⁻¹ ∈ derivedOf L := by
  have hmap : L.map (MulAut.conj c) = L := (Subgroup.mem_normalizer_iff_map_conj_eq).mp hc
  simp only [derivedOf, Subgroup.map_subtype_commutator] at ht ⊢
  have hfix : (⁅L, L⁆).map (MulAut.conj c) = ⁅L, L⁆ := by
    rw [Subgroup.map_commutator, hmap]
  have : MulAut.conj c t ∈ ⁅L, L⁆ := by
    rw [← hfix]
    exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
  rwa [MulAut.conj_apply] at this

theorem Gxy_comm (x y : G) : Gxy x y = Gxy y x := by
  show Subgroup.centralizer ({x, y} : Set G) = Subgroup.centralizer ({y, x} : Set G)
  rw [Set.pair_comm x y]

theorem Gxy_eq_map_subtype {b : G} (y : ↥(Gx b)) :
    Gxy (y : G) b = (Gx y).map (Gx b).subtype := by
  have h := map_Gx_of_injective (f := (Gx b).subtype) (Subgroup.subtype_injective (Gx b)) y
  rw [Subgroup.range_subtype, Subgroup.subtype_apply] at h
  rw [Gxy_eq_inf, ← h]

theorem Gxyz_eq_map_subtype {b : G} (y c : ↥(Gx b)) :
    Gxyz (y : G) b (c : G) = (Gx y ⊓ Gx c).map (Gx b).subtype := by
  rw [Gxyz_eq_inf, Gxy_eq_map_subtype y]
  exact map_inf_Gx_of_injective (f := (Gx b).subtype) (Subgroup.subtype_injective (Gx b))
    (Gx y) c

theorem nonempty_mulEquiv_Gxy_subtype {b : G} (y : ↥(Gx b)) :
    Nonempty (↥(Gxy (y : G) b) ≃* ↥(Gx y)) :=
  ⟨(MulEquiv.subgroupCongr (Gxy_eq_map_subtype y)).trans
    (Subgroup.equivMapOfInjective (Gx y) (Gx b).subtype
      (Subgroup.subtype_injective (Gx b))).symm⟩

theorem nonempty_mulEquiv_Gxyz_subtype {b : G} (y c : ↥(Gx b)) :
    Nonempty (↥(Gxyz (y : G) b (c : G)) ≃* ↥(Gx y ⊓ Gx c)) :=
  ⟨(MulEquiv.subgroupCongr (Gxyz_eq_map_subtype y c)).trans
    (Subgroup.equivMapOfInjective (Gx y ⊓ Gx c) (Gx b).subtype
      (Subgroup.subtype_injective (Gx b))).symm⟩

theorem exists_mulEquiv_derivedOf_Gxy_subtype {b : G} (y : ↥(Gx b))
    (φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gx y))) :
    ∃ ψ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy b (y : G))), ∀ t,
      ((ψ t : ↥(derivedOf (Gxy b (y : G)))) : G) =
        (((φ t : ↥(derivedOf (Gx y))) : ↥(Gx b)) : G) := by
  have hEq : (derivedOf (Gx y)).map (Gx b).subtype = derivedOf (Gxy b (y : G)) := by
    rw [← Gxy_comm (y : G) b, Gxy_eq_map_subtype y,
      derivedOf_map_of_injective (Subgroup.subtype_injective (Gx b))]
  refine ⟨φ.trans (((derivedOf (Gx y)).equivMapOfInjective (Gx b).subtype
    (Subgroup.subtype_injective (Gx b))).trans (MulEquiv.subgroupCongr hEq)), ?_⟩
  intro t
  rfl

end CFSG.EvenSporadicStandard.HNRecog.Section3
