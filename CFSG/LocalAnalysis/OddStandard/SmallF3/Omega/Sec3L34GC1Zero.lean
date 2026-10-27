module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Img
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Pg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTOdd

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {E : Subgroup G} {x : G}

private theorem l34g_commutator_central {E : Subgroup G} {x e : G}
    (hxN : x ∈ normalizer (E : Set G)) (heN : e ∈ normalizer (E : Set G))
    (h : E.normalizerMonoidHom ⟨e, heN⟩ * E.normalizerMonoidHom ⟨x, hxN⟩ =
      E.normalizerMonoidHom ⟨x, hxN⟩ * E.normalizerMonoidHom ⟨e, heN⟩) :
    ∀ g ∈ E, g * (x * e * x⁻¹ * e⁻¹) = (x * e * x⁻¹ * e⁻¹) * g := by
  intro g hg
  set a : ↥(normalizer (E : Set G)) := ⟨e, heN⟩
  set b : ↥(normalizer (E : Set G)) := ⟨x, hxN⟩
  have h1 : E.normalizerMonoidHom (a * b) = E.normalizerMonoidHom (b * a) := by
    simpa only [a, b, map_mul] using h
  have h3 : E.normalizerMonoidHom (a * b * (b * a)⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have h4 : E.normalizerMonoidHom (b * a * b⁻¹ * a⁻¹) = 1 := by
    have hEq : b * a * b⁻¹ * a⁻¹ = (a * b * (b * a)⁻¹)⁻¹ := by group
    rw [hEq, map_inv, h3, inv_one]
  have hwN : x * e * x⁻¹ * e⁻¹ ∈ normalizer (E : Set G) :=
    mul_mem (mul_mem (mul_mem hxN heN) (inv_mem hxN)) (inv_mem heN)
  have hw : E.normalizerMonoidHom ⟨x * e * x⁻¹ * e⁻¹, hwN⟩ = 1 := by
    have harg : (⟨x * e * x⁻¹ * e⁻¹, hwN⟩ : ↥(normalizer (E : Set G))) =
        b * a * b⁻¹ * a⁻¹ := Subtype.ext rfl
    rw [harg]
    exact h4
  exact ((l34gAct_eq_one_iff hwN).mp hw g hg).symm

theorem l34g_c0_le (hxN : x ∈ normalizer (E : Set G)) :
    l34gImg E (E ⊓ centralizer ({x} : Set G)) ≤
      l34gImg E E ⊓ centralizer ({E.normalizerMonoidHom ⟨x, hxN⟩} : Set (MulAut ↥E)) := by
  intro c hc
  obtain ⟨g, hgN, hgC, hgc⟩ := mem_l34gImg.mp hc
  have hgE : g ∈ E := hgC.1
  have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hgC.2
  refine ⟨?_, ?_⟩
  · exact mem_l34gImg.mpr ⟨g, hgN, hgE, hgc⟩
  · have h1 : E.normalizerMonoidHom (⟨g, hgN⟩ * ⟨x, hxN⟩) =
        E.normalizerMonoidHom (⟨x, hxN⟩ * ⟨g, hgN⟩) := by
      have hgx' : (⟨g, hgN⟩ * ⟨x, hxN⟩ : ↥(normalizer (E : Set G))) =
          ⟨x, hxN⟩ * ⟨g, hgN⟩ := by
        apply Subtype.ext
        simpa using hgx
      rw [hgx']
    have hcomm : E.normalizerMonoidHom ⟨g, hgN⟩ * E.normalizerMonoidHom ⟨x, hxN⟩ =
        E.normalizerMonoidHom ⟨x, hxN⟩ * E.normalizerMonoidHom ⟨g, hgN⟩ := by
      simpa only [map_mul] using h1
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← hgc]; exact hcomm)

theorem l34g_c0_normal (hxN : x ∈ normalizer (E : Set G)) :
    ∀ f ∈ l34gImg E E ⊓ centralizer ({E.normalizerMonoidHom ⟨x, hxN⟩} : Set (MulAut ↥E)),
      ∀ c ∈ l34gImg E (E ⊓ centralizer ({x} : Set G)),
        f * c * f⁻¹ ∈ l34gImg E (E ⊓ centralizer ({x} : Set G)) := by
  intro f hf c hc
  obtain ⟨hfE, hfcomm⟩ := hf
  obtain ⟨e, heN, heE, hfe⟩ := mem_l34gImg.mp hfE
  obtain ⟨c0, hc0N, hc0C, hc0eq⟩ := mem_l34gImg.mp hc
  have hc0E : c0 ∈ E := hc0C.1
  have hc0x : c0 * x = x * c0 := Subgroup.mem_centralizer_singleton_iff.mp hc0C.2
  have hfx : E.normalizerMonoidHom ⟨e, heN⟩ * E.normalizerMonoidHom ⟨x, hxN⟩ =
      E.normalizerMonoidHom ⟨x, hxN⟩ * E.normalizerMonoidHom ⟨e, heN⟩ := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hfcomm
    rwa [← hfe] at h
  have hcent := l34g_commutator_central hxN heN hfx
  have hxexE : x * e * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hxN e).mp heE
  have hECE : e * c0 * e⁻¹ ∈ E := E.mul_mem (E.mul_mem heE hc0E) (E.inv_mem heE)
  have hxce : x * c0 * x⁻¹ = c0 := by
    rw [← hc0x]; group
  have hcalc : x * (e * c0 * e⁻¹) * x⁻¹ = e * c0 * e⁻¹ := by
    have hxex : x * e * x⁻¹ = (x * e * x⁻¹ * e⁻¹) * e := by group
    have hxe' : x * e⁻¹ * x⁻¹ = e⁻¹ * (x * e * x⁻¹ * e⁻¹)⁻¹ := by group
    have hwcen := hcent (e * c0 * e⁻¹) hECE
    calc x * (e * c0 * e⁻¹) * x⁻¹
        = (x * e * x⁻¹) * (x * c0 * x⁻¹) * (x * e⁻¹ * x⁻¹) := by group
      _ = (x * e * x⁻¹ * e⁻¹) * (e * c0 * e⁻¹) * (x * e * x⁻¹ * e⁻¹)⁻¹ := by
            rw [hxex, hxce, hxe']
            group
      _ = (e * c0 * e⁻¹) * (x * e * x⁻¹ * e⁻¹) *
            (x * e * x⁻¹ * e⁻¹)⁻¹ := by rw [← hwcen]
      _ = e * c0 * e⁻¹ := by group
  have hEx : e * c0 * e⁻¹ ∈ centralizer ({x} : Set G) := by
    have h := congrArg (fun t => t * x) hcalc
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc (e * c0 * e⁻¹) * x
          = (x * (e * c0 * e⁻¹) * x⁻¹) * x := h.symm
        _ = x * (e * c0 * e⁻¹) := by group)
  refine mem_l34gImg.mpr ⟨e * c0 * e⁻¹, E.le_normalizer hECE, ⟨hECE, hEx⟩, ?_⟩
  have hsub : (⟨e * c0 * e⁻¹, E.le_normalizer hECE⟩ : ↥(normalizer (E : Set G))) =
      ⟨e, heN⟩ * ⟨c0, hc0N⟩ * (⟨e, heN⟩)⁻¹ := Subtype.ext (by simp)
  have hmap : E.normalizerMonoidHom ⟨e * c0 * e⁻¹, E.le_normalizer hECE⟩ =
      E.normalizerMonoidHom ⟨e, heN⟩ * E.normalizerMonoidHom ⟨c0, hc0N⟩ *
        (E.normalizerMonoidHom ⟨e, heN⟩)⁻¹ := by
    rw [hsub, map_mul, map_mul, map_inv]
  rw [hmap, hfe, hc0eq]

theorem l34g_c0_odd [Finite G] (hx : x * x = 1) (hxN : x ∈ normalizer (E : Set G)) :
    ∀ f ∈ l34gImg E E ⊓ centralizer ({E.normalizerMonoidHom ⟨x, hxN⟩} : Set (MulAut ↥E)),
      Odd (orderOf f) → f ∈ l34gImg E (E ⊓ centralizer ({x} : Set G)) := by
  classical
  intro f hf hodd
  obtain ⟨hfE, hfcomm⟩ := hf
  let φ : ↥E →* ↥(l34gImg E E) :=
    (E.normalizerMonoidHom.comp
      (Subgroup.inclusion (le_normalizer : E ≤ normalizer (E : Set G)))).codRestrict
      (l34gImg E E) fun e =>
        mem_l34gImg.mpr ⟨(e : G), E.le_normalizer e.2, e.2, rfl⟩
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨g, hgN, hgE, hgy⟩ := mem_l34gImg.mp y.2
    refine ⟨⟨g, hgE⟩, ?_⟩
    apply Subtype.ext
    have h1 : (φ ⟨g, hgE⟩).1 =
        E.normalizerMonoidHom ⟨g, E.le_normalizer hgE⟩ := rfl
    rw [h1]
    have h2 : E.normalizerMonoidHom ⟨g, E.le_normalizer hgE⟩ =
        E.normalizerMonoidHom ⟨g, hgN⟩ := by
      have h2sub : (⟨g, E.le_normalizer hgE⟩ : ↥(normalizer (E : Set G))) = ⟨g, hgN⟩ :=
        Subtype.ext rfl
      exact congrArg E.normalizerMonoidHom h2sub
    rw [h2, hgy]
  have hodd_f' : Odd (orderOf (⟨f, hfE⟩ : ↥(l34gImg E E))) := by
    rw [← Subgroup.orderOf_coe (⟨f, hfE⟩ : ↥(l34gImg E E))]
    simpa using hodd
  obtain ⟨e, hφe, hodd_e⟩ := l34g_exists_odd_lift φ hφ hodd_f'
  have hfe : E.normalizerMonoidHom ⟨(e : G), E.le_normalizer e.2⟩ = f := by
    have hval : (φ e).1 = f := by rw [hφe]
    exact hval
  have hfx : E.normalizerMonoidHom ⟨(e : G), E.le_normalizer e.2⟩ *
      E.normalizerMonoidHom ⟨x, hxN⟩ =
      E.normalizerMonoidHom ⟨x, hxN⟩ *
        E.normalizerMonoidHom ⟨(e : G), E.le_normalizer e.2⟩ := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hfcomm
    rwa [← hfe] at h
  have hcent := l34g_commutator_central hxN (E.le_normalizer e.2) hfx
  have hodd_eG : Odd (orderOf (e : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hodd_e
  obtain ⟨z, hzE, hzcent, hzex⟩ :=
    l34g_odd_central_lift (e := (e : G)) hx hxN e.2 hodd_eG hcent
  have hzN : z ∈ normalizer (E : Set G) := E.le_normalizer hzE
  have hgzE : (e : G) * z ∈ E := E.mul_mem e.2 hzE
  have hgzN : (e : G) * z ∈ normalizer (E : Set G) := E.le_normalizer hgzE
  have hgzC : (e : G) * z ∈ E ⊓ centralizer ({x} : Set G) := by
    exact ⟨hgzE, Subgroup.mem_centralizer_singleton_iff.mpr hzex⟩
  have hz1 : E.normalizerMonoidHom ⟨z, hzN⟩ = 1 := by
    rw [l34gAct_eq_one_iff hzN]
    intro g' hg'
    exact (hzcent g' hg').symm
  refine mem_l34gImg.mpr ⟨(e : G) * z, hgzN, hgzC, ?_⟩
  have hsub : (⟨(e : G) * z, hgzN⟩ : ↥(normalizer (E : Set G))) =
      ⟨(e : G), E.le_normalizer e.2⟩ * ⟨z, hzN⟩ := Subtype.ext rfl
  have hmap : E.normalizerMonoidHom ⟨(e : G) * z, hgzN⟩ =
      E.normalizerMonoidHom ⟨(e : G), E.le_normalizer e.2⟩ *
        E.normalizerMonoidHom ⟨z, hzN⟩ := by
    rw [hsub, map_mul]
  rw [hmap, hfe, hz1, mul_one]

end CFSG.OddStandard.SmallF3.Omega
