module

public import CFSG.Dihedral.OriginalCosetNormalizer
public import CFSG.Dihedral.OriginalCosetSetup
public import CFSG.GroupTheory.CentralizerMap

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem opposite_reflection_image_outer (hp : d.PureProjectiveNormalizer)
    (hR : d.R ≠ ⊥) (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t)
    (i j : Fin 2) (hij : i ≠ j) (hi : Cycles d.N (d.V i)) :
    e (d.s * d.r ^ j.val) * a7a ≠ a7a * e (d.s * d.r ^ j.val) := by
  let u := d.s * d.r ^ j.val
  intro hcomm
  have hcent : e u ∈ Subgroup.centralizer (a7U : Set (alternatingGroup (Fin 7))) := by
    rw [a7U_eq_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have hRcent : d.R ≤ Subgroup.centralizer ({u} : Set G) := by
    intro r hr
    have hmap : e r ∈ a7U := by
      rw [← d.R_map_eq_a7U hR e ht]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simpa only [map_mul] using (Subgroup.mem_centralizer_iff.mp hcent) (e r) hmap
  have hfixed : d.R ⊓ Subgroup.centralizer ({u} : Set G) = d.commonE :=
    d.original_opposite_reflection_fixed hp i j hij hi
  rw [inf_eq_left.mpr hRcent, d.commonE_eq_bot_of_aSeven_model e] at hfixed
  exact hR hfixed

theorem opposite_reflection_centralizer_card (hp : d.PureProjectiveNormalizer)
    (hR : d.R ≠ ⊥) (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t)
    (i j : Fin 2) (hij : i ≠ j) (hi : Cycles d.N (d.V i)) :
    Nat.card (d.N ⊓ Subgroup.centralizer ({d.s * d.r ^ j.val} : Set G) : Subgroup G) = 4 := by
  let u := d.s * d.r ^ j.val
  have huN : e u ∈ a7ThreeNormalizer := by
    rw [← d.N_map_eq_a7ThreeNormalizer hR e ht]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (d.original_reflection_mem j)
  have hu2 : (e u) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one u
    rw [d.original_reflection_order j] at h
    simpa only [map_pow, map_one] using congrArg e h
  have hu1 : e u ≠ 1 := by
    intro h
    have hu : u = 1 := e.injective (by simpa using h)
    have ho := d.original_reflection_order j
    change orderOf u = 2 at ho
    simp [hu] at ho
  have hcard := a7ThreeNormalizer_centralizer_card (e u) huN hu2 hu1
  rw [ite_eq_right (d.opposite_reflection_image_outer hp hR e ht i j hij hi)] at hcard
  rw [← Subgroup.card_map_of_injective
    (K := d.N ⊓ Subgroup.centralizer ({u} : Set G)) (f := e.toMonoidHom) e.injective,
    CFSG.centralizer_inter_map, d.N_map_eq_a7ThreeNormalizer hR e ht]
  exact hcard

theorem involution_fusion_in_original_normalizer (hp : d.PureProjectiveNormalizer)
    (hR : d.R ≠ ⊥) (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t)
    (i j : Fin 2) (hij : i ≠ j) (hi : Cycles d.N (d.V i)) :
    ∀ x ∈ d.N, orderOf x = 2 →
      ∃ y ∈ d.N, y * x * y⁻¹ = d.t ∨ y * x * y⁻¹ = d.s * d.r ^ j.val := by
  let u := d.s * d.r ^ j.val
  have hmem (x : G) (hx : x ∈ d.N) : e x ∈ a7ThreeNormalizer := by
    rw [← d.N_map_eq_a7ThreeNormalizer hR e ht]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hx
  have hinv (x : G) (hx : orderOf x = 2) : (e x) ^ 2 = 1 ∧ e x ≠ 1 := by
    constructor
    · have h := pow_orderOf_eq_one x
      rw [hx] at h
      simpa only [map_pow, map_one] using congrArg e h
    · intro h
      have h1 : x = 1 := e.injective (by simpa using h)
      simp [h1] at hx
  have hu := hinv u (d.original_reflection_order j)
  intro x hx hx2
  have hxinv := hinv x hx2
  obtain ⟨g, hg, hrep⟩ := a7ThreeNormalizer_involution_fusion (e u)
    (hmem u (d.original_reflection_mem j)) hu.1 hu.2
    (d.opposite_reflection_image_outer hp hR e ht i j hij hi) (e x)
    (hmem x hx) hxinv.1 hxinv.2
  refine ⟨e.symm g, ?_, ?_⟩
  · have hmap : g ∈ d.N.map e.toMonoidHom := by
      rwa [d.N_map_eq_a7ThreeNormalizer hR e ht]
    exact Subgroup.mem_map_equiv.mp hmap
  · rcases hrep with h | h
    · left
      apply e.injective
      simpa only [map_mul, map_inv, e.apply_symm_apply, ht] using h
    · right
      change e.symm g * x * (e.symm g)⁻¹ = u
      apply e.injective
      simpa only [map_mul, map_inv, e.apply_symm_apply] using h

theorem original_normalizer_involution_classes_distinct (hp : d.PureProjectiveNormalizer)
    (hR : d.R ≠ ⊥) (e : G ≃* alternatingGroup (Fin 7))
    (i j : Fin 2) (hij : i ≠ j) (hi : Cycles d.N (d.V i)) :
    ¬ ∃ y ∈ d.N, y * d.t * y⁻¹ = d.s * d.r ^ j.val := by
  rintro ⟨y, hy, heq⟩
  let u := d.s * d.r ^ j.val
  have hRcent : d.R ≤ Subgroup.centralizer ({u} : Set G) := by
    intro r hr
    have hr' : y⁻¹ * r * y ∈ d.R := by
      have hnorm : y⁻¹ ∈ Subgroup.normalizer (d.R : Set G) := d.N.inv_mem hy
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hnorm r).mp hr
    have hrC : y⁻¹ * r * y ∈ Subgroup.centralizer ({d.t} : Set G) := by
      simpa only [d.centralizer, t] using d.R_le hr'
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hrC
    rw [Subgroup.mem_centralizer_singleton_iff]
    change r * (d.s * d.r ^ j.val) = (d.s * d.r ^ j.val) * r
    rw [← heq]
    calc
      r * (y * d.t * y⁻¹) = y * ((y⁻¹ * r * y) * d.t) * y⁻¹ := by group
      _ = y * (d.t * (y⁻¹ * r * y)) * y⁻¹ := by rw [hc]
      _ = (y * d.t * y⁻¹) * r := by group
  have hfixed := d.original_opposite_reflection_fixed hp i j hij hi
  rw [inf_eq_left.mpr hRcent, d.commonE_eq_bot_of_aSeven_model e] at hfixed
  exact hR hfixed

theorem original_normalizer_fixedCoset_card (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t) :
    Set.ncard {x : G ⧸ d.N | d.t • x = x} = 7 := by
  rw [CFSG.fixedCoset_card_congr e d.N a7ThreeNormalizer
    (d.N_map_eq_a7ThreeNormalizer hR e ht) d.t, ht, a7ThreeNormalizer_fixedCoset_card]

end CFSG.DihedralBlueprint.OriginalData
