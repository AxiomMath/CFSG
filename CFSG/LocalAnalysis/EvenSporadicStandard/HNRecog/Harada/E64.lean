module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {t z b z₁ : G} {S Eg T T' W0 : Subgroup G} {ι : Elem2 6 →* G}

private theorem isElemAbelian_range (hι : Function.Injective ι) :
    CFSG.Open.IsElemAbelian 2 (ι.range : Subgroup G) := by
  refine ⟨inferInstance, fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [← map_pow]
  have hy : y ^ 2 = 1 := by
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    funext i
    have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
    simpa using h2 (Multiplicative.toAdd y i)
  rw [hy, map_one]

theorem exists_perm_of_mem_normalizer (hι : Function.Injective ι) {n : G}
    (hn : n ∈ normalizer (ι.range : Set G)) :
    ∃ g : Equiv.Perm V6, IsAddPerm g ∧ ∀ v, n * coordElt ι v * n⁻¹ = coordElt ι (g v) := by
  classical
  have hmem : ∀ v : V6, n * coordElt ι v * n⁻¹ ∈ ι.range := by
    intro v
    exact (Subgroup.mem_normalizer_iff.mp hn (coordElt ι v)).mp
      (MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd v, rfl⟩)
  let c : V6 → Elem2 6 := fun v => Classical.choose (MonoidHom.mem_range.mp (hmem v))
  have hc : ∀ v, ι (c v) = n * coordElt ι v * n⁻¹ := fun v =>
    Classical.choose_spec (MonoidHom.mem_range.mp (hmem v))
  let gfun : V6 → V6 := fun v => (c v).toAdd
  have hgfun : ∀ v, Multiplicative.ofAdd (gfun v) = c v := fun v => ofAdd_toAdd (c v)
  have hinj : Function.Injective gfun := by
    intro v w hvw
    have hcw : c v = c w := by
      have h := congrArg Multiplicative.ofAdd hvw
      rwa [hgfun v, hgfun w] at h
    have h1 : n * coordElt ι v * n⁻¹ = n * coordElt ι w * n⁻¹ := by rw [← hc v, ← hc w, hcw]
    have h2 : n * coordElt ι v = n * coordElt ι w := mul_right_cancel h1
    have h3 : coordElt ι v = coordElt ι w := mul_left_cancel h2
    exact Multiplicative.ofAdd.injective (hι h3)
  have hadd : ∀ v w, gfun (v + w) = gfun v + gfun w := by
    intro v w
    apply Multiplicative.ofAdd.injective
    rw [ofAdd_add, hgfun (v + w), hgfun v, hgfun w]
    apply hι
    rw [hc (v + w), map_mul, hc v, hc w, coordElt_add]
    group
  refine ⟨Equiv.ofBijective gfun (Finite.injective_iff_bijective.mp hinj), ?_, ?_⟩
  · intro v w
    show gfun (v + w) = gfun v + gfun w
    exact hadd v w
  · intro v
    show n * coordElt ι v * n⁻¹ = coordElt ι (gfun v)
    rw [← hc v]
    simp only [coordElt, hgfun v]

theorem isConj_conj_iff (t x n : G) : IsConj t (n * x * n⁻¹) ↔ IsConj t x :=
  ⟨fun h => h.trans (isConj_iff.mpr ⟨n, rfl⟩).symm, fun h => h.trans (isConj_iff.mpr ⟨n, rfl⟩)⟩

theorem HData.exists_normalizer_conj_t (hD : HData G t z b z₁ S Eg T T' W0 ι) {x : G}
    (hx : x ∈ ι.range) (hxt : IsConj t x) :
    ∃ n ∈ normalizer (ι.range : Set G), n * t * n⁻¹ = x := by
  classical
  obtain ⟨g, hg⟩ := isConj_iff.mp hxt
  let A : Subgroup G := ι.range
  let B : Subgroup G := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hB_def : B = A.map (MulAut.conj g⁻¹).toMonoidHom := rfl
  have hA : CFSG.Open.IsElemAbelian 2 A := isElemAbelian_range hD.injective_ι
  have hB_le : B ≤ centralizer ({t} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hy
    rw [← hay]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have ht : t = g⁻¹ * x * g := by rw [← hg]; group
    rw [ht]
    have hxa : x * a = a * x := Subgroup.mul_comm_of_mem_isMulCommutative A hx ha
    calc (g⁻¹ * a * g) * (g⁻¹ * x * g) = g⁻¹ * (a * x) * g := by group
      _ = g⁻¹ * (x * a) * g := by rw [hxa]
      _ = (g⁻¹ * x * g) * (g⁻¹ * a * g) := by group
  have hB_card : Nat.card B = 64 := by
    rw [hB_def, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    rw [← Nat.card_congr (MonoidHom.ofInjective hD.injective_ι).toEquiv]
    rw [← Nat.card_congr (Multiplicative.ofAdd : (Fin 6 → ZMod 2) ≃ Elem2 6)]
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hB_elem : CFSG.Open.IsElemAbelian 2 B := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hy
    rw [← hay, ← map_pow, hA.2 a ha, map_one]
  obtain ⟨h, hh_cent, hh_eq⟩ := hD.conj_E64 B hB_le hB_card hB_elem
  have hn_norm : g * h ∈ normalizer (ι.range : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have h1 : h * a * h⁻¹ ∈ B := by
        rw [hh_eq]
        exact Subgroup.mem_map.mpr
          ⟨a, ha, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
      rw [hB_def] at h1
      obtain ⟨a', ha', ha'eq⟩ := Subgroup.mem_map.mp h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at ha'eq
      have hgoal : (g * h) * a * (g * h)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ := by group
      rw [hgoal, ← ha'eq]
      convert ha' using 1
      group
    · intro ha
      have h1 : h * a * h⁻¹ ∈ B := by
        rw [hB_def]
        refine Subgroup.mem_map.mpr ⟨g * (h * a * h⁻¹) * g⁻¹, ?_, ?_⟩
        · convert ha using 1
          group
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; group
      rw [hh_eq] at h1
      obtain ⟨a', ha', ha'eq⟩ := Subgroup.mem_map.mp h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at ha'eq
      have : a' = a := by
        have h2 : h * a' = h * a := mul_right_cancel ha'eq
        exact mul_left_cancel h2
      rwa [← this]
  refine ⟨g * h, hn_norm, ?_⟩
  have hht : h * t * h⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hh_cent
    rw [hh_cent]; group
  calc (g * h) * t * (g * h)⁻¹ = g * (h * t * h⁻¹) * g⁻¹ := by group
    _ = g * t * g⁻¹ := by rw [hht]
    _ = x := hg

theorem HData.isConj_fuse (hD : HData G t z b z₁ S Eg T T' W0 ι) {v w : V6}
    (hv : IsConj t (coordElt ι v)) (hw0 : w ≠ 0) (hwt : w ≠ tv) (hv0 : v ≠ 0) (hvt : v ≠ tv)
    (hl : lam v = lam w) (hq : qm v = qm w) : IsConj t (coordElt ι w) := by
  obtain ⟨n, _hn, hnconj⟩ := hD.fuse v w hv0 hvt hw0 hwt hl hq
  rw [← hnconj]
  exact (isConj_conj_iff t (coordElt ι v) n).mpr hv

end CFSG.EvenSporadicStandard.HNRecog.Harada
