module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcCenter

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup

structure Hyp212In {G : Type*} [Group G] (K : Subgroup G) (Z : Set G) (X : Subgroup G) :
    Prop where
  le : X ≤ K
  sq_eq_one : ∀ p ∈ X, p ^ 2 = 1
  four_le : 4 ≤ Nat.card X
  not_mem : ∀ z ∈ Z, z ∉ X
  conj_mem : ∀ w ∈ X, w ≠ 1 → ∀ c ∈ K, c * w = w * c → ∀ p ∈ X, c * p * c⁻¹ ∈ X

variable {G : Type*} [Group G]

theorem Hyp212In.mul_comm {K : Subgroup G} {Z : Set G} {X : Subgroup G} (hX : Hyp212In K Z X)
    {g h : G} (hg : g ∈ X) (hh : h ∈ X) : g * h = h * g := by
  have h1 := hX.sq_eq_one _ (X.mul_mem hg hh)
  have h2 := hX.sq_eq_one g hg
  have h3 := hX.sq_eq_one h hh
  rw [sq] at h1 h2 h3
  calc g * h = g * (g * h * (g * h)) * h := by rw [h1, mul_one]
    _ = g * g * h * g * (h * h) := by group
    _ = h * g := by rw [h2, h3, one_mul, mul_one]

theorem Hyp212In.conj {K : Subgroup G} {Z : Set G} {X : Subgroup G} (hX : Hyp212In K Z X) {g : G}
    (hg : g ∈ K) (hZ : ∀ z ∈ Z, g * z * g⁻¹ = z) :
    Hyp212In K Z (X.map (MulAut.conj g).toMonoidHom) := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact K.mul_mem (K.mul_mem hg (hX.le hx)) (K.inv_mem hg)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hX.sq_eq_one x hx, map_one]
  · rw [Subgroup.card_map_of_injective hinj]
    exact hX.four_le
  · rintro z hz ⟨x, hx, hxz⟩
    have e : x = z := by
      have h1 : g * x * g⁻¹ = g * z * g⁻¹ := by rw [hZ z hz]; exact hxz
      simpa using h1
    exact hX.not_mem z hz (e ▸ hx)
  · rintro _ ⟨w, hw, rfl⟩ hw1 c hc hcw _ ⟨p, hp, rfl⟩
    have hw1' : w ≠ 1 := fun h => hw1 (by rw [h, map_one])
    have hc' : g⁻¹ * c * g ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hg) hc) hg
    have hcw' : g⁻¹ * c * g * w = w * (g⁻¹ * c * g) := by
      have e : (MulAut.conj g).toMonoidHom w = g * w * g⁻¹ := rfl
      rw [e] at hcw
      calc g⁻¹ * c * g * w = g⁻¹ * (c * (g * w * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * w * g⁻¹) * c) * g := by rw [hcw]
        _ = w * (g⁻¹ * c * g) := by group
    refine ⟨_, hX.conj_mem w hw hw1' _ hc' hcw' p hp, ?_⟩
    change g * (g⁻¹ * c * g * p * (g⁻¹ * c * g)⁻¹) * g⁻¹ = c * (g * p * g⁻¹) * c⁻¹
    group

theorem IsHyp212.hyp212In_map {H : Type} [Group H] {P : Subgroup H} (hP : IsHyp212 P)
    {K : Subgroup G} (e : H ≃* K) {Z : Set G}
    (hZ : ∀ z ∈ Z, ∃ h : z ∈ K, z ≠ 1 ∧ e.symm ⟨z, h⟩ ∈ center H) :
    Hyp212In K Z (P.map (K.subtype.comp e.toMonoidHom)) := by
  set f : H →* G := K.subtype.comp e.toMonoidHom with hf
  have hinj : Function.Injective f := Subtype.val_injective.comp e.injective
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact (e y).2
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hP.sq_eq_one y hy, map_one]
  · rw [Subgroup.card_map_of_injective hinj]
    exact hP.four_le
  · rintro z hz ⟨p, hp, hpz⟩
    obtain ⟨hzK, hz1, hzc⟩ := hZ z hz
    have hp' : p = e.symm ⟨z, hzK⟩ := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext hpz
    have h1 := hP.eq_one_of_mem_center p hp (hp' ▸ hzc)
    apply hz1
    rw [← hpz, h1, map_one]
  · rintro _ ⟨w, hw, rfl⟩ hw1 c hc hcw _ ⟨p, hp, rfl⟩
    have hw1' : w ≠ 1 := fun h => hw1 (by rw [h, map_one])
    set c' : H := e.symm ⟨c, hc⟩
    have hfc : f c' = c := by simp [hf, c']
    have hcw' : c' * w = w * c' := by
      apply hinj
      rw [map_mul, map_mul, hfc]
      exact hcw
    refine ⟨_, hP.conj_mem w hw hw1' c' hcw' p hp, ?_⟩
    rw [map_mul, map_mul, map_inv, hfc]

end CFSG.ComponentClassification.RankTwoClassical
