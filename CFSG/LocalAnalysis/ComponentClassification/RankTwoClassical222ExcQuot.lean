module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcCenter

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup

structure SqClosed {G : Type*} [Group G] (K X : Subgroup G) : Prop where
  le : X ≤ K
  sq_eq_one : ∀ p ∈ X, p ^ 2 = 1
  four_le : 4 ≤ Nat.card X
  sq_conj_mem : ∀ w ∈ X, w ≠ 1 → ∀ c ∈ K, c * w = w * c → ∀ p ∈ X, c ^ 2 * p * (c ^ 2)⁻¹ ∈ X

variable {G : Type*} [Group G]

theorem SqClosed.mul_comm {K X : Subgroup G} (hX : SqClosed K X) {g h : G} (hg : g ∈ X)
    (hh : h ∈ X) : g * h = h * g := by
  have h1 := hX.sq_eq_one _ (X.mul_mem hg hh)
  have h2 := hX.sq_eq_one g hg
  have h3 := hX.sq_eq_one h hh
  rw [sq] at h1 h2 h3
  calc g * h = g * (g * h * (g * h)) * h := by rw [h1, mul_one]
    _ = g * g * h * g * (h * h) := by group
    _ = h * g := by rw [h2, h3, one_mul, mul_one]

theorem SqClosed.conj {K X : Subgroup G} (hX : SqClosed K X) {g : G} (hg : g ∈ K) :
    SqClosed K (X.map (MulAut.conj g).toMonoidHom) := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact K.mul_mem (K.mul_mem hg (hX.le hx)) (K.inv_mem hg)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hX.sq_eq_one x hx, map_one]
  · rw [Subgroup.card_map_of_injective hinj]
    exact hX.four_le
  · rintro _ ⟨w, hw, rfl⟩ hw1 c hc hcw _ ⟨p, hp, rfl⟩
    have hw1' : w ≠ 1 := fun h => hw1 (by rw [h, map_one])
    have hc' : g⁻¹ * c * g ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hg) hc) hg
    have hcw' : g⁻¹ * c * g * w = w * (g⁻¹ * c * g) := by
      have e : (MulAut.conj g).toMonoidHom w = g * w * g⁻¹ := rfl
      rw [e] at hcw
      calc g⁻¹ * c * g * w = g⁻¹ * (c * (g * w * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * w * g⁻¹) * c) * g := by rw [hcw]
        _ = w * (g⁻¹ * c * g) := by group
    refine ⟨_, hX.sq_conj_mem w hw hw1' _ hc' hcw' p hp, ?_⟩
    have e : (g⁻¹ * c * g) ^ 2 = g⁻¹ * c ^ 2 * g := by
      rw [sq, sq]
      group
    change g * ((g⁻¹ * c * g) ^ 2 * p * ((g⁻¹ * c * g) ^ 2)⁻¹) * g⁻¹ =
      c ^ 2 * (g * p * g⁻¹) * (c ^ 2)⁻¹
    rw [e]
    group

theorem SqClosed.map_mulEquiv {Q : Type*} [Group Q] {K : Subgroup G} {Y : Subgroup Q}
    (hY : SqClosed ⊤ Y) (e : Q ≃* K) : SqClosed K (Y.map (K.subtype.comp e.toMonoidHom)) := by
  set f : Q →* G := K.subtype.comp e.toMonoidHom with hf
  have hinj : Function.Injective f := Subtype.val_injective.comp e.injective
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact (e y).2
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hY.sq_eq_one y hy, map_one]
  · rw [Subgroup.card_map_of_injective hinj]
    exact hY.four_le
  · rintro _ ⟨w, hw, rfl⟩ hw1 c hc hcw _ ⟨p, hp, rfl⟩
    have hw1' : w ≠ 1 := fun h => hw1 (by rw [h, map_one])
    set c' : Q := e.symm ⟨c, hc⟩
    have hfc : f c' = c := by simp [hf, c']
    have hcw' : c' * w = w * c' := by
      apply hinj
      rw [map_mul, map_mul, hfc]
      exact hcw
    refine ⟨_, hY.sq_conj_mem w hw hw1' c' (mem_top _) hcw' p hp, ?_⟩
    rw [map_mul, map_mul, map_inv, map_pow, hfc]

theorem IsHyp212.sqClosed_map {H : Type} [Group H] {P : Subgroup H} (hP : IsHyp212 P) :
    SqClosed ⊤ (P.map (QuotientGroup.mk' (center H))) := by
  have hinj : Set.InjOn (QuotientGroup.mk' (center H)) P := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ center H := QuotientGroup.eq.1 hab
    have h1 := hP.eq_one_of_mem_center _ (P.mul_mem (P.inv_mem ha) hb) hmem
    rw [inv_mul_eq_one] at h1
    exact h1
  refine ⟨le_top, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    rw [← map_pow, hP.sq_eq_one p hp, map_one]
  · have h1 : Nat.card (P.map (QuotientGroup.mk' (center H))) =
        Nat.card ((QuotientGroup.mk' (center H)) '' (P : Set H)) := by
      rw [← Subgroup.coe_map]
      rfl
    rw [h1, Nat.card_image_of_injOn hinj]
    exact hP.four_le
  · rintro _ ⟨w, hw, rfl⟩ hw1 c - hcw _ ⟨p, hp, rfl⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (center H) c
    have hw1' : w ≠ 1 := fun h => hw1 (by rw [h, map_one])
    have hz : c * w * c⁻¹ * w⁻¹ ∈ center H := by
      rw [← QuotientGroup.eq_one_iff]
      have e : QuotientGroup.mk' (center H) (c * w * c⁻¹ * w⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [hcw]
        group
      exact e
    set z := c * w * c⁻¹ * w⁻¹ with hzdef
    have hzc : ∀ g : H, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
    have ha : c * w * c⁻¹ = z * w := by
      rw [hzdef]
      group
    have hw2 : w * w = 1 := by
      rw [← sq]
      exact hP.sq_eq_one w hw
    have hz2 : z * z = 1 := by
      have e1 : (c * w * c⁻¹) * (c * w * c⁻¹) = 1 := by
        calc (c * w * c⁻¹) * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
          _ = 1 := by rw [hw2]; group
      rw [ha] at e1
      calc z * z = z * (w * w) * z := by rw [hw2]; group
        _ = z * w * (w * z) := by group
        _ = z * w * (z * w) := by rw [hzc w]
        _ = 1 := e1
    have hc2 : c ^ 2 * w = w * c ^ 2 := by
      have e2 : c ^ 2 * w * (c ^ 2)⁻¹ = w := by
        calc c ^ 2 * w * (c ^ 2)⁻¹ = c * (c * w * c⁻¹) * c⁻¹ := by rw [sq]; group
          _ = c * (z * w) * c⁻¹ := by rw [ha]
          _ = c * z * w * c⁻¹ := by group
          _ = z * c * w * c⁻¹ := by rw [hzc c]
          _ = z * (c * w * c⁻¹) := by group
          _ = z * (z * w) := by rw [ha]
          _ = z * z * w := by group
          _ = w := by rw [hz2, one_mul]
      calc c ^ 2 * w = c ^ 2 * w * (c ^ 2)⁻¹ * c ^ 2 := by group
        _ = w * c ^ 2 := by rw [e2]
    refine ⟨_, hP.conj_mem w hw hw1' (c ^ 2) hc2 p hp, ?_⟩
    simp only [map_mul, map_inv, map_pow]

end CFSG.ComponentClassification.RankTwoClassical
