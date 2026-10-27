module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G]

theorem Gxy_mul_left (a x : G) : Gxy a (a * x) = Gxy a x := by
  ext g
  simp only [mem_Gxy, mem_Gx]
  constructor
  · rintro ⟨hag, hax⟩
    refine ⟨hag, ?_⟩
    have h : a * (x * g) = a * (g * x) :=
      calc a * (x * g) = (a * x) * g := (mul_assoc a x g).symm
        _ = g * (a * x) := hax
        _ = (g * a) * x := (mul_assoc g a x).symm
        _ = (a * g) * x := by rw [hag]
        _ = a * (g * x) := mul_assoc a g x
    exact mul_left_cancel h
  · rintro ⟨hag, hxg⟩
    refine ⟨hag, ?_⟩
    calc (a * x) * g = a * (x * g) := mul_assoc a x g
      _ = a * (g * x) := by rw [hxg]
      _ = (a * g) * x := (mul_assoc a g x).symm
      _ = (g * a) * x := by rw [hag]
      _ = g * (a * x) := mul_assoc g a x

theorem Gxy_map_conj {a b k : G} (hk : k * a * k⁻¹ = a) :
    (Gxy a b).map (MulAut.conj k).toMonoidHom = Gxy a (k * b * k⁻¹) := by
  have ha' : k⁻¹ * a * k = a :=
    calc k⁻¹ * a * k = k⁻¹ * (k * a * k⁻¹) * k := by rw [hk]
      _ = a := by group
  ext g
  simp only [Subgroup.mem_map, mem_Gxy, mem_Gx, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, ⟨hxa, hxb⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · calc a * (k * x * k⁻¹) = (k * a * k⁻¹) * (k * x * k⁻¹) := by rw [hk]
        _ = k * (a * x) * k⁻¹ := by group
        _ = k * (x * a) * k⁻¹ := by rw [hxa]
        _ = (k * x * k⁻¹) * (k * a * k⁻¹) := by group
        _ = (k * x * k⁻¹) * a := by rw [hk]
    · calc (k * b * k⁻¹) * (k * x * k⁻¹) = k * (b * x) * k⁻¹ := by group
        _ = k * (x * b) * k⁻¹ := by rw [hxb]
        _ = (k * x * k⁻¹) * (k * b * k⁻¹) := by group
  · rintro ⟨hga, hgb⟩
    refine ⟨k⁻¹ * g * k, ⟨?_, ?_⟩, by group⟩
    · calc a * (k⁻¹ * g * k) = (k⁻¹ * a * k) * (k⁻¹ * g * k) := by rw [ha']
        _ = k⁻¹ * (a * g) * k := by group
        _ = k⁻¹ * (g * a) * k := by rw [hga]
        _ = (k⁻¹ * g * k) * (k⁻¹ * a * k) := by group
        _ = (k⁻¹ * g * k) * a := by rw [ha']
    · calc b * (k⁻¹ * g * k) = k⁻¹ * ((k * b * k⁻¹) * g) * k := by group
        _ = k⁻¹ * (g * (k * b * k⁻¹)) * k := by rw [hgb]
        _ = (k⁻¹ * g * k) * b := by group

theorem nonempty_mulEquiv_Gxy_conj {a b k : G} (hk : k * a * k⁻¹ = a) :
    Nonempty (↥(Gxy a b) ≃* ↥(Gxy a (k * b * k⁻¹))) :=
  ⟨(Subgroup.equivMapOfInjective (Gxy a b) (MulAut.conj k).toMonoidHom
      (MulAut.conj k).injective).trans (MulEquiv.subgroupCongr (Gxy_map_conj hk))⟩

theorem mul_conj_of_fix {a x k : G} (hk : k * a * k⁻¹ = a) :
    a * (k * x * k⁻¹) = k * (a * x) * k⁻¹ :=
  calc a * (k * x * k⁻¹) = (k * a * k⁻¹) * (k * x * k⁻¹) := by rw [hk]
    _ = k * (a * x) * k⁻¹ := by group

theorem comm_of_sq_mul {a t : G} (ha : a ^ 2 = 1) (ht : t ^ 2 = 1) (hat : (a * t) ^ 2 = 1) :
    a * t = t * a := by
  have h1 : a * t * (a * t) = 1 := by simpa [pow_two] using hat
  have haa : a * a = 1 := by simpa [pow_two] using ha
  have htt : t * t = 1 := by simpa [pow_two] using ht
  have h2 : a * t = (a * t)⁻¹ := eq_inv_of_mul_eq_one_left h1
  calc a * t = (a * t)⁻¹ := h2
    _ = t⁻¹ * a⁻¹ := mul_inv_rev a t
    _ = t * a := by rw [inv_eq_of_mul_eq_one_right htt, inv_eq_of_mul_eq_one_right haa]

end CFSG.EvenSporadicStandard.HNRecog.Section3
