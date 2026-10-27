module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage4.RestSetupRank

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

section Cycle

variable {G : Type} [Group G] {z u w v : G}

theorem t2P53_cycle (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hwz : w * z = z * w) (hwu : w * u * w⁻¹ = u * z) (hww : w * w = z)
    (hvz : v * z * v⁻¹ = z * u) (hvv : v * v = u) :
    (w * v) * z * (w * v)⁻¹ = u ∧ (w * v) * u * (w * v)⁻¹ = u * z ∧
      (w * v) * (u * z) * (w * v)⁻¹ = z ∧ w * (w * v) * w⁻¹ = (w * v)⁻¹ * z := by
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hwz' : w * z * w⁻¹ = z := by
    calc w * z * w⁻¹ = z * w * w⁻¹ := by rw [hwz]
      _ = z := by group
  have hvu : v * u * v⁻¹ = u := by
    calc v * u * v⁻¹ = v * (v * v) * v⁻¹ := by rw [hvv]
      _ = v * v := by group
      _ = u := hvv
  have hvzu : v * (z * u) * v⁻¹ = z := by
    calc v * (z * u) * v⁻¹ = (v * z * v⁻¹) * (v * u * v⁻¹) := by group
      _ = z * u * u := by rw [hvz, hvu]
      _ = z * (u * u) := by group
      _ = z := by rw [hu2, mul_one]
  have h1 : (w * v) * z * (w * v)⁻¹ = u := by
    calc (w * v) * z * (w * v)⁻¹ = w * (v * z * v⁻¹) * w⁻¹ := by group
      _ = w * (z * u) * w⁻¹ := by rw [hvz]
      _ = (w * z * w⁻¹) * (w * u * w⁻¹) := by group
      _ = z * (u * z) := by rw [hwz', hwu]
      _ = (z * u) * z := by group
      _ = (u * z) * z := by rw [hzu]
      _ = u * (z * z) := by group
      _ = u := by rw [hz2, mul_one]
  have h2 : (w * v) * u * (w * v)⁻¹ = u * z := by
    calc (w * v) * u * (w * v)⁻¹ = w * (v * u * v⁻¹) * w⁻¹ := by group
      _ = w * u * w⁻¹ := by rw [hvu]
      _ = u * z := hwu
  have h3 : (w * v) * (u * z) * (w * v)⁻¹ = z := by
    calc (w * v) * (u * z) * (w * v)⁻¹
        = ((w * v) * u * (w * v)⁻¹) * ((w * v) * z * (w * v)⁻¹) := by group
      _ = (u * z) * u := by rw [h2, h1]
      _ = (z * u) * u := by rw [← hzu]
      _ = z * (u * u) := by group
      _ = z := by rw [hu2, mul_one]
  refine ⟨h1, h2, h3, ?_⟩
  have hvinv : v⁻¹ = v * u := by
    have : v * u * v = 1 := by
      calc v * u * v = v * (v * v) * v := by rw [hvv]
        _ = (v * v) * (v * v) := by group
        _ = u * u := by rw [hvv]
        _ = 1 := hu2
    exact (eq_inv_of_mul_eq_one_left this).symm
  have hzv : z * v = v * u * z := by
    have h4 : v⁻¹ * z * v = z * u := by
      calc v⁻¹ * z * v = v⁻¹ * (v * (z * u) * v⁻¹) * v := by rw [hvzu]
        _ = z * u := by group
    calc z * v = v * (v⁻¹ * z * v) := by group
      _ = v * (z * u) := by rw [h4]
      _ = v * (u * z) := by rw [hzu]
      _ = v * u * z := by group
  have hwz'' : w⁻¹ * z = z * w⁻¹ := by
    calc w⁻¹ * z = w⁻¹ * z * w * w⁻¹ := by group
      _ = w⁻¹ * (z * w) * w⁻¹ := by group
      _ = w⁻¹ * (w * z) * w⁻¹ := by rw [hwz]
      _ = z * w⁻¹ := by group
  calc w * (w * v) * w⁻¹ = (w * w) * v * w⁻¹ := by group
    _ = z * v * w⁻¹ := by rw [hww]
    _ = v * u * z * w⁻¹ := by rw [hzv]
    _ = v * u * (z * w⁻¹) := by group
    _ = v * u * (w⁻¹ * z) := by rw [hwz'']
    _ = (v * u) * w⁻¹ * z := by group
    _ = v⁻¹ * w⁻¹ * z := by rw [hvinv]
    _ = (w * v)⁻¹ * z := by group

theorem t2P53_wb3 (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hwz : w * z = z * w) (hwu : w * u * w⁻¹ = u * z) (hww : w * w = z)
    (hvz : v * z * v⁻¹ = z * u) (hvv : v * v = u) :
    w * ((w * v) * (w * v) * (w * v)) * w⁻¹ = ((w * v) * (w * v) * (w * v))⁻¹ := by
  obtain ⟨h1, h2, h3, h4⟩ := t2P53_cycle hz2 hu2 hzu hwz hwu hww hvz hvv
  set b := w * v with hb
  have e1 : z * b⁻¹ = b⁻¹ * u := by
    calc z * b⁻¹ = b⁻¹ * (b * z * b⁻¹) := by group
      _ = b⁻¹ * u := by rw [h1]
  have e2 : u * z * b⁻¹ = b⁻¹ * z := by
    calc u * z * b⁻¹ = b⁻¹ * (b * (u * z) * b⁻¹) := by group
      _ = b⁻¹ * z := by rw [h3]
  have hconj : w * (b * b * b) * w⁻¹ = (w * b * w⁻¹) * (w * b * w⁻¹) * (w * b * w⁻¹) := by group
  rw [hconj, h4]
  calc b⁻¹ * z * (b⁻¹ * z) * (b⁻¹ * z) = b⁻¹ * (z * b⁻¹) * z * (b⁻¹ * z) := by group
    _ = b⁻¹ * (b⁻¹ * u) * z * (b⁻¹ * z) := by rw [e1]
    _ = b⁻¹ * b⁻¹ * (u * z * b⁻¹) * z := by group
    _ = b⁻¹ * b⁻¹ * (b⁻¹ * z) * z := by rw [e2]
    _ = b⁻¹ * b⁻¹ * b⁻¹ * (z * z) := by group
    _ = b⁻¹ * b⁻¹ * b⁻¹ := by rw [hz2, mul_one]
    _ = (b * b * b)⁻¹ := by group

theorem t2P53_a_cycle (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hwz : w * z = z * w) (hwu : w * u * w⁻¹ = u * z) (hww : w * w = z)
    (hvz : v * z * v⁻¹ = z * u) (hvv : v * v = u) :
    ((w * v) * (w * v))⁻¹ * z * ((w * v) * (w * v)) = u ∧
      ((w * v) * (w * v))⁻¹ * u * ((w * v) * (w * v)) = z * u := by
  obtain ⟨h1, h2, h3, h4⟩ := t2P53_cycle hz2 hu2 hzu hwz hwu hww hvz hvv
  set b := w * v with hb
  have f1 : b⁻¹ * u * b = z := by
    calc b⁻¹ * u * b = b⁻¹ * (b * z * b⁻¹) * b := by rw [h1]
      _ = z := by group
  have f2 : b⁻¹ * (u * z) * b = u := by
    calc b⁻¹ * (u * z) * b = b⁻¹ * (b * u * b⁻¹) * b := by rw [h2]
      _ = u := by group
  have f3 : b⁻¹ * z * b = u * z := by
    calc b⁻¹ * z * b = b⁻¹ * (b * (u * z) * b⁻¹) * b := by rw [h3]
      _ = u * z := by group
  constructor
  · calc (b * b)⁻¹ * z * (b * b) = b⁻¹ * (b⁻¹ * z * b) * b := by group
      _ = b⁻¹ * (u * z) * b := by rw [f3]
      _ = u := f2
  · calc (b * b)⁻¹ * u * (b * b) = b⁻¹ * (b⁻¹ * u * b) * b := by group
      _ = b⁻¹ * z * b := by rw [f1]
      _ = u * z := f3
      _ = z * u := hzu.symm

theorem t2P53_wa (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hwz : w * z = z * w) (hwu : w * u * w⁻¹ = u * z) (hww : w * w = z)
    (hvz : v * z * v⁻¹ = z * u) (hvv : v * v = u) :
    w * ((w * v) * (w * v)) * w⁻¹ = ((w * v) * (w * v))⁻¹ * (u * z) := by
  obtain ⟨h1, h2, h3, h4⟩ := t2P53_cycle hz2 hu2 hzu hwz hwu hww hvz hvv
  set b := w * v with hb
  have e1 : z * b⁻¹ = b⁻¹ * u := by
    calc z * b⁻¹ = b⁻¹ * (b * z * b⁻¹) := by group
      _ = b⁻¹ * u := by rw [h1]
  have hconj : w * (b * b) * w⁻¹ = (w * b * w⁻¹) * (w * b * w⁻¹) := by group
  rw [hconj, h4]
  calc b⁻¹ * z * (b⁻¹ * z) = b⁻¹ * (z * b⁻¹) * z := by group
    _ = b⁻¹ * (b⁻¹ * u) * z := by rw [e1]
    _ = (b * b)⁻¹ * (u * z) := by group

theorem t2P53_b3_comm (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z)
    (hwz : w * z = z * w) (hwu : w * u * w⁻¹ = u * z) (hww : w * w = z)
    (hvz : v * z * v⁻¹ = z * u) (hvv : v * v = u) :
    ((w * v) * (w * v) * (w * v)) * z = z * ((w * v) * (w * v) * (w * v)) ∧
      ((w * v) * (w * v) * (w * v)) * u = u * ((w * v) * (w * v) * (w * v)) := by
  obtain ⟨h1, h2, h3, h4⟩ := t2P53_cycle hz2 hu2 hzu hwz hwu hww hvz hvv
  set b := w * v with hb
  have g1 : b * b * b * z * (b * b * b)⁻¹ = z := by
    calc b * b * b * z * (b * b * b)⁻¹ = b * (b * (b * z * b⁻¹) * b⁻¹) * b⁻¹ := by group
      _ = b * (b * u * b⁻¹) * b⁻¹ := by rw [h1]
      _ = b * (u * z) * b⁻¹ := by rw [h2]
      _ = z := h3
  have g2 : b * b * b * u * (b * b * b)⁻¹ = u := by
    calc b * b * b * u * (b * b * b)⁻¹ = b * (b * (b * u * b⁻¹) * b⁻¹) * b⁻¹ := by group
      _ = b * (b * (u * z) * b⁻¹) * b⁻¹ := by rw [h2]
      _ = b * z * b⁻¹ := by rw [h3]
      _ = u := h1
  refine ⟨?_, ?_⟩
  · calc b * b * b * z = (b * b * b * z * (b * b * b)⁻¹) * (b * b * b) := by group
      _ = z * (b * b * b) := by rw [g1]
  · calc b * b * b * u = (b * b * b * u * (b * b * b)⁻¹) * (b * b * b) := by group
      _ = u * (b * b * b) := by rw [g2]

end Cycle

end CFSG.GH74.GLS.Stage4.Rest
