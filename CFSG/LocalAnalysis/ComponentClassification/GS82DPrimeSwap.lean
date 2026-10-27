module

public import CFSG.GH74.GLS.TwoThin.OddOrbit
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.TwoThin.Struct
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.DPrime

open CFSG Subgroup GH74.GLS GH74.GLS.TwoThin

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_swap_lift {t s : Y} (ht : t * t = 1) (hs : ∀ y : Y, s * y = y * s)
    (hs2 : s * s = 1) {u : barQ Y} (hu : u * u = 1)
    (hus : u * ((barMk Y t)⁻¹ * u * barMk Y t) = barMk Y s) :
    ∃ v : Y, barMk Y v = u ∧ v * v = 1 ∧ t⁻¹ * v * t = v * s := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hsbar : barMk Y s * barMk Y s = 1 := by rw [← map_mul, hs2, map_one]
  have hut : (barMk Y t)⁻¹ * u * barMk Y t = u * barMk Y s := by
    calc (barMk Y t)⁻¹ * u * barMk Y t = u⁻¹ * (u * ((barMk Y t)⁻¹ * u * barMk Y t)) := by group
      _ = u * barMk Y s := by rw [hus, huinv]
  set O := pPrimeCore 2 Y with hO
  have hOodd : Odd (Nat.card O) := odd_card_pPrimeCore Y
  have hmemO : ∀ y : Y, y ∈ O ↔ barMk Y y = 1 := fun y => (QuotientGroup.eq_one_iff y).symm
  obtain ⟨x₁, hx₁⟩ := barMk_surjective u
  have hf₁ : ∀ o : O, x₁⁻¹ * (t⁻¹ * (x₁ * o) * t) * s ∈ O := by
    intro o
    rw [hmemO]
    have ho : barMk Y o = 1 := (hmemO o).mp o.2
    simp only [map_mul, map_inv, hx₁, ho, mul_one]
    rw [show u⁻¹ * ((barMk Y t)⁻¹ * u * barMk Y t) * barMk Y s =
      u⁻¹ * ((barMk Y t)⁻¹ * u * barMk Y t * barMk Y s) by group, hut, mul_assoc, hsbar,
      mul_one, inv_mul_cancel]
  let f₁ : O → O := fun o => ⟨_, hf₁ o⟩
  have hf₁inv : Function.Involutive f₁ := by
    intro o
    apply Subtype.ext
    change x₁⁻¹ * (t⁻¹ * (x₁ * (x₁⁻¹ * (t⁻¹ * (x₁ * (o : Y)) * t) * s)) * t) * s = o
    have e1 : x₁⁻¹ * (t⁻¹ * (x₁ * (x₁⁻¹ * (t⁻¹ * (x₁ * (o : Y)) * t) * s)) * t) * s =
        x₁⁻¹ * (t⁻¹ * t⁻¹) * x₁ * (o : Y) * (t * (s * t)) * s := by group
    have h1 : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht, inv_one]
    rw [e1, h1, hs t]
    calc x₁⁻¹ * 1 * x₁ * (o : Y) * (t * (t * s)) * s = x₁⁻¹ * x₁ * o * ((t * t) * (s * s)) := by
          group
      _ = o := by rw [ht, hs2]; group
  obtain ⟨o₁, ho₁⟩ := exists_fixedPoint_of_involutive_of_odd hOodd f₁ hf₁inv
  have ho₁' : x₁⁻¹ * (t⁻¹ * (x₁ * o₁) * t) * s = o₁ := congrArg Subtype.val ho₁
  set x₀ := x₁ * (o₁ : Y) with hx₀
  have hx₀u : barMk Y x₀ = u := by
    rw [hx₀, map_mul, hx₁, (hmemO _).mp o₁.2, mul_one]
  have hx₀t : t⁻¹ * x₀ * t = x₀ * s := by
    have h1 : t⁻¹ * x₀ * t * s = x₀ := by
      calc t⁻¹ * x₀ * t * s = x₁ * (x₁⁻¹ * (t⁻¹ * (x₁ * o₁) * t) * s) := by rw [hx₀]; group
        _ = x₀ := by rw [ho₁', hx₀]
    calc t⁻¹ * x₀ * t = t⁻¹ * x₀ * t * s * s := by rw [mul_assoc _ s s, hs2, mul_one]
      _ = x₀ * s := by rw [h1]
  set C := O ⊓ centralizer ({t} : Set Y) with hC
  have hCodd : Odd (Nat.card C) := hOodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hx₀sq : barMk Y (x₀⁻¹ * x₀⁻¹) = 1 := by
    rw [map_mul, map_inv, hx₀u, huinv, hu]
  have hmemC : ∀ z : Y, z ∈ O → t⁻¹ * z * t = z → z ∈ C := by
    intro z hz hzt
    refine ⟨hz, mem_centralizer_singleton_iff.mpr ?_⟩
    calc z * t = t * (t⁻¹ * z * t) := by group
      _ = t * z := by rw [hzt]
  have hf₂ : ∀ o : C, x₀⁻¹ * (x₀ * o)⁻¹ ∈ C := by
    intro o
    have hoO : (o : Y) ∈ O := (mem_inf.mp o.2).1
    have hot : t⁻¹ * (o : Y) * t = o := by
      have h := mem_centralizer_singleton_iff.mp (mem_inf.mp o.2).2
      calc t⁻¹ * (o : Y) * t = t⁻¹ * ((o : Y) * t) := by group
        _ = o := by rw [h]; group
    refine hmemC _ ?_ ?_
    · rw [hmemO]
      simp only [map_mul, map_inv, hx₀u, (hmemO _).mp hoO, inv_one, mul_one, huinv, hu]
    · have e1 : t⁻¹ * (x₀⁻¹ * (x₀ * (o : Y))⁻¹) * t =
          (t⁻¹ * x₀ * t)⁻¹ * (t⁻¹ * (o : Y) * t)⁻¹ * (t⁻¹ * x₀ * t)⁻¹ := by group
      rw [e1, hot, hx₀t, mul_inv_rev, hsinv]
      calc s * x₀⁻¹ * (o : Y)⁻¹ * (s * x₀⁻¹) = s * (x₀⁻¹ * (o : Y)⁻¹ * s) * x₀⁻¹ := by group
        _ = s * (s * (x₀⁻¹ * (o : Y)⁻¹)) * x₀⁻¹ := by rw [hs (x₀⁻¹ * (o : Y)⁻¹)]
        _ = x₀⁻¹ * (x₀ * (o : Y))⁻¹ := by rw [← mul_assoc s s, hs2, one_mul]; group
  let f₂ : C → C := fun o => ⟨_, hf₂ o⟩
  have hf₂inv : Function.Involutive f₂ := by
    intro o
    apply Subtype.ext
    change x₀⁻¹ * (x₀ * (x₀⁻¹ * (x₀ * (o : Y))⁻¹))⁻¹ = o
    group
  obtain ⟨o₂, ho₂⟩ := exists_fixedPoint_of_involutive_of_odd hCodd f₂ hf₂inv
  have ho₂' : x₀⁻¹ * (x₀ * o₂)⁻¹ = o₂ := congrArg Subtype.val ho₂
  have ho₂O : (o₂ : Y) ∈ O := (mem_inf.mp o₂.2).1
  have ho₂t : (o₂ : Y) * t = t * o₂ := mem_centralizer_singleton_iff.mp (mem_inf.mp o₂.2).2
  refine ⟨x₀ * o₂, ?_, ?_, ?_⟩
  · rw [map_mul, hx₀u, (hmemO _).mp ho₂O, mul_one]
  · have h1 : (x₀ * (o₂ : Y))⁻¹ = x₀ * o₂ := by
      calc (x₀ * (o₂ : Y))⁻¹ = x₀ * (x₀⁻¹ * (x₀ * o₂)⁻¹) := by group
        _ = x₀ * o₂ := by rw [ho₂']
    calc x₀ * (o₂ : Y) * (x₀ * o₂) = x₀ * (o₂ : Y) * (x₀ * o₂)⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel _
  · calc t⁻¹ * (x₀ * (o₂ : Y)) * t = (t⁻¹ * x₀ * t) * (t⁻¹ * ((o₂ : Y) * t)) := by group
      _ = x₀ * (o₂ : Y) * s := by
        rw [hx₀t, ho₂t, ← mul_assoc t⁻¹ t, inv_mul_cancel, one_mul, mul_assoc x₀ s,
          hs (o₂ : Y), ← mul_assoc]

end CFSG.ComponentClassification.GS82PumpInputs.DPrime
