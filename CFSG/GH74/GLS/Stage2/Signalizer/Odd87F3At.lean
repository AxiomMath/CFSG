module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3S
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup

variable {M : Type*} [Group M]

@[expose] def F3SAt (G : Subgroup M) (u x : M) (p : ℕ) : Prop :=
  x ∈ G → orderOf x = p → u * x * u⁻¹ = x⁻¹ →
    ¬ IsPGroup p ↥(Subgroup.closure {w : M | ∃ c ∈ Subgroup.closure
      {y : M | y ∈ G ∧ u * y = y * u ∧ Odd (orderOf y)}, w = c * x * c⁻¹})

theorem F3S_of_at {G : Subgroup M} {u : M} {p : ℕ} (h : ∀ x, F3SAt G u x p) : F3S G u p :=
  fun x hx => h x hx

theorem F3SAt.conj {G : Subgroup M} {u x d : M} {p : ℕ} (h : F3SAt G u x p) (hd : d ∈ G)
    (hdu : u * d = d * u) : F3SAt G u (d * x * d⁻¹) p := by
  intro hx' hxo hxu hpg
  have hdu' : d⁻¹ * u = u * d⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hdu, mul_assoc, mul_inv_cancel, mul_one]
  have hxG : x ∈ G := by
    have := G.mul_mem (G.mul_mem (G.inv_mem hd) hx') hd
    rwa [show d⁻¹ * (d * x * d⁻¹) * d = x by group] at this
  have hord : orderOf x = p := by
    have := MulEquiv.orderOf_eq (MulAut.conj d) x
    simp only [MulAut.conj_apply] at this
    rw [← this, hxo]
  have hc : u * (d * x * d⁻¹) * u⁻¹ = d * (u * x * u⁻¹) * d⁻¹ := by
    have hdi : d⁻¹ * u⁻¹ = u⁻¹ * d⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hdu]
    calc u * (d * x * d⁻¹) * u⁻¹ = (u * d) * x * (d⁻¹ * u⁻¹) := by group
      _ = (d * u) * x * (u⁻¹ * d⁻¹) := by rw [hdu, hdi]
      _ = d * (u * x * u⁻¹) * d⁻¹ := by group
  have hxu' : u * x * u⁻¹ = x⁻¹ := by
    have e : d * (u * x * u⁻¹) * d⁻¹ = d * x⁻¹ * d⁻¹ := by rw [← hc, hxu]; group
    exact mul_left_cancel (mul_right_cancel e)
  refine h hxG hord hxu' ?_
  set S := {y : M | y ∈ G ∧ u * y = y * u ∧ Odd (orderOf y)}
  have hS : (Subgroup.closure S).map (MulAut.conj d).toMonoidHom ≤ Subgroup.closure S := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, ⟨hyG, hyu, hyo⟩, rfl⟩
    refine Subgroup.subset_closure ⟨?_, ?_, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact G.mul_mem (G.mul_mem hd hyG) (G.inv_mem hd)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc u * (d * y * d⁻¹) = (u * d) * y * d⁻¹ := by group
        _ = d * (u * y) * d⁻¹ := by rw [hdu]; group
        _ = d * (y * u) * d⁻¹ := by rw [hyu]
        _ = d * y * (u * d⁻¹) := by group
        _ = d * y * (d⁻¹ * u) := by rw [hdu']
        _ = d * y * d⁻¹ * u := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have := MulEquiv.orderOf_eq (MulAut.conj d) y
      simp only [MulAut.conj_apply] at this
      rw [this]
      exact hyo
  have hle : Subgroup.closure {w : M | ∃ c ∈ Subgroup.closure S, w = c * x * c⁻¹} ≤
      (Subgroup.closure {w : M | ∃ c ∈ Subgroup.closure S, w = c * (d * x * d⁻¹) * c⁻¹}).map
        (MulAut.conj d⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro w ⟨c, hc, rfl⟩
    refine ⟨d * c * d⁻¹ * (d * x * d⁻¹) * (d * c * d⁻¹)⁻¹, Subgroup.subset_closure
      ⟨d * c * d⁻¹, hS ⟨c, hc, rfl⟩, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact (hpg.map (MulAut.conj d⁻¹).toMonoidHom).to_le hle

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

end
