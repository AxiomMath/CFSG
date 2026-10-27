module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupTableBasic

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem involution_mem_of_out {N : Type*} [Group N] [Finite N] (H : Subgroup N) [H.Normal]
    (hC : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) (t : N) (ht : t * t = 1)
    (hOut : ∀ E : Subgroup (Outer ↥H), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 1) : t ∈ H := by
  have hfinAut : Finite (MulAut ↥H) :=
    Finite.of_injective (fun f : MulAut ↥H => (f : ↥H → ↥H)) DFunLike.coe_injective
  have : Finite (Outer ↥H) := inferInstanceAs
    (Finite (MulAut ↥H ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥H))
  let σ : MulAut ↥H := MulAut.conjNormal t
  have hσ : σ * σ = 1 := by
    change MulAut.conjNormal t * MulAut.conjNormal t = 1
    rw [← map_mul, ht, map_one]
  let e : Outer ↥H := QuotientGroup.mk σ
  have he : e * e = 1 := by
    change (QuotientGroup.mk σ : Outer ↥H) * QuotientGroup.mk σ = 1
    rw [← QuotientGroup.mk_mul, hσ]
    rfl
  have hE : ∀ x ∈ Subgroup.zpowers e, x * x = 1 := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, he, one_zpow]
  have hcard := hOut _ hE
  have hbot : Subgroup.zpowers e = ⊥ := by
    rw [Subgroup.eq_bot_iff_card]
    exact le_antisymm hcard Nat.card_pos
  have he1 : e = 1 := by
    have : e ∈ Subgroup.zpowers e := Subgroup.mem_zpowers e
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  have hin : σ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥H :=
    (QuotientGroup.eq_one_iff σ).mp he1
  obtain ⟨h, hh⟩ := hin
  have hcomm : (h : N)⁻¹ * t ∈ Subgroup.centralizer (H : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut ↥H => ((φ ⟨x, hx⟩ : ↥H) : N)) hh
    have hσx : ((σ ⟨x, hx⟩ : ↥H) : N) = t * x * t⁻¹ := by
      show (((MulAut.conjNormal t : MulAut ↥H) ⟨x, hx⟩ : ↥H) : N) = _
      rw [MulAut.conjNormal_apply]
    simp only [MulAut.conj_apply] at h1
    rw [hσx] at h1
    have h2 : (h : N) * x * (h : N)⁻¹ = t * x * t⁻¹ := h1
    calc x * ((h : N)⁻¹ * t) = (h : N)⁻¹ * ((h : N) * x * (h : N)⁻¹) * t := by group
      _ = (h : N)⁻¹ * (t * x * t⁻¹) * t := by rw [h2]
      _ = (h : N)⁻¹ * t * x := by group
  have h1 : (h : N)⁻¹ * t = 1 :=
    hC _ (fun y hy => (Subgroup.mem_centralizer_iff.mp hcomm y hy).symm)
  have : t = h := by
    have := congrArg (fun z => (h : N) * z) h1
    simpa using this
  rw [this]
  exact h.2

end CFSG.GH74.Generic.BProg.B2.PumpupTableBasic
