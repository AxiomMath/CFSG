module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

section Gen

variable {Y : Type} [Group Y]

theorem ka_conj_injective_of_center_bot (h : center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  have hc : y ∈ center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut Y => φ g) hy
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * y = (y * g * y⁻¹) * y := by rw [this]
      _ = y * g := by group
  rw [h] at hc
  exact hc

theorem ka_comm_mem_innSub (u : Y) (x : MulAut Y) :
    ⁅x, (MulAut.conj u : MulAut Y)⁆ ∈ innSub Y := by
  refine ⟨x u * u⁻¹, ?_⟩
  have h := conj_apply_aut x u
  show MulAut.conj (x u * u⁻¹) = x * MulAut.conj u * x⁻¹ * (MulAut.conj u)⁻¹
  rw [map_mul, map_inv, ← h]

omit [Group Y] in
theorem ka_congr_eq_mul_aut {Z : Type} [Group Z] (h f : MulAut Z) :
    MulAut.congr h f = h * f * h⁻¹ := by
  ext x
  simp [MulAut.congr_apply]

theorem ka_all_of_X0_bot [Finite Y] (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {α : MulAut Y} (L : Subgroup Y) (hLC : L ≤ fixSub α)
    (hLgen : Subgroup.closure {x : Y | x ∈ L ∧ Odd (orderOf x)} = L)
    (hX0 : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup Y, X ≤ fixSub α → IsPGroup p ↥X →
      (∀ l ∈ L, l ∈ normalizer (X : Set Y)) → X = ⊥)
    (hrig : KARigidTriv L) : KAAll α := by
  intro p hp hp2 P hP
  obtain ⟨hPp, hP1, hcomm, hnorm⟩ := hP
  exfalso
  have hLN := ka_normalizes_of_gen hnorm hLC hLgen
  have hX0p : IsPGroup p ↥(kaInner P) := kaInner_isPGroup hinj hPp
  have hX0bot : kaInner P = ⊥ :=
    hX0 p hp hp2 (kaInner P) (kaInner_le_fixSub hinj hcomm) hX0p fun l hl =>
      mem_normalizer_kaInner (hLN l hl)
  have hfix : ∀ e ∈ P, ∀ r ∈ L, e r = r := by
    intro e he r hr
    have hx : r * (e r)⁻¹ ∈ kaInner P := by
      rw [mem_kaInner, map_mul, map_inv]
      have h1 : e * MulAut.conj r * e⁻¹ = MulAut.conj (e r) := conj_apply_aut e r
      have h2 : MulAut.conj r * (MulAut.conj (e r))⁻¹ =
          (MulAut.conj r * e * (MulAut.conj r)⁻¹) * e⁻¹ := by
        rw [← h1]
        group
      rw [h2]
      exact P.mul_mem ((Subgroup.mem_normalizer_iff.1 (hLN r hr) e).1 he) (P.inv_mem he)
    rw [hX0bot, Subgroup.mem_bot, mul_inv_eq_one] at hx
    exact hx.symm
  apply hP1
  rw [eq_bot_iff]
  intro e he
  have h1 : e = 1 :=
    hrig p hp hp2 e (IsPGroup.to_le hPp ((Subgroup.zpowers_le).2 he)) (hfix e he)
  rw [h1]
  exact Subgroup.one_mem _

end Gen

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
