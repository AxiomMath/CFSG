module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GroupTheory

universe u

variable {G : Type u} [Group G]

noncomputable def conjClassCommutingEquiv (d₀ u g : G) :
    {d : G // IsConj d₀ d ∧ Commute d u} ≃
      {d : G // IsConj d₀ d ∧ Commute d (g * u * g⁻¹)} where
  toFun d :=
    ⟨g * d.1 * g⁻¹,
      ⟨d.2.1.trans (isConj_iff.mpr ⟨g, rfl⟩),
        (Commute.conj_iff g).mpr d.2.2⟩⟩
  invFun d :=
    ⟨g⁻¹ * d.1 * g,
      ⟨d.2.1.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩),
        (by
          have h : Commute (g⁻¹ * d.1 * g) (g⁻¹ * (g * u * g⁻¹) * g) := by
            have h0 := (Commute.conj_iff g⁻¹).mpr d.2.2
            simpa using h0
          have hgroup : g⁻¹ * (g * u * g⁻¹) * g = u := by group
          rw [hgroup] at h
          exact h)⟩⟩
  left_inv d := by
    apply Subtype.ext
    show g⁻¹ * (g * d.1 * g⁻¹) * g = d.1
    group
  right_inv d := by
    apply Subtype.ext
    show g * (g⁻¹ * d.1 * g) * g⁻¹ = d.1
    group

theorem natCard_commuting_conj (d₀ u g : G) [Finite G] :
    Nat.card {d : G // IsConj d₀ d ∧ Commute d u} =
      Nat.card {d : G // IsConj d₀ d ∧ Commute d (g * u * g⁻¹)} :=
  Nat.card_congr (conjClassCommutingEquiv d₀ u g)

theorem natCard_commuting_conjClass_eq {d₀ u v : G} [Finite G]
    (hu : IsConj d₀ u) (hv : IsConj d₀ v) :
    Nat.card {d : G // IsConj d₀ d ∧ Commute d u} =
      Nat.card {d : G // IsConj d₀ d ∧ Commute d v} := by
  have huv : IsConj u v := (isConj_comm.mpr hu).trans hv
  obtain ⟨g, hg⟩ := isConj_iff.mp huv
  rw [← hg]
  exact natCard_commuting_conj d₀ u g

noncomputable def mulEquivCommutingEquiv {H : Type*} [Group H] (e : G ≃* H)
    (C : Set G) (u : G) :
    {d : G // d ∈ C ∧ Commute d u} ≃
      {d : H // d ∈ e '' C ∧ Commute d (e u)} where
  toFun d :=
    ⟨e d.1, ⟨⟨d.1, d.2.1, rfl⟩, Commute.map d.2.2 e.toMonoidHom⟩⟩
  invFun d := by
    refine ⟨e.symm d.1, ⟨?_, ?_⟩⟩
    · obtain ⟨c, hc, hcd⟩ := d.2.1
      rwa [← hcd, e.symm_apply_apply]
    · have h := Commute.map d.2.2 e.symm.toMonoidHom
      simpa using h
  left_inv d := by
    apply Subtype.ext
    simp
  right_inv d := by
    apply Subtype.ext
    simp

theorem natCard_commuting_mulEquiv {H : Type*} [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (C : Set G) (u : G) :
    Nat.card {d : G // d ∈ C ∧ Commute d u} =
      Nat.card {d : H // d ∈ e '' C ∧ Commute d (e u)} :=
  Nat.card_congr (mulEquivCommutingEquiv e C u)

end CFSG.GroupTheory
