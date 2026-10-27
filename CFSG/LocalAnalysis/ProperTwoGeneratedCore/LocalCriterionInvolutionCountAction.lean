module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransportAction
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

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport

universe u v w

abbrev orderedDistinctPairs (Ω : Type v) : Type v :=
  {p : Ω × Ω // p.1 ≠ p.2}

theorem card_eq_card_mul_constant_fiber
    {A : Type u} {B : Type v} [Finite A] [Finite B]
    (f : A → B) (m : ℕ) (hf : ∀ b : B, Nat.card {a : A // f a = b} = m) :
    Nat.card A = Nat.card B * m := by
  classical
  let := Fintype.ofFinite B
  calc
    Nat.card A = Nat.card (Σ b : B, {a : A // f a = b}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ b : B, Nat.card {a : A // f a = b} := Nat.card_sigma
    _ = Nat.card B * m := by simp only [hf, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Nat.card_eq_fintype_card]

theorem orderedDistinctPairs_card (Ω : Type v) [Finite Ω] :
    Nat.card (orderedDistinctPairs Ω) = Nat.card Ω * (Nat.card Ω - 1) := by
  classical
  let := Fintype.ofFinite Ω
  let e : orderedDistinctPairs Ω ≃ Σ a : Ω, {b : Ω // a ≠ b} :=
    { toFun := fun p => ⟨p.val.1, p.val.2, p.property⟩
      invFun := fun p => ⟨(p.1, p.2.val), p.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc (a : Ω) : Nat.card {b : Ω // a ≠ b} = Nat.card Ω - 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype_eq'] using
      Fintype.card_subtype_compl (fun b : Ω => a = b)
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card]

variable {G : Type u} [Group G] {Ω : Type v} [MulAction Gᵐᵒᵖ Ω]

instance orderedDistinctPairsAction : MulAction Gᵐᵒᵖ (orderedDistinctPairs Ω) where
  smul g p := ⟨(g • p.val.1, g • p.val.2), fun heq =>
    p.property (by
      have hh := congrArg (fun a : Ω => g⁻¹ • a) heq
      simpa only [inv_smul_smul] using hh)⟩
  one_smul p := Subtype.ext (Prod.ext (one_smul _ _) (one_smul _ _))
  mul_smul g h p := Subtype.ext (Prod.ext (mul_smul _ _ _) (mul_smul _ _ _))

theorem ordered_pair_stabilizer (a b : Ω) (hab : a ≠ b) :
    (MulAction.stabilizer Gᵐᵒᵖ (⟨(a, b), hab⟩ : orderedDistinctPairs Ω)).unop =
      rightStabilizer a ⊓ rightStabilizer b := by
  ext g
  change (MulOpposite.op g • (⟨(a, b), hab⟩ : orderedDistinctPairs Ω) =
    (⟨(a, b), hab⟩ : orderedDistinctPairs Ω)) ↔
    rightAct a g = a ∧ rightAct b g = b
  constructor
  · intro hg
    have hh := congrArg Subtype.val hg
    exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
  · rintro ⟨ha, hb⟩
    exact Subtype.ext (Prod.ext ha hb)

theorem doubly_transitive_card [Finite G] [Finite Ω]
    (hdouble : ∀ a b c d : Ω, a ≠ b → c ≠ d →
      ∃ g : G, rightAct a g = c ∧ rightAct b g = d)
    (a b : Ω) (hab : a ≠ b) :
    Nat.card G = Nat.card Ω * (Nat.card Ω - 1) *
      Nat.card (rightStabilizer a ⊓ rightStabilizer b : Subgroup G) := by
  classical
  let p : orderedDistinctPairs Ω := ⟨(a, b), hab⟩
  let : MulAction.IsPretransitive Gᵐᵒᵖ (orderedDistinctPairs Ω) := ⟨by
    intro x y
    obtain ⟨g, hg1, hg2⟩ := hdouble x.val.1 x.val.2 y.val.1 y.val.2
      x.property y.property
    exact ⟨MulOpposite.op g, Subtype.ext (Prod.ext hg1 hg2)⟩⟩
  let : Finite Gᵐᵒᵖ := Finite.of_equiv G MulOpposite.opEquiv
  let := Fintype.ofFinite Gᵐᵒᵖ
  let := Fintype.ofFinite (MulAction.orbit Gᵐᵒᵖ p)
  let := Fintype.ofFinite (MulAction.stabilizer Gᵐᵒᵖ p)
  have horbit : MulAction.orbit Gᵐᵒᵖ p = Set.univ := MulAction.orbit_eq_univ Gᵐᵒᵖ p
  have hcard := MulAction.card_orbit_mul_card_stabilizer_eq_card_group Gᵐᵒᵖ p
  have hstab : Nat.card (MulAction.stabilizer Gᵐᵒᵖ p) =
      Nat.card (rightStabilizer a ⊓ rightStabilizer b : Subgroup G) := by
    rw [← ordered_pair_stabilizer a b hab]
    exact (Nat.card_congr
      ((MulAction.stabilizer Gᵐᵒᵖ p).unop.equivOp)).symm
  have hG : Nat.card Gᵐᵒᵖ = Nat.card G := Nat.card_congr MulOpposite.opEquiv.symm
  have hO : Nat.card (MulAction.orbit Gᵐᵒᵖ p) = Nat.card (orderedDistinctPairs Ω) := by
    rw [horbit]
    exact Nat.card_congr (Equiv.Set.univ _)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, hstab, hG, hO, orderedDistinctPairs_card] at hcard
  exact hcard.symm

end CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount
