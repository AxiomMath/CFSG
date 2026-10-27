module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω]

theorem pair_stabilizer_map_conj
    (a b a₀ b₀ : Ω) (g : G) (ha : g • a = a₀) (hb : g • b = b₀) :
    (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b).map
        (MulAut.conj g).toMonoidHom =
      MulAction.stabilizer G a₀ ⊓ MulAction.stabilizer G b₀ := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, ha, hb]

theorem full_pair_cyclic_card_and_inversion_of_standard_pair
    (hdouble : MulAction.IsMultiplyPretransitive G Ω 2)
    (a₀ b₀ : Ω) (h₀ : a₀ ≠ b₀) (w : G)
    (hwa : w • a₀ = b₀) (hwb : w • b₀ = a₀)
    (T₀ : Subgroup G)
    (hT₀ : (T₀ : Set G) = {x | x • a₀ = a₀ ∧ x • b₀ = b₀})
    (hcyclic : IsCyclic T₀)
    (hinv : ∀ x ∈ T₀, rightConjugateElem x w = x⁻¹)
    (a b : Ω) (hab : a ≠ b) (t : G)
    (hta : t • a = b) (htb : t • b = a) :
    let T := MulAction.stabilizer G a ⊓ MulAction.stabilizer G b
    IsCyclic T ∧ Nat.card T = Nat.card T₀ ∧
      ∀ x ∈ T, rightConjugateElem x t = x⁻¹ := by
  have hTset : T₀ = MulAction.stabilizer G a₀ ⊓ MulAction.stabilizer G b₀ := by
    ext x
    change x ∈ T₀ ↔ x • a₀ = a₀ ∧ x • b₀ = b₀
    exact Set.ext_iff.mp hT₀ x
  obtain ⟨g, hga, hgb⟩ := (MulAction.is_two_pretransitive_iff.mp hdouble) hab h₀
  let T := MulAction.stabilizer G a ⊓ MulAction.stabilizer G b
  let c := MulAut.conj g
  have hmap : T.map c.toMonoidHom = T₀ :=
    (pair_stabilizer_map_conj a b a₀ b₀ g hga hgb).trans hTset.symm
  let e : T ≃* T₀ :=
    (T.equivMapOfInjective c.toMonoidHom c.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hfix (x : G) (z : Ω) : (c x) • (g • z) = g • (x • z) := by
    simp only [c, MulAut.conj_apply, mul_smul, inv_smul_smul]
  let t₀ := c t
  have ht₀a : t₀ • a₀ = b₀ := by rw [← hga, hfix, hta, hgb]
  have ht₀b : t₀ • b₀ = a₀ := by rw [← hgb, hfix, htb, hga]
  have hwiA : w⁻¹ • a₀ = b₀ := by
    rw [← hwb, inv_smul_smul]
  have hwiB : w⁻¹ • b₀ = a₀ := by
    rw [← hwa, inv_smul_smul]
  let d := t₀ * w⁻¹
  have hd : d ∈ T₀ := by
    rw [hTset]
    exact ⟨by change (t₀ * w⁻¹) • a₀ = a₀; rw [mul_smul, hwiA, ht₀b],
      by change (t₀ * w⁻¹) • b₀ = b₀; rw [mul_smul, hwiB, ht₀a]⟩
  have ht₀eq : t₀ = d * w := by dsimp [d]; group
  refine ⟨e.isCyclic.mpr hcyclic, Nat.card_congr e.toEquiv, ?_⟩
  intro x hx
  have hcx : c x ∈ T₀ := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem c.toMonoidHom hx
  let : IsCyclic T₀ := hcyclic
  have hccomm : d⁻¹ * c x = c x * d⁻¹ :=
    setLike_mul_comm (T₀.inv_mem hd) hcx
  have heq : rightConjugateElem (c x) t₀ = (c x)⁻¹ := by
    rw [rightConjugateElem, ht₀eq]
    calc
      (d * w)⁻¹ * c x * (d * w) = w⁻¹ * (d⁻¹ * c x) * d * w := by group
      _ = w⁻¹ * (c x * d⁻¹) * d * w := by rw [hccomm]
      _ = rightConjugateElem (c x) w := by dsimp [rightConjugateElem]; group
      _ = (c x)⁻¹ := hinv _ hcx
  apply c.injective
  simpa only [rightConjugateElem, map_mul, map_inv, t₀] using heq

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
