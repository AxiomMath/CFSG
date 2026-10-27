module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeDefs
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.M11Three
import CFSG.Sporadic.Bridge.M11
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IL32Inv
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree

section


theorem not_threeAutFour_m11 :
    ¬ ThreeAutFour (TauCeti.CFSGIndex.sporadic .M11).Group := by
  intro h
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have hN : ThreeAutFour ↥CFSG.Blueprint.NativeSporadic.M11 :=
    ThreeAutFour.of_injective e.toMonoidHom e.injective h
  obtain ⟨R, hRG, hRcard, -, -, -, t, ht, h4, -, -⟩ :=
    CFSG.AGLEmbeddingD2.m11_three_localData
  let G := CFSG.Blueprint.NativeSporadic.M11
  let y : ↥G := ⟨t, ht.2⟩
  let E : Subgroup ↥G := R.subgroupOf G
  have hEcard : Nat.card E = 3 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRG).toEquiv, hRcard]
  have hE : IsPGroup 3 E := IsPGroup.of_card (n := 2) hEcard
  have htE : y ∈ Subgroup.normalizer (E : Set ↥G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hRG]
    exact Subgroup.mem_subgroupOf.mpr ht.1
  obtain ⟨k, hk⟩ := hN E hE y htE
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card E := by rw [hEcard]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := E) 3 hdvd
  have hxord : orderOf (x : ↥G) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hx3 : (x : ↥G) ^ 3 = 1 := by
    simpa [hxord] using pow_orderOf_eq_one (x : ↥G)
  have hx2 : (x : ↥G) ^ 2 = (x : ↥G)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    simpa using hx3
  have hconj4 : y ^ 4 * (x : ↥G) * (y ^ 4)⁻¹ = (x : ↥G) ^ 2 := by
    apply Subtype.ext
    simpa using h4 ((x : ↥G) : Equiv.Perm (Fin 11)) (Subgroup.mem_subgroupOf.mp x.2)
  have hconj4inv : y ^ 4 * (x : ↥G) * (y ^ 4)⁻¹ = (x : ↥G)⁻¹ := by
    rw [hconj4, hx2]
  have hpow_inv : y ^ (4 * 3 ^ k) * (x : ↥G) * (y ^ (4 * 3 ^ k))⁻¹ =
      (x : ↥G)⁻¹ := by
    have hodd : Odd (3 ^ k) := Odd.pow (by norm_num : Odd 3)
    have h :=
      CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I.conj_pow_odd_eq_inv
        (G := ↥G) hconj4inv hodd
    simpa only [pow_mul] using h
  have hcent : y ^ (4 * 3 ^ k) * (x : ↥G) * (y ^ (4 * 3 ^ k))⁻¹ = (x : ↥G) := by
    rw [hk x x.2, mul_assoc, mul_inv_cancel, mul_one]
  have hxeq : (x : ↥G) = (x : ↥G)⁻¹ := hcent.symm.trans hpow_inv
  have hx2one : (x : ↥G) ^ 2 = 1 := by
    simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp hxeq)
  have hdvd2 : orderOf (x : ↥G) ∣ 2 := orderOf_dvd_of_pow_eq_one hx2one
  rw [hxord] at hdvd2
  norm_num at hdvd2

end

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree
