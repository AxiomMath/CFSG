module

public import Certificates.Data.Kernel.Spor.M11
public import CFSG.Monster.B.Mathieu.Order
import CFSG.Certificates.Kernel.Spor.PK.M11
public import CFSG.Sporadic.Schreier.Enumeration
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KS.M11

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu

@[expose] def shiftLabel (z : Int) : Int := if 0 < z then z + 2 else z - 2

theorem m11K_sound {gA gB : Equiv.Perm (Fin 11)} {words : List (List Int)}
    {hbs : (#v[0, 1, 2, 3] : Vector (Fin 11) 4).toList.Nodup}
    {tA tB : List Nat} {W : List (List Int)} (hA : tA = imageList gA)
    (hB : tB = imageList gB) (hW : W = [[1], [2]] ++ words.map (List.map shiftLabel))
    {XL YL : List (Nat × Nat)} (hbase : m11Base tA tB W = true)
    (hX : m11Col tA tB W 1 = packPairs XL) (hY : m11Col tA tB W 3 = packPairs YL)
    (hXb : pairsBdd 44 XL = true) (hYb : pairsBdd 44 YL = true) :
    let Q := certificate (by decide) [gA, gB] words #v[0, 1, 2, 3] hbs
    let E := (enumeration Q).map tab
    (Q.check = true ∧ Q.orderCertificate = 7920)
    ∧ (orderIs gA 2 = true ∧ orderIs gB 4 = true ∧ orderIs (gA * gB) 11 = true ∧
      orderIs (gA * gB * gA⁻¹ * gB⁻¹) 6 = true ∧
      (E.filter (orderIs · 2)).length = XL.length ∧
      (E.filter (orderIs · 4)).length = YL.length ∧
      ((E.filter (orderIs · 2) ×ˢ E.filter (orderIs · 4)).filter
        fun q => orderIs (q.1 * q.2) 11 && orderIs (q.1 * q.2 * q.1⁻¹ * q.2⁻¹) 6).length =
        pairCntL XL YL) :=
  CFSG.KS.PK.m11K_sound' (sh := shiftLabel) (fun _ => rfl) hA hB hW hbase hX hY hXb hYb

end CFSG.KS.M11

end
