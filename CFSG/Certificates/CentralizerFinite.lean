module

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
public import Mathlib.GroupTheory.Schreier
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

public section

namespace CFSG.Certificates

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutatorElement_mul_center_left {z : G} (hz : z ∈ center G) (g h : G) :
    ⁅g * z, h⁆ = ⁅g, h⁆ := by
  have hzh : z * h = h * z := (mem_center_iff.mp hz h).symm
  rw [commutatorElement_def, commutatorElement_def, mul_assoc g z h, hzh]
  group

theorem commutatorElement_mul_center_right {z : G} (hz : z ∈ center G) (g h : G) :
    ⁅g, h * z⁆ = ⁅g, h⁆ := by
  have hzg : z * g = g * z := (mem_center_iff.mp hz g).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  have : g * (h * z) * g⁻¹ * (z⁻¹ * h⁻¹) = g * h * (z * g⁻¹) * z⁻¹ * h⁻¹ := by group
  have hz' : z * g⁻¹ = g⁻¹ * z := by
    have := (mem_center_iff.mp hz g⁻¹).symm
    exact this
  rw [this, hz']
  group

theorem finite_commutatorSet_of_finiteIndex_center [(center G).FiniteIndex] :
    Finite (commutatorSet G) := by
  have : Finite (G ⧸ center G) := Subgroup.finite_quotient_of_finiteIndex
  refine Set.Finite.to_subtype (Set.Finite.subset
    (Set.finite_range (fun p : (G ⧸ center G) × (G ⧸ center G) => ⁅p.1.out, p.2.out⁆)) ?_)
  rintro _ ⟨g, h, rfl⟩
  refine ⟨((g : G ⧸ center G), (h : G ⧸ center G)), ?_⟩
  obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (center G) g
  obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (center G) h
  simp only
  rw [hz, hw, commutatorElement_mul_center_left z.2, commutatorElement_mul_center_right w.2]

theorem finite_of_centralizer_finiteIndex (a : G) (H : Subgroup G)
    (hH : H ≤ centralizer {a}) [H.FiniteIndex] (hN : normalClosure {a} = ⊤)
    (hP : commutator G = ⊤) : Finite G := by
  set C := centralizer ({a} : Set G)
  have hC : C.FiniteIndex := Subgroup.finiteIndex_of_le hH
  set S : Set G := Set.range fun g : G => g * a * g⁻¹
  have hS : S.Finite := by
    have : Finite (G ⧸ C) := Subgroup.finite_quotient_of_finiteIndex
    refine Set.Finite.subset (Set.finite_range fun q : G ⧸ C => q.out * a * q.out⁻¹) ?_
    rintro _ ⟨g, rfl⟩
    refine ⟨(g : G ⧸ C), ?_⟩
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul C g
    simp only
    rw [hc]
    have hca : (c : G) * a = a * c := mem_centralizer_singleton_iff.mp c.2
    rw [mul_inv_rev, show g * ↑c * a * ((↑c)⁻¹ * g⁻¹) = g * (↑c * a * (↑c)⁻¹) * g⁻¹ by group,
      hca, mul_inv_cancel_right]
  have hfin : Finite S := hS.to_subtype
  set Z' := ⨅ x : S, centralizer ({(x : G)} : Set G)
  have hZ' : Z'.FiniteIndex := by
    refine Subgroup.finiteIndex_iInf fun x => ?_
    obtain ⟨g, hg⟩ := x.2
    have : centralizer ({(x : G)} : Set G) = C.comap (MulAut.conj g⁻¹).toMonoidHom := by
      ext y
      simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        mem_centralizer_singleton_iff, C, ← hg]
      constructor
      · intro h
        calc g⁻¹ * y * g * a = g⁻¹ * (y * (g * a * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * a * g⁻¹) * y) * g := by rw [h]
          _ = a * (g⁻¹ * y * g) := by group
      · intro h
        calc y * (g * a * g⁻¹) = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by group
          _ = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
          _ = g * a * g⁻¹ * y := by group
    rw [this]
    refine ⟨?_⟩
    rw [Subgroup.index_comap_of_surjective C (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).surjective]
    exact hC.index_ne_zero
  have hZc : Z' ≤ center G := by
    intro x hx
    rw [mem_center_iff]
    intro y
    have hy : y ∈ normalClosure ({a} : Set G) := hN ▸ mem_top y
    have hcl : normalClosure ({a} : Set G) ≤ centralizer ({x} : Set G) := by
      rw [normalClosure, Subgroup.closure_le]
      intro z hz
      rw [Group.mem_conjugatesOfSet_iff] at hz
      obtain ⟨a', ha', hconj⟩ := hz
      rw [Set.mem_singleton_iff] at ha'
      subst ha'
      obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
      have := (mem_iInf.mp hx) ⟨g * a' * g⁻¹, g, rfl⟩
      rw [mem_centralizer_singleton_iff] at this
      exact mem_centralizer_singleton_iff.mpr this.symm
    exact mem_centralizer_singleton_iff.mp (hcl hy)
  have hZ : (center G).FiniteIndex := Subgroup.finiteIndex_of_le hZc
  have := finite_commutatorSet_of_finiteIndex_center (G := G)
  have hfc : Finite (_root_.commutator G) := inferInstance
  rw [hP] at hfc
  exact Finite.of_equiv _ Subgroup.topEquiv.toEquiv

end CFSG.Certificates
