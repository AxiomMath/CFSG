module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusDefs
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
public import Mathlib.Order.CompletePartialOrder
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
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

open scoped commutatorElement

variable {G G' : Type} [Group G] [Group G']

theorem map_finset_sup [DecidableEq (Subgroup G')] (e : G →* G') (S : Finset (Subgroup G)) :
    (S.sup id).map e = (S.image (Subgroup.map e)).sup id := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert F S hF ih =>
    rw [Finset.sup_insert, Subgroup.map_sup, ih, Finset.image_insert, Finset.sup_insert]
    rfl

theorem IsCommProd.map_hom {Q : Type} [Group Q] {N : Subgroup G} (h : IsCommProd Q N)
    (f : G →* G') (hf : Function.Injective f) : IsCommProd Q (N.map f) := by
  classical
  obtain ⟨S, hS, hc, hsup⟩ := h
  have hinj : Function.Injective (Subgroup.map f) := Subgroup.map_injective hf
  refine ⟨S.image (Subgroup.map f), ?_, ?_, ?_⟩
  · intro F hF
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hF
    exact ⟨(Subgroup.equivMapOfInjective A f hf).symm.trans (hS A hA).some⟩
  · intro F hF F' hF' hne
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hF)
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hF')
    have hAB : A ≠ B := fun h => hne (by rw [h])
    rw [← Subgroup.map_commutator, hc (Finset.mem_coe.mpr hA) (Finset.mem_coe.mpr hB) hAB,
      Subgroup.map_bot]
  · rw [← map_finset_sup f S, hsup]

theorem IsCommProd.map {Q : Type} [Group Q] {N : Subgroup G} (h : IsCommProd Q N) (e : G ≃* G') :
    IsCommProd Q (N.map e.toMonoidHom) :=
  h.map_hom e.toMonoidHom e.injective

variable (G) in
theorem sSup_map_equiv (P : ∀ (X : Type) [Group X], Subgroup X → Prop)
    (hP : ∀ (X Y : Type) [Group X] [Group Y] (e : X ≃* Y) (N : Subgroup X), P X N →
      P Y (N.map e.toMonoidHom)) (e : G ≃* G') :
    (sSup {N : Subgroup G | P G N}).map e.toMonoidHom = sSup {N : Subgroup G' | P G' N} := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun N hN => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (hP G G' e N hN)
  · refine sSup_le fun N hN => ?_
    have h1 : P G (N.map e.symm.toMonoidHom) := hP G' G e.symm N hN
    have h2 : N = (N.map e.symm.toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map]
      have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G' := by
        ext x
        simp
      rw [this, Subgroup.map_id]
    rw [h2]
    exact Subgroup.map_mono (le_sSup h1)

theorem NOne_map (e : G ≃* G') : (NOne G).map e.toMonoidHom = NOne G' :=
  sSup_map_equiv G (fun _ _ N => N.Normal ∧ IsCommProd SL23 N)
    (fun _ _ _ _ e _ hN => ⟨hN.1.map e.toMonoidHom e.surjective, hN.2.map e⟩) e

theorem NTwo_map (e : G ≃* G') : (NTwo G).map e.toMonoidHom = NTwo G' :=
  sSup_map_equiv G (fun _ _ N => N.Normal ∧ IsCommProd A4 N)
    (fun _ _ _ _ e _ hN => ⟨hN.1.map e.toMonoidHom e.surjective, hN.2.map e⟩) e

theorem layer_map_equiv (e : G ≃* G') : (layer G).map e.toMonoidHom = layer G' :=
  CFSG.WholeGroup.layer_map_mulEquiv e

theorem EPlus_map (e : G ≃* G') : (EPlus G).map e.toMonoidHom = EPlus G' := by
  unfold EPlus
  rw [Subgroup.map_sup, Subgroup.map_sup, NOne_map, NTwo_map, layer_map_equiv]

theorem NOne_map_aut (φ : MulAut G) : (NOne G).map φ.toMonoidHom = NOne G := NOne_map φ

theorem NTwo_map_aut (φ : MulAut G) : (NTwo G).map φ.toMonoidHom = NTwo G := NTwo_map φ

theorem EPlus_map_aut (φ : MulAut G) : (EPlus G).map φ.toMonoidHom = EPlus G := EPlus_map φ

end CFSG.OddStandard.Solomon75
