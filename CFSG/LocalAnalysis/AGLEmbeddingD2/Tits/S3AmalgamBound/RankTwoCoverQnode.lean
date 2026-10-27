module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.SteinbergBNPair
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

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem CFSG.AGLEmbeddingD2.McLaughlin.Lie

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem exists_qnode
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H) :
    ∃ Q : Fin D.rank → Subgroup K,
      (∀ i, borel D H ≤ Q i ∧ rankOne D.rootGroup i ≤ Q i ∧ Q i ≠ borel D H ∧
        ∀ A : Subgroup K, borel D H ≤ A → A ≤ Q i → A = borel D H ∨ A = Q i) ∧
      ∀ A : Subgroup K, borel D H ≤ A → A ≠ borel D H →
        (∀ A' : Subgroup K, borel D H ≤ A' → A' ≤ A → A' = borel D H ∨ A' = A) →
          ∃ k, A = Q k := by
  haveI := cartan_borel_weylN_normal hct hext
  have hBN := isBNPair_borel_weylN hct hext
  set B := borel D H with hB
  set N := weylN n H with hN
  have hemptyS : (∅ : Set (WeylGroup B N)) ⊆ simpleRefl D n H := Set.empty_subset _
  have hP0 : parabolic B N (∅ : Set (WeylGroup B N)) = B := by
    ext x
    rw [hBN.mem_parabolic_iff hemptyS]
    constructor
    · rintro ⟨w, hw, hx⟩
      rw [Subgroup.closure_empty, Subgroup.mem_bot] at hw
      rw [hw, mem_dc_one] at hx
      exact hx
    · intro hx
      exact ⟨1, one_mem _, mem_dc_one.2 hx⟩
  let s : Fin D.rank → WeylGroup B N := fun i => ((⟨n i, n_mem_weylN i⟩ : N) : WeylGroup B N)
  have hsS : ∀ i, s i ∈ simpleRefl D n H := fun i => ⟨i, rfl⟩
  have hJS : ∀ i, ({s i} : Set (WeylGroup B N)) ⊆ simpleRefl D n H := fun i =>
    Set.singleton_subset_iff.2 (hsS i)
  have hne : ∀ i, parabolic B N {s i} ≠ B := by
    intro i heq
    have : ({s i} : Set (WeylGroup B N)) = ∅ :=
      hBN.parabolic_injOn (hJS i) hemptyS (heq.trans hP0.symm)
    exact Set.singleton_ne_empty _ this
  refine ⟨fun i => parabolic B N {s i}, fun i => ⟨hBN.le_parabolic (hJS i), ?_, hne i, ?_⟩, ?_⟩
  ·
    have hnP : n i ∈ parabolic B N {s i} := by
      rw [hBN.mem_parabolic_iff (hJS i)]
      exact ⟨s i, Subgroup.subset_closure rfl,
        mem_dc_mk_iff.2 ⟨1, one_mem _, 1, one_mem _, by simp [hB]⟩⟩
    intro g hg
    rcases hext.rankOne_bruhat i g hg with ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
    · have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
        (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
      exact mul_mem (hBN.le_parabolic (hJS i) (iSup_le_borel (le_iSup H i hh)))
        (hBN.le_parabolic (hJS i) (rootGroup_le_borel hα (ht_single_pos i) hu))
    · have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
        (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
      exact mul_mem (mul_mem (mul_mem
        (hBN.le_parabolic (hJS i) (rootGroup_le_borel hα (ht_single_pos i) hu)) hnP)
        (hBN.le_parabolic (hJS i) (iSup_le_borel (le_iSup H i hh))))
        (hBN.le_parabolic (hJS i) (rootGroup_le_borel hα (ht_single_pos i) hv))
  · intro A hBA hAQ
    obtain ⟨J, ⟨hJ, hAJ⟩, -⟩ := hBN.existsUnique_parabolic hBA
    have hJs : J ⊆ {s i} := (hBN.parabolic_le_iff hJ (hJS i)).1 (hAJ ▸ hAQ)
    rcases Set.subset_singleton_iff_eq.1 hJs with h0 | h1
    · left
      rw [hAJ, h0, hP0]
    · right
      rw [hAJ, h1]
  · intro A hBA hAne hmin
    obtain ⟨J, ⟨hJ, hAJ⟩, -⟩ := hBN.existsUnique_parabolic hBA
    have hJne : J.Nonempty := by
      by_contra hJe
      rw [Set.not_nonempty_iff_eq_empty] at hJe
      exact hAne (by rw [hAJ, hJe, hP0])
    obtain ⟨t, ht⟩ := hJne
    obtain ⟨k, hk⟩ := hJ ht
    have hle : parabolic B N {s k} ≤ A := by
      rw [hAJ]
      refine (hBN.parabolic_le_iff (hJS k) hJ).2 ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have : s k = t := hk
      rw [this]; exact ht
    rcases hmin _ (hBN.le_parabolic (hJS k)) hle with h1 | h2
    · exact absurd h1 (hne k)
    · exact ⟨k, h2.symm⟩

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
