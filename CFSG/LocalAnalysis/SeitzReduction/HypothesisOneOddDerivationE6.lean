module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivation

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def oddDerivE6YFrame : List (Fin Tag.E6.rank → ℤ) :=
  [![1, 1, 2, 2, 1, 1], ![1, 1, 1, 2, 2, 1]]

@[expose] def oddDerivE6YDeriv :
    List ((Fin Tag.E6.rank → ℤ) × (Fin Tag.E6.rank → ℤ) × (Fin Tag.E6.rank → ℤ)) := [
  (![0, 0, 0, 0, 0, 1], ![0, 0, 1, 1, 1, 1], ![0, 0, -1, -1, -1, 0]),
  (![0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, -1, 0, 0, 0, 0]),
  (![0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 0, 0, -1, 0, 0]),
  (![1, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 1, 0], ![0, 0, -1, -1, -1, 0]),
  (![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 1, 1], ![0, 0, 0, -1, 0, 0]),
  (![0, 1, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0]),
  (![1, 0, 1, 0, 0, 0], ![1, 0, 1, 1, 0, 0], ![0, 0, 0, -1, 0, 0]),
  (![0, 0, 0, 1, 1, 1], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 1]),
  (![0, 0, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 0], ![0, -1, 0, 0, 0, 0]),
  (![1, 0, 1, 1, 0, 0], ![0, 0, 0, 1, 0, 0], ![1, 0, 1, 0, 0, 0]),
  (![0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 1], ![0, 0, 1, 1, 1, 0]),
  (![0, 1, 0, 1, 1, 1], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 1]),
  (![0, 1, 1, 1, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0]),
  (![1, 0, 1, 1, 1, 0], ![1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0]),
  (![1, 1, 1, 1, 0, 0], ![0, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0]),
  (![0, 1, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 1], ![0, 1, 1, 1, 1, 0]),
  (![0, 1, 1, 2, 1, 0], ![0, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 1, 0]),
  (![1, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 1], ![1, 0, 1, 1, 1, 0]),
  (![1, 1, 1, 1, 1, 0], ![0, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 1, 0]),
  (![0, 1, 1, 2, 1, 1], ![0, 0, 0, 0, 0, 1], ![0, 1, 1, 2, 1, 0]),
  (![1, 1, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 0]),
  (![1, 1, 1, 2, 1, 0], ![0, 0, 0, 1, 0, 0], ![1, 1, 1, 1, 1, 0]),
  (![0, 1, 1, 2, 2, 1], ![0, 0, 0, 0, 1, 1], ![0, 1, 1, 2, 1, 0]),
  (![1, 1, 1, 2, 1, 1], ![0, 0, 0, 0, 0, 1], ![1, 1, 1, 2, 1, 0]),
  (![1, 1, 2, 2, 1, 0], ![1, 0, 1, 0, 0, 0], ![0, 1, 1, 2, 1, 0]),
  (![1, 1, 1, 2, 2, 1], ![1, 0, 0, 0, 0, 0], ![0, 1, 1, 2, 2, 1]),
  (![1, 1, 2, 2, 1, 1], ![0, 0, 0, 0, 0, 1], ![1, 1, 2, 2, 1, 0]),
  (![1, 1, 2, 2, 2, 1], ![0, 0, 0, 0, 1, 1], ![1, 1, 2, 2, 1, 0]),
  (![1, 1, 2, 3, 2, 1], ![0, 0, 0, 1, 0, 0], ![1, 1, 2, 2, 2, 1]),
  (![1, 2, 2, 3, 2, 1], ![0, 1, 0, 0, 0, 0], ![1, 1, 2, 3, 2, 1])]

@[expose] def oddDerivE6YPerp : List (Fin Tag.E6.rank → ℤ) := [
  ![0, -1, -1, -2, -1, 0], ![0, -1, -1, -1, -1, 0], ![0, 0, -1, -1, -1, 0], ![0, -1, 0, -1, 0, 0],
  ![0, -1, 0, 0, 0, 0], ![0, 0, 0, -1, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0],
  ![0, 1, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 0]]

theorem oddDerivE6Y_check :
    oddDerivCheck .E6 4 oddDerivE6YFrame (oddDerivE6YDeriv.map Prod.fst) oddDerivE6YPerp oddDerivE6YDeriv = true := by
  decide +kernel

@[expose] def oddDerivE6ZFrame : List (Fin Tag.E6.rank → ℤ) :=
  [![0, 1, 1, 2, 2, 1], ![1, 1, 1, 2, 1, 1], ![1, 1, 2, 2, 1, 0]]

@[expose] def oddDerivE6ZDeriv :
    List ((Fin Tag.E6.rank → ℤ) × (Fin Tag.E6.rank → ℤ) × (Fin Tag.E6.rank → ℤ)) := [
  (![0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, -1, 0, 0, 0, 0]),
  (![0, 0, 0, 1, 1, 0], ![0, 1, 0, 1, 1, 0], ![0, -1, 0, 0, 0, 0]),
  (![0, 0, 1, 1, 0, 0], ![0, 1, 1, 1, 0, 0], ![0, -1, 0, 0, 0, 0]),
  (![0, 1, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0]),
  (![0, 1, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 0], ![0, 1, 0, 0, 0, 0]),
  (![0, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 0], ![0, 1, 0, 0, 0, 0]),
  (![0, 0, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 1], ![0, -1, 0, 0, 0, 0]),
  (![1, 0, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 0], ![0, -1, 0, 0, 0, 0]),
  (![0, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1], ![0, 1, 0, 0, 0, 0]),
  (![0, 1, 1, 2, 1, 0], ![0, 0, 0, 1, 1, 0], ![0, 1, 1, 1, 0, 0]),
  (![1, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![0, -1, 0, 0, 0, 0]),
  (![1, 1, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 0], ![0, 1, 0, 0, 0, 0]),
  (![0, 1, 1, 2, 1, 1], ![0, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 1, 1]),
  (![1, 1, 1, 1, 1, 1], ![1, 0, 1, 1, 1, 1], ![0, 1, 0, 0, 0, 0]),
  (![1, 1, 1, 2, 1, 0], ![0, 0, 0, 1, 0, 0], ![1, 1, 1, 1, 1, 0]),
  (![0, 1, 1, 2, 2, 1], ![0, 0, 0, 1, 1, 0], ![0, 1, 1, 1, 1, 1]),
  (![1, 1, 1, 2, 1, 1], ![0, 0, 0, 1, 0, 0], ![1, 1, 1, 1, 1, 1]),
  (![1, 1, 2, 2, 1, 0], ![0, 0, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 0]),
  (![1, 1, 1, 2, 2, 1], ![0, 0, 0, 1, 1, 0], ![1, 1, 1, 1, 1, 1]),
  (![1, 1, 2, 2, 1, 1], ![0, 0, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 1]),
  (![1, 1, 2, 2, 2, 1], ![0, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 0]),
  (![1, 1, 2, 3, 2, 1], ![0, 0, 0, 1, 0, 0], ![1, 1, 2, 2, 2, 1]),
  (![1, 2, 2, 3, 2, 1], ![0, 1, 0, 1, 0, 0], ![1, 1, 2, 2, 2, 1])]

@[expose] def oddDerivE6ZPerp : List (Fin Tag.E6.rank → ℤ) := [
  ![0, -1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]

theorem oddDerivE6Z_check :
    oddDerivCheck .E6 5 oddDerivE6ZFrame (oddDerivE6ZDeriv.map Prod.fst) oddDerivE6ZPerp oddDerivE6ZDeriv = true := by
  decide +kernel


variable {K : Type} [Field K]

theorem rootSpan_le_closure_odd_E6_y [Finite K] [CharP K 2] {t : adjointGroup .E6 K}
    (ht : (t : ModGL .E6 K) = (oddDerivE6YFrame.map fun σ => pinnedX .E6 K σ 1).prod) :
    ∀ x : adjointGroup .E6 K, (x : ModGL .E6 K) ∈ rootSpan .E6 K {γ | γ ∈ oddDerivE6YDeriv.map Prod.fst} →
      x ∈ closure {c : adjointGroup .E6 K | c * t = t * c ∧ Odd (orderOf c)} := by
  have h := oddDerivE6Y_check
  simp only [oddDerivCheck, Bool.and_eq_true] at h
  exact rootSpan_le_closure_odd_of_oddDerivFrame _ _ ht h.1.1.1 (oddDeriv_cov_map_fst _) h.1.2

theorem heightSeries_le_closure_odd_E6_y [Finite K] [CharP K 2] {t : adjointGroup .E6 K}
    (ht : (t : ModGL .E6 K) = (oddDerivE6YFrame.map fun σ => pinnedX .E6 K σ 1).prod) :
    ∀ x : adjointGroup .E6 K, (x : ModGL .E6 K) ∈ heightSeries .E6 K 4 →
      x ∈ closure {c : adjointGroup .E6 K | c * t = t * c ∧ Odd (orderOf c)} :=
  heightSeries_le_closure_odd_of_oddDerivCheck _ _ ht oddDerivE6Y_check

theorem rootSpan_le_closure_odd_E6_z [Finite K] [CharP K 2] {t : adjointGroup .E6 K}
    (ht : (t : ModGL .E6 K) = (oddDerivE6ZFrame.map fun σ => pinnedX .E6 K σ 1).prod) :
    ∀ x : adjointGroup .E6 K, (x : ModGL .E6 K) ∈ rootSpan .E6 K {γ | γ ∈ oddDerivE6ZDeriv.map Prod.fst} →
      x ∈ closure {c : adjointGroup .E6 K | c * t = t * c ∧ Odd (orderOf c)} := by
  have h := oddDerivE6Z_check
  simp only [oddDerivCheck, Bool.and_eq_true] at h
  exact rootSpan_le_closure_odd_of_oddDerivFrame _ _ ht h.1.1.1 (oddDeriv_cov_map_fst _) h.1.2

theorem heightSeries_le_closure_odd_E6_z [Finite K] [CharP K 2] {t : adjointGroup .E6 K}
    (ht : (t : ModGL .E6 K) = (oddDerivE6ZFrame.map fun σ => pinnedX .E6 K σ 1).prod) :
    ∀ x : adjointGroup .E6 K, (x : ModGL .E6 K) ∈ heightSeries .E6 K 5 →
      x ∈ closure {c : adjointGroup .E6 K | c * t = t * c ∧ Odd (orderOf c)} :=
  heightSeries_le_closure_odd_of_oddDerivCheck _ _ ht oddDerivE6Z_check
end CFSG.SeitzReduction
