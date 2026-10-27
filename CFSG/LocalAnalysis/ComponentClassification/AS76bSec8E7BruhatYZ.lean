module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Bruhat

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

@[expose] def e7BruhatLowY : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 1, 1, 2, 2, 2, 1], ![1, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 2, 1]]

@[expose] def e7BruhatHighY : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 2, 2, 3, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1]]

theorem e7BruhatY_check :
    (oddDerivE7YFrame ++ e7BruhatLowY ++ e7BruhatHighY).Nodup ∧
    (∀ β ∈ oddDerivE7YFrame ++ e7BruhatLowY ++ e7BruhatHighY,
      List.ofFn β ∈ Tag.artifactRoots .E7 ∧ 0 < height β ∧ 2 ≤ iform β oddDerivE7YFrame.sum) ∧
    (∀ ρ ∈ oddDerivE7YFrame ++ e7BruhatLowY, ∀ β ∈ oddDerivE7YFrame ++ e7BruhatHighY,
      0 < height (ρ - β) → List.ofFn (ρ - β) ∉ Tag.artifactRoots .E7) ∧
    (∀ i : Fin Tag.E7.rank, 0 ≤ iform (Pi.single i 1) oddDerivE7YFrame.sum) ∧
    tupleCheck oddDerivE7YFrame e7BruhatHighY = true ∧
    oddDerivE7YFrame.Nodup ∧ oddDerivE7YFrame.Pairwise fun a b => iform a b = 0 := by
  decide +kernel

theorem e7BruhatY_roots : ∀ k < Tag.E7.rootCertificate.roots.length,
    iform (Tag.E7.rootCertificate.root k) oddDerivE7YFrame.sum ≤ 3 ∧
      (2 ≤ iform (Tag.E7.rootCertificate.root k) oddDerivE7YFrame.sum →
        Tag.E7.rootCertificate.root k ∈ oddDerivE7YFrame ++ e7BruhatLowY ++ e7BruhatHighY) := by
  decide +kernel

@[expose] def e7BruhatLowZ : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 1, 2, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 1, 0], ![1, 1, 2, 2, 1, 1, 1], ![1, 1, 2, 2, 2, 1, 0],
    ![1, 1, 2, 2, 2, 1, 1], ![1, 1, 2, 3, 2, 1, 0]]

@[expose] def e7BruhatHighZ : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 1, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 2, 1, 1], ![1, 1, 2, 3, 3, 2, 1], ![1, 2, 2, 3, 2, 2, 1],
    ![1, 2, 2, 3, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1]]

theorem e7BruhatZ_check :
    (oddDerivE7ZFrame ++ e7BruhatLowZ ++ e7BruhatHighZ).Nodup ∧
    (∀ β ∈ oddDerivE7ZFrame ++ e7BruhatLowZ ++ e7BruhatHighZ,
      List.ofFn β ∈ Tag.artifactRoots .E7 ∧ 0 < height β ∧ 2 ≤ iform β oddDerivE7ZFrame.sum) ∧
    (∀ ρ ∈ oddDerivE7ZFrame ++ e7BruhatLowZ, ∀ β ∈ oddDerivE7ZFrame ++ e7BruhatHighZ,
      0 < height (ρ - β) → List.ofFn (ρ - β) ∉ Tag.artifactRoots .E7) ∧
    (∀ i : Fin Tag.E7.rank, 0 ≤ iform (Pi.single i 1) oddDerivE7ZFrame.sum) ∧
    tupleCheck oddDerivE7ZFrame e7BruhatHighZ = true ∧
    oddDerivE7ZFrame.Nodup ∧ oddDerivE7ZFrame.Pairwise fun a b => iform a b = 0 := by
  decide +kernel

theorem e7BruhatZ_roots : ∀ k < Tag.E7.rootCertificate.roots.length,
    iform (Tag.E7.rootCertificate.root k) oddDerivE7ZFrame.sum ≤ 3 ∧
      (2 ≤ iform (Tag.E7.rootCertificate.root k) oddDerivE7ZFrame.sum →
        Tag.E7.rootCertificate.root k ∈ oddDerivE7ZFrame ++ e7BruhatLowZ ++ e7BruhatHighZ) := by
  decide +kernel

theorem frameBruhatData_y : FrameBruhatData oddDerivE7YFrame e7BruhatLowY e7BruhatHighY := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := e7BruhatY_check
  exact FrameBruhatData.of_check h1 h2 h3 h4 h5 h6 h7 e7BruhatY_roots

theorem frameBruhatData_z : FrameBruhatData oddDerivE7ZFrame e7BruhatLowZ e7BruhatHighZ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := e7BruhatZ_check
  exact FrameBruhatData.of_check h1 h2 h3 h4 h5 h6 h7 e7BruhatZ_roots

variable
  {K : Type} [Field K]

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
