module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerCode
import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup CFSG.SCATWreath

variable {G : Type*} [Group G] {K : Subgroup G} {y : G}

theorem inv_conj_mem (hyN : y ∈ normalizer (K : Set G)) {k : G} (hk : k ∈ K) :
    y⁻¹ * k * y ∈ K := by
  have h := (mem_normalizer_iff.1 hyN (y⁻¹ * k * y)).2
  apply h
  rwa [show y * (y⁻¹ * k * y) * y⁻¹ = k by group]

theorem conj_mem_of_norm (hyN : y ∈ normalizer (K : Set G)) {k : G} (hk : k ∈ K) :
    y * k * y⁻¹ ∈ K :=
  (mem_normalizer_iff.1 hyN k).1 hk

variable {n : ℕ} {mul : ℕ → ℕ → ℕ} {dec : ℕ → G}

end CFSG.OddStandard.AltStdSmall4.Tower
