module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherParabolicData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) (r ε : ℕ)

abbrev isoStabilizer (W : Submodule K (HypIndex r ε → K)) : Subgroup (hypSU h r ε) :=
  MulAction.stabilizer (hypSU h r ε) W

@[expose] def projIsoStabilizer (W : Submodule K (HypIndex r ε → K)) :
    Subgroup (hypPSU h r ε) :=
  (isoStabilizer h r ε W).map (hypProj h r ε)

@[expose] noncomputable def flagStabilizer (I : Set ℕ) : Subgroup (hypSU h r ε) :=
  ⨅ i ∈ I, isoStabilizer h r ε (hypFlag h r ε i)

abbrev sylowNormalizers : Set (Subgroup (hypPSU h r ε)) :=
  LinearFlag.sylowNormalizers (hypPSU h r ε) p

abbrev maximalParabolics : Set (Subgroup (hypPSU h r ε)) :=
  LinearFlag.maximalParabolics (hypPSU h r ε) p

abbrev minParabolics : Set (Subgroup (hypPSU h r ε)) :=
  LinearFlag.extremalParabolics (hypPSU h r ε) p

@[expose] def maxParabolics : Set (Subgroup (hypPSU h r ε)) :=
  {M | M ∈ maximalParabolics h r ε ∧ ∀ M' ∈ maximalParabolics h r ε, M'.index ≤ M.index}

@[expose] noncomputable def intrinsicParabolics : Set (Subgroup (hypPSU h r ε)) :=
  if 2 * r + ε = 4 then maxParabolics h r ε else minParabolics h r ε

variable {h r ε}

theorem mem_isoStabilizer {W : Submodule K (HypIndex r ε → K)} {g : hypSU h r ε} :
    g ∈ isoStabilizer h r ε W ↔ g • W = W :=
  MulAction.mem_stabilizer_iff

theorem mem_flagStabilizer {I : Set ℕ} {g : hypSU h r ε} :
    g ∈ flagStabilizer h r ε I ↔ ∀ i ∈ I, g • hypFlag h r ε i = hypFlag h r ε i := by
  simp only [flagStabilizer, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]

theorem mem_maxParabolics {M : Subgroup (hypPSU h r ε)} :
    M ∈ maxParabolics h r ε ↔
      M ∈ maximalParabolics h r ε ∧ ∀ M' ∈ maximalParabolics h r ε, M'.index ≤ M.index :=
  Iff.rfl

theorem intrinsicParabolics_of_eq_four (hn : 2 * r + ε = 4) :
    intrinsicParabolics h r ε = maxParabolics h r ε := by
  simp [intrinsicParabolics, hn]

theorem intrinsicParabolics_of_ne_four (hn : 2 * r + ε ≠ 4) :
    intrinsicParabolics h r ε = minParabolics h r ε := by
  simp [intrinsicParabolics, hn]

theorem hypScalars_le_isoStabilizer (W : Submodule K (HypIndex r ε → K)) :
    hypScalars h r ε ≤ isoStabilizer h r ε W :=
  fun _ hg => mem_isoStabilizer.mpr (smul_submodule_of_mem_normOneScalars hg W)

theorem hypScalars_le_flagStabilizer (I : Set ℕ) :
    hypScalars h r ε ≤ flagStabilizer h r ε I :=
  fun _ hg => mem_flagStabilizer.mpr fun _ _ =>
    mem_isoStabilizer.mp (hypScalars_le_isoStabilizer _ hg)

theorem comap_projIsoStabilizer (W : Submodule K (HypIndex r ε → K)) :
    (projIsoStabilizer h r ε W).comap (hypProj h r ε) = isoStabilizer h r ε W := by
  rw [projIsoStabilizer, Subgroup.comap_map_eq_self]
  rw [ker_hypProj]
  exact hypScalars_le_isoStabilizer W

theorem flagStabilizer_empty : flagStabilizer h r ε ∅ = ⊤ :=
  eq_top_iff.mpr fun _ _ => mem_flagStabilizer.mpr fun _ hi => absurd hi (Set.notMem_empty _)

theorem unitary_parabolic_data :
    (∀ W : Submodule K (HypIndex r ε → K), hypScalars h r ε ≤ isoStabilizer h r ε W) ∧
    (∀ I : Set ℕ, hypScalars h r ε ≤ flagStabilizer h r ε I) ∧
    (∀ W : Submodule K (HypIndex r ε → K),
      (projIsoStabilizer h r ε W).comap (hypProj h r ε) = isoStabilizer h r ε W) ∧
    (∀ I : Set ℕ, ((flagStabilizer h r ε I).map (hypProj h r ε)).comap (hypProj h r ε) =
      flagStabilizer h r ε I) ∧
    flagStabilizer h r ε ∅ = ⊤ ∧
    (2 * r + ε = 4 → intrinsicParabolics h r ε = maxParabolics h r ε) ∧
    (2 * r + ε ≠ 4 → intrinsicParabolics h r ε = minParabolics h r ε) := by
  refine ⟨hypScalars_le_isoStabilizer, hypScalars_le_flagStabilizer, comap_projIsoStabilizer,
    fun I => ?_, flagStabilizer_empty, intrinsicParabolics_of_eq_four,
    intrinsicParabolics_of_ne_four⟩
  rw [Subgroup.comap_map_eq_self]
  rw [ker_hypProj]
  exact hypScalars_le_flagStabilizer I

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
