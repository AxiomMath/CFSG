module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherParabolicData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix CFSG.Assembly.LowTwoRank SymplecticFlag

variable (r : ℕ) (K : Type) [Field K]

abbrev spScalars : Subgroup (StatedSp r K) :=
  (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)

@[expose] def projStabilizer (W : Submodule K (Fin r ⊕ Fin r → K)) :
    Subgroup (StatedProj (StatedSp r K)) :=
  (stabilizer r K W).map (proj r K)

@[expose] def flagStabilizer (I : Set ℕ) : Subgroup (StatedSp r K) :=
  ⨅ i ∈ I, stabilizer r K (flag r K i)

variable {r K}

theorem mem_flagStabilizer {I : Set ℕ} {g : StatedSp r K} :
    g ∈ flagStabilizer r K I ↔ ∀ i ∈ I, g ∈ stabilizer r K (flag r K i) := by
  simp only [flagStabilizer, Subgroup.mem_iInf]

theorem ker_proj : (proj r K).ker = spScalars r K :=
  QuotientGroup.ker_mk' _

theorem proj_surjective : Function.Surjective (proj r K) :=
  QuotientGroup.mk'_surjective _

theorem spScalars_le_stabilizer (W : Submodule K (Fin r ⊕ Fin r → K)) :
    spScalars r K ≤ stabilizer r K W := by
  intro g hg
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  have hmul : ∀ v : Fin r ⊕ Fin r → K,
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v =
        (c : K) • v := fun v => by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply]
    ext x
    simp [mulVec_diagonal]
  rw [mem_stabilizer]
  refine le_antisymm ?_ fun v hv => ⟨((c⁻¹ : Kˣ) : K) • v, W.smul_mem _ hv, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [mulVecLin_apply, hmul]
    exact W.smul_mem _ hv
  · rw [mulVecLin_apply, hmul, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_smul]

theorem spScalars_le_flagStabilizer (I : Set ℕ) : spScalars r K ≤ flagStabilizer r K I :=
  fun _ hg => mem_flagStabilizer.mpr fun _ _ => spScalars_le_stabilizer _ hg

theorem comap_projStabilizer (W : Submodule K (Fin r ⊕ Fin r → K)) :
    (projStabilizer r K W).comap (proj r K) = stabilizer r K W := by
  rw [projStabilizer, Subgroup.comap_map_eq_self]
  rw [ker_proj]
  exact spScalars_le_stabilizer W

theorem flagStabilizer_empty : flagStabilizer r K ∅ = ⊤ :=
  eq_top_iff.mpr fun _ _ => mem_flagStabilizer.mpr fun _ h => absurd h (Set.notMem_empty _)

theorem parabolic_data :
    (∀ W : Submodule K (Fin r ⊕ Fin r → K), spScalars r K ≤ stabilizer r K W) ∧
    (∀ I : Set ℕ, spScalars r K ≤ flagStabilizer r K I) ∧
    (∀ W : Submodule K (Fin r ⊕ Fin r → K),
      (projStabilizer r K W).comap (proj r K) = stabilizer r K W) ∧
    (∀ I : Set ℕ,
      ((flagStabilizer r K I).map (proj r K)).comap (proj r K) = flagStabilizer r K I) ∧
    flagStabilizer r K ∅ = ⊤ := by
  refine ⟨spScalars_le_stabilizer, spScalars_le_flagStabilizer, comap_projStabilizer,
    fun I => ?_, flagStabilizer_empty⟩
  rw [Subgroup.comap_map_eq_self]
  rw [ker_proj]
  exact spScalars_le_flagStabilizer I

variable (r K)

abbrev spSylowNormalizers (p : ℕ) : Set (Subgroup (StatedProj (StatedSp r K))) :=
  LinearFlag.sylowNormalizers (StatedProj (StatedSp r K)) p

abbrev spMaximalParabolics (p : ℕ) : Set (Subgroup (StatedProj (StatedSp r K))) :=
  LinearFlag.maximalParabolics (StatedProj (StatedSp r K)) p

abbrev spExtremalParabolics (p : ℕ) : Set (Subgroup (StatedProj (StatedSp r K))) :=
  LinearFlag.extremalParabolics (StatedProj (StatedSp r K)) p

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
