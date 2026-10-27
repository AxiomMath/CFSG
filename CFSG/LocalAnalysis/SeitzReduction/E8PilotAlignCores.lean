module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignTori

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore)
open F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti le_centralizerPerfectCore
  normalizer_le_normalizer_centralizerPerfectCore map_centralizerPerfectCore)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG modelToG_mono modelToG_le
  modelToG_inf_adjointGroup modelToG_le_centralizer modelToG_commutator
  mem_normalizer_modelToG_of_mem_centralizer symm_mem_normalizer_modelToG modelToG_map_conj)

local instance e8PilotAlignCoresNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

section Cores

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
  (e : L ≃* adjointGroup .E8 K)

@[expose] noncomputable def pieceCore (J : Finset (Fin (Tag.rank .E8))) : Subgroup G :=
  centralizerPerfectCore (modelToG e (leviTorus K J))

theorem le_normalizer_pieceCore {t : G} (ht : t ∈ centralizer (L : Set G))
    (J : Finset (Fin (Tag.rank .E8))) : t ∈ normalizer (pieceCore e J : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _
    (mem_normalizer_modelToG_of_mem_centralizer e ht _)

section Neighbour

@[expose] noncomputable def neighbourCore (N : E8Neighbour) : Subgroup G :=
  centralizerPerfectCore (modelToG e (N.torus K))

theorem neighbourCore_high :
    neighbourCore e .high = centralizerPerfectCore (modelToG e (EPilot.highTorusLine .E8 K)) := by
  rw [neighbourCore, E8Neighbour.torus_high]

theorem modelToG_le_neighbourCore {N : E8Neighbour} {H : Subgroup (ModGL .E8 K)}
    (hH : H ≤ centralizer (N.torus K : Set (ModGL .E8 K)))
    (hperf : ⁅modelToG e H, modelToG e H⁆ = modelToG e H) : modelToG e H ≤ neighbourCore e N :=
  le_centralizerPerfectCore hperf (modelToG_le_centralizer e hH)

theorem le_normalizer_neighbourCore {t : G} (ht : t ∈ centralizer (L : Set G))
    (N : E8Neighbour) : t ∈ normalizer (neighbourCore e N : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _
    (mem_normalizer_modelToG_of_mem_centralizer e ht _)

section Finite

variable [Finite G]

theorem neighbourCore_eq_map_conj (N : E8Neighbour) :
    neighbourCore e N =
      (neighbourCore e .high).map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom := by
  rw [neighbourCore, neighbourCore, map_centralizerPerfectCore, ← modelToG_map_conj,
    E8Neighbour.map_conj_rep_torus_high]

theorem pieceCore_eq (N : E8Neighbour) {J : Finset (Fin (Tag.rank .E8))} (hJ : J ⊆ N.nodes) :
    pieceCore e J =
      perfectCore (neighbourCore e N ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) :=
  F4Pilot.centralizerPerfectCore_eq_of_le (modelToG_mono e (N.torus_le_leviTorus hJ))

end Finite

end Neighbour

@[expose] def IsTriplePerp (γ : Fin (Tag.rank .E8) → ℤ) : Prop :=
  iform (highRoot .E8) γ = 0 ∧ iform (Pi.single 1 1 : Fin (Tag.rank .E8) → ℤ) γ = 0 ∧
    iform (Pi.single 5 1 : Fin (Tag.rank .E8) → ℤ) γ = 0

instance (γ : Fin (Tag.rank .E8) → ℤ) : Decidable (IsTriplePerp γ) := by
  unfold IsTriplePerp
  infer_instance

section Points

theorem rootSubgroup_le_centralizer_corootLine {δ γ : Fin (Tag.rank .E8) → ℤ}
    (hγ : IsRoot .E8 γ) (h : iform δ γ = 0) :
    rootSubgroup .E8 K γ ≤ centralizer (corootLine K δ : Set (ModGL .E8 K)) := by
  intro x hx
  rw [mem_centralizer_iff]
  rintro _ ⟨c, rfl⟩
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hx
  have hconj := rootDiagUnit_conj_pinnedX (corootTuple δ c) hγ d
  rw [rootChar_corootTuple, h, zpow_zero, Units.val_one, one_mul] at hconj
  exact mul_inv_eq_iff_eq_mul.1 hconj

theorem rootSpan_orthRoots_le_centralizer_torus (N : E8Neighbour) :
    rootSpan .E8 K (orthRoots N.root) ≤ centralizer (N.torus K : Set (ModGL .E8 K)) :=
  iSup₂_le fun _ hγ => rootSubgroup_le_centralizer_corootLine hγ.1 hγ.2

theorem modelToG_rootSpan_orthRoots_le_neighbourCore (N : E8Neighbour)
    (hperf : ⁅rootSpan .E8 K (orthRoots N.root), rootSpan .E8 K (orthRoots N.root)⁆ =
      rootSpan .E8 K (orthRoots N.root)) :
    modelToG e (rootSpan .E8 K (orthRoots N.root)) ≤ neighbourCore e N := by
  have hC := rootSpan_le_adjointGroup_E8 (K := K) (orthRoots N.root)
  refine modelToG_le_neighbourCore e (rootSpan_orthRoots_le_centralizer_torus N) ?_
  rw [← modelToG_commutator e hC hC, hperf]

end Points

end Cores

end CFSG.SeitzReduction.E8Pilot
