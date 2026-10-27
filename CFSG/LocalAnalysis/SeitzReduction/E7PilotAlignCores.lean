module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignTori
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore)
open F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti le_centralizerPerfectCore
  normalizer_le_normalizer_centralizerPerfectCore map_centralizerPerfectCore)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG modelToG_mono modelToG_le
  modelToG_inf_adjointGroup modelToG_le_centralizer modelToG_commutator
  mem_normalizer_modelToG_of_mem_centralizer symm_mem_normalizer_modelToG modelToG_map_conj)

local instance e7PilotAlignCoresNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section Cores

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
  (e : L ≃* adjointGroup .E7 K)

@[expose] noncomputable def pieceCore (J : Finset (Fin (Tag.rank .E7))) : Subgroup G :=
  centralizerPerfectCore (modelToG e (leviTorus K J))

theorem le_normalizer_pieceCore {t : G} (ht : t ∈ centralizer (L : Set G))
    (J : Finset (Fin (Tag.rank .E7))) : t ∈ normalizer (pieceCore e J : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _
    (mem_normalizer_modelToG_of_mem_centralizer e ht _)

section Neighbour

@[expose] noncomputable def neighbourCore (N : E7Neighbour) : Subgroup G :=
  centralizerPerfectCore (modelToG e (N.torus K))

theorem neighbourCore_high :
    neighbourCore e .high = centralizerPerfectCore (modelToG e (EPilot.highTorusLine .E7 K)) := by
  rw [neighbourCore, E7Neighbour.torus_high]

theorem modelToG_le_neighbourCore {N : E7Neighbour} {H : Subgroup (ModGL .E7 K)}
    (hH : H ≤ centralizer (N.torus K : Set (ModGL .E7 K)))
    (hperf : ⁅modelToG e H, modelToG e H⁆ = modelToG e H) : modelToG e H ≤ neighbourCore e N :=
  le_centralizerPerfectCore hperf (modelToG_le_centralizer e hH)

theorem le_normalizer_neighbourCore {t : G} (ht : t ∈ centralizer (L : Set G))
    (N : E7Neighbour) : t ∈ normalizer (neighbourCore e N : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _
    (mem_normalizer_modelToG_of_mem_centralizer e ht _)

section Finite

variable [Finite G]

theorem neighbourCore_eq_map_conj (N : E7Neighbour) :
    neighbourCore e N =
      (neighbourCore e .high).map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom := by
  rw [neighbourCore, neighbourCore, map_centralizerPerfectCore, ← modelToG_map_conj,
    E7Neighbour.map_conj_rep_torus_high]

theorem pieceCore_eq (N : E7Neighbour) {J : Finset (Fin (Tag.rank .E7))} (hJ : J ⊆ N.nodes) :
    pieceCore e J =
      perfectCore (neighbourCore e N ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) :=
  F4Pilot.centralizerPerfectCore_eq_of_le (modelToG_mono e (N.torus_le_leviTorus hJ))

end Finite

end Neighbour

@[expose] def IsPairPerp (N N' : E7Neighbour) (γ : Fin (Tag.rank .E7) → ℤ) : Prop :=
  iform N.root γ = 0 ∧ iform N'.root γ = 0

instance (N N' : E7Neighbour) (γ : Fin (Tag.rank .E7) → ℤ) : Decidable (IsPairPerp N N' γ) := by
  unfold IsPairPerp
  infer_instance

@[expose] def IsTriplePerp (γ : Fin (Tag.rank .E7) → ℤ) : Prop :=
  iform (highRoot .E7) γ = 0 ∧ iform (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ) γ = 0 ∧
    iform (Pi.single 3 1 : Fin (Tag.rank .E7) → ℤ) γ = 0

instance (γ : Fin (Tag.rank .E7) → ℤ) : Decidable (IsTriplePerp γ) := by
  unfold IsTriplePerp
  infer_instance

section Points

theorem rootSubgroup_le_centralizer_corootLine {δ γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : IsRoot .E7 γ) (h : iform δ γ = 0) :
    rootSubgroup .E7 K γ ≤ centralizer (corootLine K δ : Set (ModGL .E7 K)) := by
  intro x hx
  rw [mem_centralizer_iff]
  rintro _ ⟨c, rfl⟩
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hx
  have hconj := rootDiagUnit_conj_pinnedX (corootTuple δ c) hγ d
  rw [rootChar_corootTuple, h, zpow_zero, Units.val_one, one_mul] at hconj
  exact mul_inv_eq_iff_eq_mul.1 hconj

theorem rootSpan_orthRoots_le_centralizer_torus (N : E7Neighbour) :
    rootSpan .E7 K (orthRoots N.root) ≤ centralizer (N.torus K : Set (ModGL .E7 K)) :=
  iSup₂_le fun _ hγ => rootSubgroup_le_centralizer_corootLine hγ.1 hγ.2

theorem modelToG_rootSpan_orthRoots_le_neighbourCore (N : E7Neighbour)
    (hperf : ⁅rootSpan .E7 K (orthRoots N.root), rootSpan .E7 K (orthRoots N.root)⁆ =
      rootSpan .E7 K (orthRoots N.root)) :
    modelToG e (rootSpan .E7 K (orthRoots N.root)) ≤ neighbourCore e N := by
  have hC := EPilot.rootSpan_le_adjointGroup' (K := K) (orthRoots N.root)
  refine modelToG_le_neighbourCore e (rootSpan_orthRoots_le_centralizer_torus N) ?_
  rw [← modelToG_commutator e hC hC, hperf]

end Points

section PerfectLevi

variable [Finite K] [CharP K 2]

theorem commutator_rootSubgroup_sup_neg_E7 (hq : 4 ≤ Nat.card K) {b : Fin (Tag.rank .E7) → ℤ}
    (hb : IsRoot .E7 b) :
    ⁅rootSubgroup .E7 K b ⊔ rootSubgroup .E7 K (-b),
        rootSubgroup .E7 K b ⊔ rootSubgroup .E7 K (-b)⁆ =
      rootSubgroup .E7 K b ⊔ rootSubgroup .E7 K (-b) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .E7 K hb
  exact Subgroup.isPerfect_iff.1 (h ‹Finite K› hq).2.1

theorem commutator_rootSpan_eq_of_neg_mem (hq : 4 ≤ Nat.card K)
    {S : Set (Fin (Tag.rank .E7) → ℤ)} (hS : ∀ γ ∈ S, IsRoot .E7 γ) (hneg : ∀ γ ∈ S, -γ ∈ S) :
    ⁅rootSpan .E7 K S, rootSpan .E7 K S⁆ = rootSpan .E7 K S := by
  refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (iSup₂_le fun γ hγ => ?_)
  have hR : rootSubgroup .E7 K γ ⊔ rootSubgroup .E7 K (-γ) ≤ rootSpan .E7 K S :=
    sup_le (le_iSup₂_of_le (f := fun β (_ : β ∈ S) => rootSubgroup .E7 K β) γ hγ le_rfl)
      (le_iSup₂_of_le (f := fun β (_ : β ∈ S) => rootSubgroup .E7 K β) (-γ) (hneg γ hγ) le_rfl)
  have h1 : rootSubgroup .E7 K γ ≤ rootSubgroup .E7 K γ ⊔ rootSubgroup .E7 K (-γ) := le_sup_left
  rw [← commutator_rootSubgroup_sup_neg_E7 hq (hS γ hγ)] at h1
  exact h1.trans (Subgroup.commutator_mono hR hR)

theorem commutator_rootSpan_orthRoots_eq_E7 (hq : 4 ≤ Nat.card K) (θ' : Fin (Tag.rank .E7) → ℤ) :
    ⁅rootSpan .E7 K (orthRoots θ'), rootSpan .E7 K (orthRoots θ')⁆ =
      rootSpan .E7 K (orthRoots θ') :=
  commutator_rootSpan_eq_of_neg_mem hq (fun _ hγ => hγ.1)
    fun _ hγ => ⟨IsRoot.neg hγ.1, by rw [iform_neg_right_E7, hγ.2, neg_zero]⟩

theorem commutator_levi_eq_E7 (hq : 4 ≤ Nat.card K) (N : E7Neighbour) :
    ⁅N.levi K, N.levi K⁆ = N.levi K := by
  apply map_injective (adjointGroup .E7 K).subtype_injective
  have hm : (N.levi K).map (adjointGroup .E7 K).subtype = rootSpan .E7 K (orthRoots N.root) := by
    rw [E7Neighbour.levi, subgroupOf_map_subtype,
      inf_of_le_left (EPilot.rootSpan_le_adjointGroup' _)]
  rw [Subgroup.map_commutator, hm, commutator_rootSpan_orthRoots_eq_E7 hq]

theorem commutator_perpLevi_eq_E7 (hq : 4 ≤ Nat.card K) :
    ⁅EPilot.perpLevi .E7 K, EPilot.perpLevi .E7 K⁆ = EPilot.perpLevi .E7 K := by
  rw [← E7Neighbour.levi_high]
  exact commutator_levi_eq_E7 hq _

theorem modelToG_rootSpan_orthRoots_le_neighbourCore_of_charTwo (hq : 4 ≤ Nat.card K)
    (N : E7Neighbour) : modelToG e (rootSpan .E7 K (orthRoots N.root)) ≤ neighbourCore e N :=
  modelToG_rootSpan_orthRoots_le_neighbourCore e N (commutator_rootSpan_orthRoots_eq_E7 hq _)

end PerfectLevi

end Cores

end CFSG.SeitzReduction.E7Pilot
