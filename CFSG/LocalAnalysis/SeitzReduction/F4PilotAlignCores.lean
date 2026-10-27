module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignTori

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)

local instance f4PilotAlignCoresNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Abstract

variable {G : Type*} [Group G] [Finite G]

theorem centralizerPerfectCore_eq_of_le {Y T : Subgroup G} (h : Y ≤ T) :
    centralizerPerfectCore T =
      perfectCore (centralizerPerfectCore Y ⊓ centralizer (T : Set G)) := by
  rw [← centralizerPerfectCore_sup, sup_eq_right.mpr h]

theorem perfectCore_neighbour_eq_of_le_of_le {Y₁ Y₂ T : Subgroup G} (h₁ : Y₁ ≤ T)
    (h₂ : Y₂ ≤ T) :
    perfectCore (centralizerPerfectCore Y₁ ⊓ centralizer (T : Set G)) =
      perfectCore (centralizerPerfectCore Y₂ ⊓ centralizer (T : Set G)) := by
  rw [← centralizerPerfectCore_eq_of_le h₁, ← centralizerPerfectCore_eq_of_le h₂]

end Abstract

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
  (e : L ≃* adjointGroup .F4 K)

@[expose] noncomputable def modelToG (H : Subgroup (ModGL .F4 K)) : Subgroup G :=
  ((H.subgroupOf (adjointGroup .F4 K)).map e.symm.toMonoidHom).map L.subtype

theorem mem_modelToG {H : Subgroup (ModGL .F4 K)} {g : G} :
    g ∈ modelToG e H ↔
      ∃ x : adjointGroup .F4 K, (x : ModGL .F4 K) ∈ H ∧ ((e.symm x : L) : G) = g := by
  simp only [modelToG, mem_map, mem_subgroupOf, MulEquiv.coe_toMonoidHom, coe_subtype]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

theorem symm_mem_modelToG {H : Subgroup (ModGL .F4 K)} {x : adjointGroup .F4 K}
    (hx : (x : ModGL .F4 K) ∈ H) : ((e.symm x : L) : G) ∈ modelToG e H :=
  (mem_modelToG e).2 ⟨x, hx, rfl⟩

theorem modelToG_mono {H₁ H₂ : Subgroup (ModGL .F4 K)} (h : H₁ ≤ H₂) :
    modelToG e H₁ ≤ modelToG e H₂ :=
  map_mono (map_mono (comap_mono h))

theorem modelToG_le (H : Subgroup (ModGL .F4 K)) : modelToG e H ≤ L :=
  map_subtype_le _

theorem modelToG_le_centralizer {H₁ H₂ : Subgroup (ModGL .F4 K)}
    (h : H₁ ≤ centralizer (H₂ : Set (ModGL .F4 K))) :
    modelToG e H₁ ≤ centralizer (modelToG e H₂ : Set G) := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hg
  rw [mem_centralizer_iff]
  intro g' hg'
  obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hg'
  have hxy : y * x = x * y := Subtype.ext (mem_centralizer_iff.1 (h hx) _ hy)
  rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, hxy]

theorem modelToG_commutator {H₁ H₂ : Subgroup (ModGL .F4 K)} (h₁ : H₁ ≤ adjointGroup .F4 K)
    (h₂ : H₂ ≤ adjointGroup .F4 K) :
    modelToG e ⁅H₁, H₂⁆ = ⁅modelToG e H₁, modelToG e H₂⁆ := by
  have hsub : ⁅H₁, H₂⁆.subgroupOf (adjointGroup .F4 K) =
      ⁅H₁.subgroupOf (adjointGroup .F4 K), H₂.subgroupOf (adjointGroup .F4 K)⁆ := by
    apply map_injective (adjointGroup .F4 K).subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_of_le_left h₁, inf_of_le_left h₂,
      inf_of_le_left ((commutator_mono h₁ h₂).trans (commutator_le_self _))]
  rw [modelToG, modelToG, modelToG, hsub, map_commutator, map_commutator]

theorem mem_normalizer_modelToG_of_mem_centralizer {t : G} (ht : t ∈ centralizer (L : Set G))
    (H : Subgroup (ModGL .F4 K)) : t ∈ normalizer (modelToG e H : Set G) :=
  centralizer_le_normalizer _ (centralizer_le (SetLike.coe_subset_coe.2 (modelToG_le e H)) ht)

theorem symm_mem_normalizer_modelToG {H : Subgroup (ModGL .F4 K)} {x : adjointGroup .F4 K}
    (hx : (x : ModGL .F4 K) ∈ normalizer (H : Set (ModGL .F4 K))) :
    ((e.symm x : L) : G) ∈ normalizer (modelToG e H : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hg
    refine (mem_modelToG e).2 ⟨x * y * x⁻¹, (mem_normalizer_iff.1 hx y).1 hy, ?_⟩
    rw [map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]
  · intro hg
    obtain ⟨y, hy, hyg⟩ := (mem_modelToG e).1 hg
    have hy' : ((x⁻¹ * y * x : adjointGroup .F4 K) : ModGL .F4 K) ∈ H := by
      have := (mem_normalizer_iff.1 (inv_mem hx) y).1 hy
      simpa only [inv_inv, coe_mul, coe_inv] using this
    refine (mem_modelToG e).2 ⟨x⁻¹ * y * x, hy', ?_⟩
    rw [map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv, hyg]
    group

theorem modelToG_map_conj (H : Subgroup (ModGL .F4 K)) (n : adjointGroup .F4 K) :
    modelToG e (H.map (MulAut.conj (n : ModGL .F4 K)).toMonoidHom) =
      (modelToG e H).map (MulAut.conj ((e.symm n : L) : G)).toMonoidHom := by
  ext g
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [mem_modelToG]
  constructor
  · rintro ⟨x, ⟨y, hy, hyx'⟩, rfl⟩
    have hyx : (n : ModGL .F4 K) * y * (n : ModGL .F4 K)⁻¹ = x := hyx'
    have hyC : y ∈ adjointGroup .F4 K := by
      have : y = (n : ModGL .F4 K)⁻¹ * x * n := by rw [← hyx]; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem n.2) x.2) n.2
    refine ⟨((e.symm ⟨y, hyC⟩ : L) : G), symm_mem_modelToG e hy, ?_⟩
    have hx : x = n * ⟨y, hyC⟩ * n⁻¹ := Subtype.ext hyx.symm
    rw [hx, map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]
  · rintro ⟨_, hg, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hg
    refine ⟨n * y * n⁻¹, ⟨y, hy, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]

@[expose] noncomputable def pieceCore (J : Finset (Fin (Tag.rank .F4))) : Subgroup G :=
  centralizerPerfectCore (modelToG e (leviTorus K J))

theorem pieceCore_def (J : Finset (Fin (Tag.rank .F4))) :
    pieceCore e J = centralizerPerfectCore (modelToG e (leviTorus K J)) :=
  rfl

theorem pieceCore_mono {I J : Finset (Fin (Tag.rank .F4))} (h : I ⊆ J) :
    pieceCore e I ≤ pieceCore e J :=
  centralizerPerfectCore_anti (modelToG_mono e (leviTorus_anti h))

theorem modelToG_le_pieceCore {J : Finset (Fin (Tag.rank .F4))} {H : Subgroup (ModGL .F4 K)}
    (hH : H ≤ centralizer (leviTorus K J : Set (ModGL .F4 K)))
    (hperf : ⁅modelToG e H, modelToG e H⁆ = modelToG e H) : modelToG e H ≤ pieceCore e J :=
  le_centralizerPerfectCore hperf (modelToG_le_centralizer e hH)

theorem le_normalizer_pieceCore {t : G} (ht : t ∈ centralizer (L : Set G))
    (J : Finset (Fin (Tag.rank .F4))) : t ∈ normalizer (pieceCore e J : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _
    (mem_normalizer_modelToG_of_mem_centralizer e ht _)

theorem normalizer_modelToG_le_normalizer_pieceCore (J : Finset (Fin (Tag.rank .F4))) :
    normalizer (modelToG e (leviTorus K J) : Set G) ≤ normalizer (pieceCore e J : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _

theorem symm_mem_normalizer_pieceCore {J : Finset (Fin (Tag.rank .F4))} {x : adjointGroup .F4 K}
    (hx : (x : ModGL .F4 K) ∈ normalizer (leviTorus K J : Set (ModGL .F4 K))) :
    ((e.symm x : L) : G) ∈ normalizer (pieceCore e J : Set G) :=
  normalizer_modelToG_le_normalizer_pieceCore e J (symm_mem_normalizer_modelToG e hx)

section Neighbour


@[expose] noncomputable def neighbourCore (N : AmalgamNeighbour) : Subgroup G :=
  centralizerPerfectCore (modelToG e (N.torus K))

theorem neighbourCore_X :
    neighbourCore e .X = centralizerPerfectCore (modelToG e (torusLineR K)) :=
  rfl

theorem neighbourCore_Y :
    neighbourCore e .Y = centralizerPerfectCore (modelToG e (torusLineS K)) :=
  rfl

theorem neighbourCore_X' :
    neighbourCore e .X' = centralizerPerfectCore (modelToG e (torusLine1242 K)) :=
  rfl

theorem pieceCore_le_neighbourCore (N : AmalgamNeighbour) {J : Finset (Fin (Tag.rank .F4))}
    (hJ : J ⊆ N.nodes) : pieceCore e J ≤ neighbourCore e N :=
  centralizerPerfectCore_anti (modelToG_mono e (N.torus_le_leviTorus hJ))

theorem modelToG_le_neighbourCore {N : AmalgamNeighbour} {H : Subgroup (ModGL .F4 K)}
    (hH : H ≤ centralizer (N.torus K : Set (ModGL .F4 K)))
    (hperf : ⁅modelToG e H, modelToG e H⁆ = modelToG e H) : modelToG e H ≤ neighbourCore e N :=
  le_centralizerPerfectCore hperf (modelToG_le_centralizer e hH)

theorem le_normalizer_neighbourCore {t : G} (ht : t ∈ centralizer (L : Set G))
    (N : AmalgamNeighbour) : t ∈ normalizer (neighbourCore e N : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _
    (mem_normalizer_modelToG_of_mem_centralizer e ht _)

theorem symm_mem_normalizer_neighbourCore {N : AmalgamNeighbour} {x : adjointGroup .F4 K}
    (hx : (x : ModGL .F4 K) ∈ normalizer (N.torus K : Set (ModGL .F4 K))) :
    ((e.symm x : L) : G) ∈ normalizer (neighbourCore e N : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _ (symm_mem_normalizer_modelToG e hx)

section Finite

variable [Finite G]

theorem neighbourCore_X'_eq_map_conj :
    neighbourCore e .X' =
      (neighbourCore e .X).map (MulAut.conj ((e.symm (n1242 K) : L) : G)).toMonoidHom := by
  rw [neighbourCore_X', neighbourCore_X, map_centralizerPerfectCore, torusLine1242,
    modelToG_map_conj]

theorem pieceCore_eq (N : AmalgamNeighbour) {J : Finset (Fin (Tag.rank .F4))}
    (hJ : J ⊆ N.nodes) :
    pieceCore e J =
      perfectCore (neighbourCore e N ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) :=
  centralizerPerfectCore_eq_of_le (modelToG_mono e (N.torus_le_leviTorus hJ))

theorem perfectCore_neighbourCore_inf_eq {N N' : AmalgamNeighbour}
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) (hJ' : J ⊆ N'.nodes) :
    perfectCore (neighbourCore e N ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) =
      perfectCore (neighbourCore e N' ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) := by
  rw [← pieceCore_eq e N hJ, ← pieceCore_eq e N' hJ']

theorem perfectCore_neighbourCore_X_eq_Y :
    perfectCore (neighbourCore e .X ⊓ centralizer (modelToG e (leviTorus K {1, 2}) : Set G)) =
      perfectCore (neighbourCore e .Y ⊓ centralizer (modelToG e (leviTorus K {1, 2}) : Set G)) :=
  perfectCore_neighbourCore_inf_eq e (by decide) (by decide)

end Finite

end Neighbour

section Points


theorem modelToG_rootSpan_le_pieceCore (J : Finset (Fin (Tag.rank .F4)))
    (hperf : ⁅modelToG e (rootSpan .F4 K (amalgamRoots J)),
        modelToG e (rootSpan .F4 K (amalgamRoots J))⁆ =
      modelToG e (rootSpan .F4 K (amalgamRoots J))) :
    modelToG e (rootSpan .F4 K (amalgamRoots J)) ≤ pieceCore e J :=
  modelToG_le_pieceCore e (rootSpan_amalgamRoots_le_centralizer_leviTorus J) hperf

theorem modelToG_rootSpan_le_pieceCore_of_perfect (J : Finset (Fin (Tag.rank .F4)))
    (hperf : ⁅rootSpan .F4 K (amalgamRoots J), rootSpan .F4 K (amalgamRoots J)⁆ =
      rootSpan .F4 K (amalgamRoots J)) :
    modelToG e (rootSpan .F4 K (amalgamRoots J)) ≤ pieceCore e J := by
  have hC := rootSpan_le_adjointGroup_F4 (K := K) (amalgamRoots J)
  refine modelToG_rootSpan_le_pieceCore e J ?_
  rw [← modelToG_commutator e hC hC, hperf]

end Points

end Transport

end CFSG.SeitzReduction.F4Pilot
