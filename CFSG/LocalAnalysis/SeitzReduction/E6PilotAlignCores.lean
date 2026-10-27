module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignTori

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)
open F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti le_centralizerPerfectCore
  normalizer_le_normalizer_centralizerPerfectCore map_centralizerPerfectCore)

local instance e6PilotAlignCoresNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Transport

variable {τ : Tag} {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
  (e : L ≃* adjointGroup τ K)

@[expose] noncomputable def modelToG (H : Subgroup (ModGL τ K)) : Subgroup G :=
  ((H.subgroupOf (adjointGroup τ K)).map e.symm.toMonoidHom).map L.subtype

theorem mem_modelToG {H : Subgroup (ModGL τ K)} {g : G} :
    g ∈ modelToG e H ↔ ∃ x : adjointGroup τ K, (x : ModGL τ K) ∈ H ∧ ((e.symm x : L) : G) = g := by
  simp only [modelToG, mem_map, mem_subgroupOf, MulEquiv.coe_toMonoidHom, coe_subtype]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

theorem symm_mem_modelToG {H : Subgroup (ModGL τ K)} {x : adjointGroup τ K}
    (hx : (x : ModGL τ K) ∈ H) : ((e.symm x : L) : G) ∈ modelToG e H :=
  (mem_modelToG e).2 ⟨x, hx, rfl⟩

theorem modelToG_mono {H₁ H₂ : Subgroup (ModGL τ K)} (h : H₁ ≤ H₂) :
    modelToG e H₁ ≤ modelToG e H₂ :=
  map_mono (map_mono (comap_mono h))

theorem modelToG_le (H : Subgroup (ModGL τ K)) : modelToG e H ≤ L :=
  map_subtype_le _

theorem modelToG_inf_adjointGroup (H : Subgroup (ModGL τ K)) :
    modelToG e (H ⊓ adjointGroup τ K) = modelToG e H := by
  refine le_antisymm (modelToG_mono e inf_le_left) fun g hg => ?_
  obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hg
  exact symm_mem_modelToG e ⟨hx, x.2⟩

theorem modelToG_le_centralizer {H₁ H₂ : Subgroup (ModGL τ K)}
    (h : H₁ ≤ centralizer (H₂ : Set (ModGL τ K))) :
    modelToG e H₁ ≤ centralizer (modelToG e H₂ : Set G) := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hg
  rw [mem_centralizer_iff]
  intro g' hg'
  obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hg'
  have hxy : y * x = x * y := Subtype.ext (mem_centralizer_iff.1 (h hx) _ hy)
  rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, hxy]

theorem modelToG_commutator {H₁ H₂ : Subgroup (ModGL τ K)} (h₁ : H₁ ≤ adjointGroup τ K)
    (h₂ : H₂ ≤ adjointGroup τ K) :
    modelToG e ⁅H₁, H₂⁆ = ⁅modelToG e H₁, modelToG e H₂⁆ := by
  have hsub : ⁅H₁, H₂⁆.subgroupOf (adjointGroup τ K) =
      ⁅H₁.subgroupOf (adjointGroup τ K), H₂.subgroupOf (adjointGroup τ K)⁆ := by
    apply map_injective (adjointGroup τ K).subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_of_le_left h₁, inf_of_le_left h₂,
      inf_of_le_left ((commutator_mono h₁ h₂).trans (commutator_le_self _))]
  rw [modelToG, modelToG, modelToG, hsub, map_commutator, map_commutator]

theorem mem_normalizer_modelToG_of_mem_centralizer {t : G} (ht : t ∈ centralizer (L : Set G))
    (H : Subgroup (ModGL τ K)) : t ∈ normalizer (modelToG e H : Set G) :=
  centralizer_le_normalizer _ (centralizer_le (SetLike.coe_subset_coe.2 (modelToG_le e H)) ht)

theorem symm_mem_normalizer_modelToG {H : Subgroup (ModGL τ K)} {x : adjointGroup τ K}
    (hx : (x : ModGL τ K) ∈ normalizer (H : Set (ModGL τ K))) :
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
    have hy' : ((x⁻¹ * y * x : adjointGroup τ K) : ModGL τ K) ∈ H := by
      have := (mem_normalizer_iff.1 (inv_mem hx) y).1 hy
      simpa only [inv_inv, coe_mul, coe_inv] using this
    refine (mem_modelToG e).2 ⟨x⁻¹ * y * x, hy', ?_⟩
    rw [map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv, hyg]
    group

theorem modelToG_map_conj (H : Subgroup (ModGL τ K)) (n : adjointGroup τ K) :
    modelToG e (H.map (MulAut.conj (n : ModGL τ K)).toMonoidHom) =
      (modelToG e H).map (MulAut.conj ((e.symm n : L) : G)).toMonoidHom := by
  ext g
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [mem_modelToG]
  constructor
  · rintro ⟨x, ⟨y, hy, hyx'⟩, rfl⟩
    have hyx : (n : ModGL τ K) * y * (n : ModGL τ K)⁻¹ = x := hyx'
    have hyC : y ∈ adjointGroup τ K := by
      have : y = (n : ModGL τ K)⁻¹ * x * n := by rw [← hyx]; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem n.2) x.2) n.2
    refine ⟨((e.symm ⟨y, hyC⟩ : L) : G), symm_mem_modelToG e hy, ?_⟩
    have hx : x = n * ⟨y, hyC⟩ * n⁻¹ := Subtype.ext hyx.symm
    rw [hx, map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]
  · rintro ⟨_, hg, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hg
    refine ⟨n * y * n⁻¹, ⟨y, hy, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]

end Transport

section Cores

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
  (e : L ≃* adjointGroup .E6 K)

@[expose] noncomputable def pieceCore (J : Finset (Fin (Tag.rank .E6))) : Subgroup G :=
  centralizerPerfectCore (modelToG e (leviTorus K J))

theorem pieceCore_def (J : Finset (Fin (Tag.rank .E6))) :
    pieceCore e J = centralizerPerfectCore (modelToG e (leviTorus K J)) :=
  rfl

theorem pieceCore_eq_inf (J : Finset (Fin (Tag.rank .E6))) :
    pieceCore e J =
      centralizerPerfectCore (modelToG e (leviTorus K J ⊓ adjointGroup .E6 K)) := by
  rw [pieceCore, modelToG_inf_adjointGroup]

theorem pieceCore_mono {I J : Finset (Fin (Tag.rank .E6))} (h : I ⊆ J) :
    pieceCore e I ≤ pieceCore e J :=
  centralizerPerfectCore_anti (modelToG_mono e (leviTorus_anti h))

theorem modelToG_le_pieceCore {J : Finset (Fin (Tag.rank .E6))} {H : Subgroup (ModGL .E6 K)}
    (hH : H ≤ centralizer (leviTorus K J : Set (ModGL .E6 K)))
    (hperf : ⁅modelToG e H, modelToG e H⁆ = modelToG e H) : modelToG e H ≤ pieceCore e J :=
  le_centralizerPerfectCore hperf (modelToG_le_centralizer e hH)

theorem le_normalizer_pieceCore {t : G} (ht : t ∈ centralizer (L : Set G))
    (J : Finset (Fin (Tag.rank .E6))) : t ∈ normalizer (pieceCore e J : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _
    (mem_normalizer_modelToG_of_mem_centralizer e ht _)

theorem symm_mem_normalizer_pieceCore {J : Finset (Fin (Tag.rank .E6))} {x : adjointGroup .E6 K}
    (hx : (x : ModGL .E6 K) ∈ normalizer (leviTorus K J : Set (ModGL .E6 K))) :
    ((e.symm x : L) : G) ∈ normalizer (pieceCore e J : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _ (symm_mem_normalizer_modelToG e hx)

section Neighbour

@[expose] noncomputable def neighbourCore (N : E6Neighbour) : Subgroup G :=
  centralizerPerfectCore (modelToG e (N.torus K))

theorem neighbourCore_high :
    neighbourCore e .high = centralizerPerfectCore (modelToG e (EPilot.highTorusLine .E6 K)) := by
  rw [neighbourCore, E6Neighbour.torus_high]

theorem pieceCore_le_neighbourCore (N : E6Neighbour) {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J ⊆ N.nodes) : pieceCore e J ≤ neighbourCore e N :=
  centralizerPerfectCore_anti (modelToG_mono e (N.torus_le_leviTorus hJ))

theorem modelToG_le_neighbourCore {N : E6Neighbour} {H : Subgroup (ModGL .E6 K)}
    (hH : H ≤ centralizer (N.torus K : Set (ModGL .E6 K)))
    (hperf : ⁅modelToG e H, modelToG e H⁆ = modelToG e H) : modelToG e H ≤ neighbourCore e N :=
  le_centralizerPerfectCore hperf (modelToG_le_centralizer e hH)

theorem le_normalizer_neighbourCore {t : G} (ht : t ∈ centralizer (L : Set G))
    (N : E6Neighbour) : t ∈ normalizer (neighbourCore e N : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _
    (mem_normalizer_modelToG_of_mem_centralizer e ht _)

theorem symm_mem_normalizer_neighbourCore {N : E6Neighbour} {x : adjointGroup .E6 K}
    (hx : (x : ModGL .E6 K) ∈ normalizer (N.torus K : Set (ModGL .E6 K))) :
    ((e.symm x : L) : G) ∈ normalizer (neighbourCore e N : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _ (symm_mem_normalizer_modelToG e hx)

section Finite

variable [Finite G]

theorem neighbourCore_eq_map_conj (N : E6Neighbour) :
    neighbourCore e N =
      (neighbourCore e .high).map (MulAut.conj ((e.symm (N.rep K) : L) : G)).toMonoidHom := by
  rw [neighbourCore, neighbourCore, map_centralizerPerfectCore, ← modelToG_map_conj,
    E6Neighbour.map_conj_rep_torus_high]

theorem pieceCore_eq (N : E6Neighbour) {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) :
    pieceCore e J =
      perfectCore (neighbourCore e N ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) :=
  F4Pilot.centralizerPerfectCore_eq_of_le (modelToG_mono e (N.torus_le_leviTorus hJ))

theorem perfectCore_neighbourCore_inf_eq {N N' : E6Neighbour} {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J ⊆ N.nodes) (hJ' : J ⊆ N'.nodes) :
    perfectCore (neighbourCore e N ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) =
      perfectCore (neighbourCore e N' ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) := by
  rw [← pieceCore_eq e N hJ, ← pieceCore_eq e N' hJ']

theorem pieceCore_eq_placement {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2) :
    pieceCore e J = perfectCore (neighbourCore e (amalgamPlacement J) ⊓
      centralizer (modelToG e (leviTorus K J) : Set G)) :=
  pieceCore_eq e _ (subset_nodes_amalgamPlacement hJ)

theorem perfectCore_neighbourCore_high_eq_six {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J ⊆ {0, 2, 3}) :
    perfectCore (neighbourCore e .high ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) =
      perfectCore (neighbourCore e .six ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) :=
  perfectCore_neighbourCore_inf_eq e (hJ.trans (by decide)) (hJ.trans (by decide))

theorem perfectCore_neighbourCore_high_eq_three {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J ⊆ {4, 5}) :
    perfectCore (neighbourCore e .high ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) =
      perfectCore (neighbourCore e .three ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) :=
  perfectCore_neighbourCore_inf_eq e (hJ.trans (by decide)) (hJ.trans (by decide))

theorem perfectCore_neighbourCore_six_eq_three {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J ⊆ {1}) :
    perfectCore (neighbourCore e .six ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) =
      perfectCore (neighbourCore e .three ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) :=
  perfectCore_neighbourCore_inf_eq e (hJ.trans (by decide)) (hJ.trans (by decide))

@[expose] noncomputable def pairCore (N N' : E6Neighbour) : Subgroup G :=
  centralizerPerfectCore (modelToG e (N.torus K) ⊔ modelToG e (N'.torus K))

theorem pairCore_eq_left (N N' : E6Neighbour) :
    pairCore e N N' =
      perfectCore (neighbourCore e N ⊓ centralizer (modelToG e (N'.torus K) : Set G)) :=
  F4Pilot.centralizerPerfectCore_sup _ _

theorem pairCore_eq_right (N N' : E6Neighbour) :
    pairCore e N N' =
      perfectCore (neighbourCore e N' ⊓ centralizer (modelToG e (N.torus K) : Set G)) := by
  rw [pairCore, sup_comm]
  exact F4Pilot.centralizerPerfectCore_sup _ _

omit [Finite G] in
theorem pairCore_le_neighbourCore (N N' : E6Neighbour) :
    pairCore e N N' ≤ neighbourCore e N ⊓ neighbourCore e N' :=
  le_inf (centralizerPerfectCore_anti le_sup_left) (centralizerPerfectCore_anti le_sup_right)

omit [Finite G] in
theorem pieceCore_le_pairCore {N N' : E6Neighbour} {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J ⊆ N.nodes) (hJ' : J ⊆ N'.nodes) : pieceCore e J ≤ pairCore e N N' :=
  centralizerPerfectCore_anti (sup_le (modelToG_mono e (N.torus_le_leviTorus hJ))
    (modelToG_mono e (N'.torus_le_leviTorus hJ')))

@[expose] noncomputable def tripleCore : Subgroup G :=
  centralizerPerfectCore (modelToG e (E6Neighbour.high.torus K) ⊔
    modelToG e (E6Neighbour.six.torus K) ⊔ modelToG e (E6Neighbour.three.torus K))

omit [Finite G] in
theorem tripleCore_le_pairCore (N N' : E6Neighbour) : tripleCore e ≤ pairCore e N N' := by
  have hT : ∀ M : E6Neighbour, modelToG e (M.torus K) ≤
      modelToG e (E6Neighbour.high.torus K) ⊔ modelToG e (E6Neighbour.six.torus K) ⊔
        modelToG e (E6Neighbour.three.torus K) := fun M => by
    cases M
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  exact centralizerPerfectCore_anti (sup_le (hT N) (hT N'))

end Finite

end Neighbour

open CFSG.LieType.Steinberg.Adjoint in
theorem triplePerp_check :
    (∀ γ ∈ rootFinset .E6,
      (iform (highRoot .E6) γ = 0 ∧ iform (Pi.single 5 1 : Fin (Tag.rank .E6) → ℤ) γ = 0 ∧
        iform (Pi.single 2 1 : Fin (Tag.rank .E6) → ℤ) γ = 0) →
        γ ∈ ([![1, 0, 1, 1, 0, 0], -![1, 0, 1, 1, 0, 0]] : List (Fin (Tag.rank .E6) → ℤ))) ∧
    ∀ γ ∈ ([![1, 0, 1, 1, 0, 0], -![1, 0, 1, 1, 0, 0]] : List (Fin (Tag.rank .E6) → ℤ)),
      γ ∈ rootFinset .E6 ∧ iform (highRoot .E6) γ = 0 ∧
        iform (Pi.single 5 1 : Fin (Tag.rank .E6) → ℤ) γ = 0 ∧
        iform (Pi.single 2 1 : Fin (Tag.rank .E6) → ℤ) γ = 0 := by
  decide +kernel

section Points


theorem modelToG_rootSpan_le_pieceCore (J : Finset (Fin (Tag.rank .E6)))
    (hperf : ⁅modelToG e (rootSpan .E6 K (amalgamRoots J)),
        modelToG e (rootSpan .E6 K (amalgamRoots J))⁆ =
      modelToG e (rootSpan .E6 K (amalgamRoots J))) :
    modelToG e (rootSpan .E6 K (amalgamRoots J)) ≤ pieceCore e J :=
  modelToG_le_pieceCore e (rootSpan_amalgamRoots_le_centralizer_leviTorus J) hperf

theorem modelToG_rootSpan_le_pieceCore_of_perfect (J : Finset (Fin (Tag.rank .E6)))
    (hperf : ⁅rootSpan .E6 K (amalgamRoots J), rootSpan .E6 K (amalgamRoots J)⁆ =
      rootSpan .E6 K (amalgamRoots J)) :
    modelToG e (rootSpan .E6 K (amalgamRoots J)) ≤ pieceCore e J := by
  have hC := rootSpan_le_adjointGroup_E6 (K := K) (amalgamRoots J)
  refine modelToG_rootSpan_le_pieceCore e J ?_
  rw [← modelToG_commutator e hC hC, hperf]

end Points

end Cores

end CFSG.SeitzReduction.E6Pilot
