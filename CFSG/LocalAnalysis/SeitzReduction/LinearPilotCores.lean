module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCoresTori
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignCores
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti
  le_centralizerPerfectCore normalizer_le_normalizer_centralizerPerfectCore
  map_centralizerPerfectCore)

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  (e : L ≃* LinearFlag.projectiveSL n K)

@[expose] noncomputable def modelToG (A : Subgroup (LinearFlag.projectiveSL n K)) : Subgroup G :=
  (A.map e.symm.toMonoidHom).map L.subtype

theorem mem_modelToG {A : Subgroup (LinearFlag.projectiveSL n K)} {g : G} :
    g ∈ modelToG e A ↔ ∃ x ∈ A, ((e.symm x : L) : G) = g := by
  simp only [modelToG, mem_map, MulEquiv.coe_toMonoidHom, coe_subtype]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

theorem symm_mem_modelToG {A : Subgroup (LinearFlag.projectiveSL n K)}
    {x : LinearFlag.projectiveSL n K} (hx : x ∈ A) : ((e.symm x : L) : G) ∈ modelToG e A :=
  (mem_modelToG e).2 ⟨x, hx, rfl⟩

theorem modelToG_mono {A B : Subgroup (LinearFlag.projectiveSL n K)} (h : A ≤ B) :
    modelToG e A ≤ modelToG e B :=
  map_mono (map_mono h)

theorem modelToG_le (A : Subgroup (LinearFlag.projectiveSL n K)) : modelToG e A ≤ L :=
  map_subtype_le _

theorem modelToG_top : modelToG e (⊤ : Subgroup (LinearFlag.projectiveSL n K)) = L := by
  rw [modelToG, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.symm.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

theorem modelToG_le_centralizer {A B : Subgroup (LinearFlag.projectiveSL n K)}
    (h : A ≤ centralizer (B : Set (LinearFlag.projectiveSL n K))) :
    modelToG e A ≤ centralizer (modelToG e B : Set G) := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hg
  rw [mem_centralizer_iff]
  intro g' hg'
  obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hg'
  rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, mem_centralizer_iff.1 (h hx) y hy]

theorem modelToG_commutator (A B : Subgroup (LinearFlag.projectiveSL n K)) :
    modelToG e ⁅A, B⁆ = ⁅modelToG e A, modelToG e B⁆ := by
  rw [modelToG, modelToG, modelToG, map_commutator, map_commutator]

theorem modelToG_perfect {A : Subgroup (LinearFlag.projectiveSL n K)} (hA : ⁅A, A⁆ = A) :
    ⁅modelToG e A, modelToG e A⁆ = modelToG e A := by
  rw [← modelToG_commutator, hA]

theorem mem_normalizer_modelToG_of_mem_centralizer {t : G} (ht : t ∈ centralizer (L : Set G))
    (A : Subgroup (LinearFlag.projectiveSL n K)) : t ∈ normalizer (modelToG e A : Set G) :=
  centralizer_le_normalizer _ (centralizer_le (SetLike.coe_subset_coe.2 (modelToG_le e A)) ht)

theorem symm_mem_normalizer_modelToG {A : Subgroup (LinearFlag.projectiveSL n K)}
    {x : LinearFlag.projectiveSL n K}
    (hx : x ∈ normalizer (A : Set (LinearFlag.projectiveSL n K))) :
    ((e.symm x : L) : G) ∈ normalizer (modelToG e A : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hg
    refine (mem_modelToG e).2 ⟨x * y * x⁻¹, (mem_normalizer_iff.1 hx y).1 hy, ?_⟩
    rw [map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]
  · intro hg
    obtain ⟨y, hy, hyg⟩ := (mem_modelToG e).1 hg
    have hy' : x⁻¹ * y * x ∈ A := by
      have := (mem_normalizer_iff.1 (inv_mem hx) y).1 hy
      simpa only [inv_inv] using this
    refine (mem_modelToG e).2 ⟨x⁻¹ * y * x, hy', ?_⟩
    rw [map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv, hyg]
    group

theorem modelToG_map_conj (A : Subgroup (LinearFlag.projectiveSL n K))
    (x : LinearFlag.projectiveSL n K) :
    modelToG e (A.map (MulAut.conj x).toMonoidHom) =
      (modelToG e A).map (MulAut.conj ((e.symm x : L) : G)).toMonoidHom := by
  ext g
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [mem_modelToG]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨((e.symm y : L) : G), symm_mem_modelToG e hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]
  · rintro ⟨_, hg, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hg
    refine ⟨x * y * x⁻¹, ⟨y, hy, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]

@[expose] noncomputable def pieceCore (I : Finset (Fin n)) : Subgroup G :=
  centralizerPerfectCore (modelToG e (blockTorus (K := K) I))

theorem pieceCore_def (I : Finset (Fin n)) :
    pieceCore e I = centralizerPerfectCore (modelToG e (blockTorus (K := K) I)) :=
  rfl

theorem pieceCore_mono {I I' : Finset (Fin n)} (h : I ⊆ I') : pieceCore e I ≤ pieceCore e I' :=
  centralizerPerfectCore_anti (modelToG_mono e (blockTorus_anti h))

theorem modelToG_le_pieceCore {I : Finset (Fin n)} {A : Subgroup (LinearFlag.projectiveSL n K)}
    (hA : A ≤ centralizer (blockTorus (K := K) I : Set (LinearFlag.projectiveSL n K)))
    (hperf : ⁅A, A⁆ = A) : modelToG e A ≤ pieceCore e I :=
  le_centralizerPerfectCore (modelToG_perfect e hperf) (modelToG_le_centralizer e hA)

theorem modelToG_blockSL_le_pieceCore (I : Finset (Fin n))
    (hperf : ⁅blockSL (K := K) I, blockSL (K := K) I⁆ = blockSL I) :
    modelToG e (blockSL (K := K) I) ≤ pieceCore e I :=
  modelToG_le_pieceCore e (blockSL_le_centralizer_blockTorus I) hperf

theorem modelToG_blockSL_le_pieceCore_of_two_le [Finite K] {I : Finset (Fin n)}
    (hI : 2 ≤ I.card) (hK : 4 ≤ Nat.card K) :
    modelToG e (blockSL (K := K) I) ≤ pieceCore e I := by
  refine modelToG_blockSL_le_pieceCore e I ?_
  rcases hI.lt_or_eq with h | h
  · exact commutator_blockSL_eq_of_three_le h
  · exact commutator_blockSL_eq_of_card_two h.symm hK

theorem modelToG_blockSL_le_pieceCore_of_three_le {I : Finset (Fin n)} (hI : 3 ≤ I.card) :
    modelToG e (blockSL (K := K) I) ≤ pieceCore e I :=
  modelToG_blockSL_le_pieceCore e I (commutator_blockSL_eq_of_three_le hI)

theorem le_normalizer_pieceCore {t : G} (ht : t ∈ centralizer (L : Set G)) (I : Finset (Fin n)) :
    t ∈ normalizer (pieceCore e I : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _
    (mem_normalizer_modelToG_of_mem_centralizer e ht _)

theorem normalizer_modelToG_le_normalizer_pieceCore (I : Finset (Fin n)) :
    normalizer (modelToG e (blockTorus (K := K) I) : Set G) ≤ normalizer (pieceCore e I : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _

theorem symm_mem_normalizer_pieceCore {I : Finset (Fin n)} {x : LinearFlag.projectiveSL n K}
    (hx : x ∈ normalizer (blockTorus (K := K) I : Set (LinearFlag.projectiveSL n K))) :
    ((e.symm x : L) : G) ∈ normalizer (pieceCore e I : Set G) :=
  normalizer_modelToG_le_normalizer_pieceCore e I (symm_mem_normalizer_modelToG e hx)

@[expose] noncomputable def neighbourCore (N : Neighbour n) : Subgroup G :=
  centralizerPerfectCore (modelToG e (N.torus K))

theorem neighbourCore_root {a b : Fin n} (hab : a ≠ b) :
    neighbourCore e (.root a b hab) =
      centralizerPerfectCore (modelToG e (rootTorus (K := K) hab)) :=
  rfl

theorem neighbourCore_levi (a : Fin n) :
    neighbourCore e (.levi a) = centralizerPerfectCore (modelToG e (levTorus (K := K) a)) :=
  rfl

theorem neighbourCore_levi_eq_pieceCore (a : Fin n) :
    neighbourCore e (.levi a) = pieceCore e ({a}ᶜ : Finset (Fin n)) := by
  rw [neighbourCore_levi, pieceCore_def, blockTorus_compl_singleton]

theorem modelToG_torus_le_blockTorus (N : Neighbour n) {I : Finset (Fin n)} (hI : I ⊆ N.index) :
    modelToG e (N.torus K) ≤ modelToG e (blockTorus (K := K) I) :=
  modelToG_mono e (N.torus_le_blockTorus hI)

theorem modelToG_levTorus_le {a : Fin n} {I : Finset (Fin n)} (ha : a ∉ I) :
    modelToG e (levTorus (K := K) a) ≤ modelToG e (blockTorus (K := K) I) :=
  modelToG_mono e (levTorus_le_blockTorus ha)

theorem modelToG_rootTorus_le {a b : Fin n} (hab : a ≠ b) {I : Finset (Fin n)} (ha : a ∉ I)
    (hb : b ∉ I) :
    modelToG e (rootTorus (K := K) hab) ≤ modelToG e (blockTorus (K := K) I) :=
  modelToG_mono e (rootTorus_le_blockTorus hab ha hb)

theorem pieceCore_le_neighbourCore (N : Neighbour n) {I : Finset (Fin n)} (hI : I ⊆ N.index) :
    pieceCore e I ≤ neighbourCore e N :=
  centralizerPerfectCore_anti (modelToG_torus_le_blockTorus e N hI)

theorem modelToG_le_neighbourCore {N : Neighbour n} {A : Subgroup (LinearFlag.projectiveSL n K)}
    (hA : A ≤ centralizer (N.torus K : Set (LinearFlag.projectiveSL n K))) (hperf : ⁅A, A⁆ = A) :
    modelToG e A ≤ neighbourCore e N :=
  le_centralizerPerfectCore (modelToG_perfect e hperf) (modelToG_le_centralizer e hA)

theorem modelToG_blockSL_index_le_neighbourCore (N : Neighbour n)
    (hperf : ⁅blockSL (K := K) N.index, blockSL (K := K) N.index⁆ = blockSL N.index) :
    modelToG e (blockSL (K := K) N.index) ≤ neighbourCore e N :=
  modelToG_le_neighbourCore e (N.blockSL_index_le_centralizer_torus) hperf

theorem le_normalizer_neighbourCore {t : G} (ht : t ∈ centralizer (L : Set G))
    (N : Neighbour n) : t ∈ normalizer (neighbourCore e N : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _
    (mem_normalizer_modelToG_of_mem_centralizer e ht _)

theorem symm_mem_normalizer_neighbourCore {N : Neighbour n} {x : LinearFlag.projectiveSL n K}
    (hx : x ∈ normalizer (N.torus K : Set (LinearFlag.projectiveSL n K))) :
    ((e.symm x : L) : G) ∈ normalizer (neighbourCore e N : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _ (symm_mem_normalizer_modelToG e hx)

section Finite

variable [Finite G]

theorem pieceCore_eq_perfectCore_inf {X : Subgroup G} {I : Finset (Fin n)}
    (hX : X ≤ modelToG e (blockTorus (K := K) I)) :
    pieceCore e I = perfectCore (centralizerPerfectCore X ⊓
      centralizer (modelToG e (blockTorus (K := K) I) : Set G)) :=
  F4Pilot.centralizerPerfectCore_eq_of_le hX

theorem perfectCore_neighbour_inf_eq {X X' : Subgroup G} {I : Finset (Fin n)}
    (hX : X ≤ modelToG e (blockTorus (K := K) I))
    (hX' : X' ≤ modelToG e (blockTorus (K := K) I)) :
    perfectCore (centralizerPerfectCore X ⊓
        centralizer (modelToG e (blockTorus (K := K) I) : Set G)) =
      perfectCore (centralizerPerfectCore X' ⊓
        centralizer (modelToG e (blockTorus (K := K) I) : Set G)) :=
  F4Pilot.perfectCore_neighbour_eq_of_le_of_le hX hX'

theorem pieceCore_eq (N : Neighbour n) {I : Finset (Fin n)} (hI : I ⊆ N.index) :
    pieceCore e I =
      perfectCore (neighbourCore e N ⊓ centralizer (modelToG e (blockTorus (K := K) I) : Set G)) :=
  pieceCore_eq_perfectCore_inf e (modelToG_torus_le_blockTorus e N hI)

theorem perfectCore_neighbourCore_inf_eq {N N' : Neighbour n} {I : Finset (Fin n)}
    (hI : I ⊆ N.index) (hI' : I ⊆ N'.index) :
    perfectCore (neighbourCore e N ⊓ centralizer (modelToG e (blockTorus (K := K) I) : Set G)) =
      perfectCore (neighbourCore e N' ⊓
        centralizer (modelToG e (blockTorus (K := K) I) : Set G)) := by
  rw [← pieceCore_eq e N hI, ← pieceCore_eq e N' hI']

theorem pieceCore_eq_map_conj {I J : Finset (Fin n)} {x : LinearFlag.projectiveSL n K}
    (hx : (blockTorus (K := K) I).map (MulAut.conj x).toMonoidHom = blockTorus J) :
    pieceCore e J = (pieceCore e I).map (MulAut.conj ((e.symm x : L) : G)).toMonoidHom := by
  rw [pieceCore_def, pieceCore_def, ← hx, modelToG_map_conj, map_centralizerPerfectCore]

theorem neighbourCore_eq_map_conj {N N' : Neighbour n} {x : LinearFlag.projectiveSL n K}
    (hx : (N.torus K).map (MulAut.conj x).toMonoidHom = N'.torus K) :
    neighbourCore e N' =
      (neighbourCore e N).map (MulAut.conj ((e.symm x : L) : G)).toMonoidHom := by
  rw [neighbourCore, neighbourCore, ← hx, modelToG_map_conj, map_centralizerPerfectCore]

theorem exists_pieceCore_map_conj (ρ : Equiv.Perm (Fin n)) :
    ∃ w ∈ L, (∀ I : Finset (Fin n),
      pieceCore e (I.map ρ.toEmbedding) = (pieceCore e I).map (MulAut.conj w).toMonoidHom ∧
      modelToG e (blockSL (K := K) (I.map ρ.toEmbedding)) =
        (modelToG e (blockSL (K := K) I)).map (MulAut.conj w).toMonoidHom) ∧
      ∀ N : Neighbour n,
        neighbourCore e (N.map ρ) = (neighbourCore e N).map (MulAut.conj w).toMonoidHom := by
  obtain ⟨x, hxI, hxN⟩ := exists_conj_blockTorus (K := K) ρ
  refine ⟨((e.symm x : L) : G), (e.symm x).2, fun I => ⟨pieceCore_eq_map_conj e (hxI I).1, ?_⟩,
    fun N => neighbourCore_eq_map_conj e (hxN N)⟩
  rw [← (hxI I).2, modelToG_map_conj]

theorem exists_conjugate_pieceCore (ρ : Equiv.Perm (Fin n)) :
    ∃ w ∈ L, ∀ I : Finset (Fin n),
      conjugate (pieceCore e I) w = pieceCore e (I.map ρ.toEmbedding) := by
  obtain ⟨w, hw, h, -⟩ := exists_pieceCore_map_conj e ρ
  refine ⟨w⁻¹, L.inv_mem hw, fun I => ?_⟩
  rw [conjugate, inv_inv, (h I).1]

end Finite

end Transport

end CFSG.SeitzReduction.LinearPilot
