module

import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParam

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

section Embed

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]

@[expose] noncomputable def neighbourBlockHom (e : L ≃* LinearFlag.projectiveSL n K)
    (Nb : Neighbour n) {m : ℕ} (eN : Nb.index ≃ Fin m) :
    SpecialLinearGroup (Fin m) K →* centralizer (modelToG e (Nb.torus K) : Set G) :=
  MonoidHom.codRestrict (L.subtype.comp (e.symm.toMonoidHom.comp ((LinearFlag.proj n K).comp
      ((blockSpecialLinear (K := K) Nb.index).subtype.comp (blockSLEquiv Nb.index eN).toMonoidHom))))
    _ fun x => modelToG_le_centralizer e Nb.blockSL_index_le_centralizer_torus
      (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv Nb.index eN x).2))

theorem coe_neighbourBlockHom (e : L ≃* LinearFlag.projectiveSL n K) (Nb : Neighbour n) {m : ℕ}
    (eN : Nb.index ≃ Fin m) (x : SpecialLinearGroup (Fin m) K) :
    ((neighbourBlockHom e Nb eN x : centralizer (modelToG e (Nb.torus K) : Set G)) : G) =
      ((e.symm (LinearFlag.proj n K (blockSLEquiv Nb.index eN x)) : L) : G) :=
  rfl

theorem range_neighbourBlockHom (e : L ≃* LinearFlag.projectiveSL n K) (Nb : Neighbour n) {m : ℕ}
    (eN : Nb.index ≃ Fin m) :
    (neighbourBlockHom e Nb eN).range =
      (modelToG e (blockSL (K := K) Nb.index)).subgroupOf
        (centralizer (modelToG e (Nb.torus K) : Set G)) := by
  ext ⟨g, hg⟩
  rw [mem_subgroupOf, MonoidHom.mem_range]
  change (∃ x, neighbourBlockHom e Nb eN x = ⟨g, hg⟩) ↔ g ∈ modelToG e (blockSL Nb.index)
  constructor
  · rintro ⟨x, hx⟩
    have hx' : ((e.symm (LinearFlag.proj n K (blockSLEquiv Nb.index eN x)) : L) : G) = g :=
      congrArg Subtype.val hx
    rw [← hx']
    exact symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv Nb.index eN x).2)
  · intro h
    obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 h
    obtain ⟨A, hA, rfl⟩ := hy
    obtain ⟨x, hx⟩ := (blockSLEquiv Nb.index eN).surjective ⟨A, hA⟩
    refine ⟨x, Subtype.ext ?_⟩
    rw [coe_neighbourBlockHom, hx]

variable (e : L ≃* LinearFlag.projectiveSL n K) (Nb : Neighbour n) {m : ℕ} (eN : Nb.index ≃ Fin m)

@[expose] noncomputable def neighbourBarHom :
    SpecialLinearGroup (Fin m) K →* centralizer (modelToG e (Nb.torus K) : Set G) ⧸
      oddCore (centralizer (modelToG e (Nb.torus K) : Set G)) :=
  (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))).comp
    (neighbourBlockHom e Nb eN)

theorem range_neighbourBarHom :
    (neighbourBarHom e Nb eN).range =
      ((modelToG e (blockSL (K := K) Nb.index)).subgroupOf
        (centralizer (modelToG e (Nb.torus K) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))) := by
  rw [neighbourBarHom, MonoidHom.range_comp, range_neighbourBlockHom]

theorem ker_neighbourBarHom (hm : 3 ≤ m)
    (hne : ((modelToG e (blockSL (K := K) Nb.index)).subgroupOf
        (centralizer (modelToG e (Nb.torus K) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))) ≠ ⊥)
    (hZ : center (((modelToG e (blockSL (K := K) Nb.index)).subgroupOf
        (centralizer (modelToG e (Nb.torus K) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G))))) = ⊥) :
    (neighbourBarHom e Nb eN).ker = center (SpecialLinearGroup (Fin m) K) := by
  set φ := neighbourBarHom e Nb eN with hφ
  refine le_antisymm (LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup hm) ?_) ?_
  · by_contra h
    push Not at h
    apply hne
    rw [← range_neighbourBarHom, eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    exact (mem_bot).mpr (h x)
  · intro z hz
    have hZ' : center φ.range = ⊥ := by
      rw [hφ, range_neighbourBarHom]
      exact hZ
    have hzc : (⟨φ z, z, rfl⟩ : φ.range) ∈ center φ.range := by
      rw [mem_center_iff]
      rintro ⟨_, x, rfl⟩
      apply Subtype.ext
      change φ x * φ z = φ z * φ x
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz x)]
    rw [hZ', mem_bot] at hzc
    exact congrArg Subtype.val hzc

theorem exists_projectiveSL_embedding (hm : 3 ≤ m)
    (hne : ((modelToG e (blockSL (K := K) Nb.index)).subgroupOf
        (centralizer (modelToG e (Nb.torus K) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))) ≠ ⊥)
    (hZ : center (((modelToG e (blockSL (K := K) Nb.index)).subgroupOf
        (centralizer (modelToG e (Nb.torus K) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G))))) = ⊥)
    {Kc : Subgroup (centralizer (modelToG e (Nb.torus K) : Set G) ⧸
      oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))}
    (hDK : ((modelToG e (blockSL (K := K) Nb.index)).subgroupOf
        (centralizer (modelToG e (Nb.torus K) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G)))) ≤ Kc) :
    ∃ ε : LinearFlag.projectiveSL m K →* Kc, Function.Injective ε ∧
      ε.range = (((modelToG e (blockSL (K := K) Nb.index)).subgroupOf
        (centralizer (modelToG e (Nb.torus K) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (Nb.torus K) : Set G))))).subgroupOf
            Kc ∧
      ∀ x, ((ε (LinearFlag.proj m K x) : Kc) : centralizer (modelToG e (Nb.torus K) : Set G) ⧸
        oddCore (centralizer (modelToG e (Nb.torus K) : Set G))) = neighbourBarHom e Nb eN x := by
  have hker := ker_neighbourBarHom e Nb eN hm hne hZ
  have hsc : LinearFlag.scalars m K ≤ (neighbourBarHom e Nb eN).ker := by
    rw [hker, LinearFlag.scalars_eq_center]
  set ε₀ := QuotientGroup.lift (LinearFlag.scalars m K) (neighbourBarHom e Nb eN) hsc with hε₀
  have hε₀app : ∀ x, ε₀ (LinearFlag.proj m K x) = neighbourBarHom e Nb eN x := fun x =>
    QuotientGroup.lift_mk' _ hsc x
  have hmem : ∀ y, ε₀ y ∈ Kc := by
    intro y
    obtain ⟨x, rfl⟩ := LinearFlag.proj_surjective m K y
    rw [hε₀app]
    exact hDK (by rw [← range_neighbourBarHom]; exact ⟨x, rfl⟩)
  refine ⟨ε₀.codRestrict Kc hmem, ?_, ?_, fun x => hε₀app x⟩
  ·
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨x, rfl⟩ := LinearFlag.proj_surjective m K y
    have h1 : neighbourBarHom e Nb eN x = 1 := by
      rw [← hε₀app]
      exact congrArg Subtype.val hy
    have h2 : x ∈ (neighbourBarHom e Nb eN).ker := h1
    rw [hker] at h2
    rw [LinearFlag.proj_eq_one_iff, LinearFlag.scalars_eq_center]
    exact h2
  ·
    ext ⟨k, hk⟩
    rw [mem_subgroupOf, MonoidHom.mem_range, ← range_neighbourBarHom]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := LinearFlag.proj_surjective m K y
      have h1 : neighbourBarHom e Nb eN x = k := by
        rw [← hε₀app]
        exact congrArg Subtype.val hy
      exact ⟨x, h1⟩
    · rintro ⟨x, hx⟩
      exact ⟨LinearFlag.proj m K x, Subtype.ext (by
        change ε₀ (LinearFlag.proj m K x) = k
        rw [hε₀app, hx])⟩

end Embed

end CFSG.SeitzReduction.LinearPilot
