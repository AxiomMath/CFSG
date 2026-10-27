module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalize

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)

local instance e6PilotAlignFieldNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Piece

variable (K : Type) [Field K]

@[expose] noncomputable def leviPiece (N : E6Neighbour) (J : Finset (Fin (Tag.rank .E6))) :
    Subgroup (N.levi K) :=
  ((rootSpan .E6 K (amalgamRoots J)).subgroupOf (adjointGroup .E6 K)).subgroupOf (N.levi K)

variable {K}

end Piece

section Images

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem FieldNeighbourIso.map_comap_centralizer {N : E6Neighbour}
    (h : FieldNeighbourIso σ e N) (J : Finset (Fin (Tag.rank .E6))) :
    ((centralizer (((leviTorus (fixSubfield σ) J ⊓ adjointGroup .E6 (fixSubfield σ)).map
        (baseChangeGL (fixSubfield σ).subtype) : Subgroup (ModGL .E6 K)) :
          Set (ModGL .E6 K))).comap
          ((adjointGroup .E6 K).subtype.comp (N.levi K).subtype)).map
        ((neighbourCore e N).subtype.comp h.Φ.toMonoidHom) =
      neighbourCore e N ⊓ centralizer (modelToG e (leviTorus (fixSubfield σ) J) : Set G) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨(h.Φ x).2, mem_centralizer_iff.2 fun g' hg' => ?_⟩
    obtain ⟨d, hdT, rfl⟩ := (mem_modelToG e).1 hg'
    have hc : Commute ((x : adjointGroup .E6 K) : ModGL .E6 K)
        (baseChangeGL (fixSubfield σ).subtype (d : ModGL .E6 (fixSubfield σ))) :=
      (mem_centralizer_iff.1 hx _ ⟨_, ⟨hdT, d.2⟩, rfl⟩).symm
    exact ((h.commute_iff_of_mem_leviTorus hdT x).2 hc).symm.eq
  · intro hg
    obtain ⟨hgE, hgC⟩ := mem_inf.1 hg
    refine ⟨h.Φ.symm ⟨g, hgE⟩, mem_comap.2 (mem_centralizer_iff.2 ?_), by simp⟩
    rintro _ ⟨d₀, ⟨hd₀, hd₀C⟩, rfl⟩
    have hgd := mem_centralizer_iff.1 hgC _ (symm_mem_modelToG e (x := ⟨d₀, hd₀C⟩) hd₀)
    have hc : Commute ((h.Φ (h.Φ.symm ⟨g, hgE⟩) : neighbourCore e N) : G)
        ((e.symm ⟨d₀, hd₀C⟩ : L) : G) := by
      rw [MulEquiv.apply_symm_apply]
      exact hgd.symm
    exact ((h.commute_iff_of_mem_leviTorus (d := ⟨d₀, hd₀C⟩) hd₀ _).1 hc).symm.eq

theorem FieldNeighbourIso.map_leviPiece [Finite G] {N : E6Neighbour}
    (h : FieldNeighbourIso σ e N) (hq : 4 ≤ Nat.card (fixSubfield σ))
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2) :
    ((leviPiece K N J).map h.Φ.toMonoidHom).map (neighbourCore e N).subtype = pieceCore e J := by
  set j : N.levi K →* ModGL .E6 K := (adjointGroup .E6 K).subtype.comp (N.levi K).subtype with hj
  have hjinj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  set C' := (centralizer (((leviTorus (fixSubfield σ) J ⊓ adjointGroup .E6 (fixSubfield σ)).map
    (baseChangeGL (fixSubfield σ).subtype) : Subgroup (ModGL .E6 K)) : Set (ModGL .E6 K))).comap j
    with hC'
  have hrange : (⊤ : Subgroup (N.levi K)).map j = (N.levi K).map (adjointGroup .E6 K).subtype := by
    rw [hj, ← map_map, ← MonoidHom.range_eq_map, range_subtype]
  have hmapC : C'.map j = (N.levi K).map (adjointGroup .E6 K).subtype ⊓
      centralizer (((leviTorus (fixSubfield σ) J ⊓ adjointGroup .E6 (fixSubfield σ)).map
        (baseChangeGL (fixSubfield σ).subtype) : Subgroup (ModGL .E6 K)) : Set (ModGL .E6 K)) := by
    rw [hC', map_comap_eq, MonoidHom.range_eq_map, hrange, inf_comm]
  have hpiece : (leviPiece K N J).map j = rootSpan .E6 K (amalgamRoots J) := by
    have hle : rootSpan .E6 K (amalgamRoots J) ≤ (N.levi K).map (adjointGroup .E6 K).subtype := by
      rw [← map_subtype_levi_adjDatumE6 J]
      exact map_mono (levi_le_neighbourLevi hJ)
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hg
      obtain ⟨y, hy, rfl⟩ := hle hg
      exact ⟨⟨y, hy⟩, hg, rfl⟩
  have hP : perfectCore C' = leviPiece K N J := by
    apply map_injective hjinj
    rw [CFSG.Quasithin.map_perfectCore, hmapC, hpiece]
    exact perfectCore_levi_inf_centralizer_map_leviTorus_inf (fixSubfield σ).subtype hq hJ2 N hJ
  rw [pieceCore_eq e N hJ, ← h.map_comap_centralizer J, ← CFSG.Quasithin.map_perfectCore, hP,
    ← map_map]

end Images

end CFSG.SeitzReduction.E6Pilot
