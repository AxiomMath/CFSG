module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalize

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)

local instance f4PilotAlignFieldNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Piece


variable (K : Type) [Field K]

@[expose] noncomputable def leviPiece (N : AmalgamNeighbour) (J : Finset (Fin (Tag.rank .F4))) :
    Subgroup (N.levi K) :=
  ((rootSpan .F4 K (amalgamRoots J)).subgroupOf (adjointGroup .F4 K)).subgroupOf (N.levi K)

variable {K}

theorem mem_leviPiece {N : AmalgamNeighbour} {J : Finset (Fin (Tag.rank .F4))} {x : N.levi K} :
    x ∈ leviPiece K N J ↔
      ((x : adjointGroup .F4 K) : ModGL .F4 K) ∈ rootSpan .F4 K (amalgamRoots J) :=
  Iff.rfl

end Piece

section Images


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  {L : Subgroup G} {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem FieldNeighbourIso.map_comap_centralizer {N : AmalgamNeighbour}
    (h : FieldNeighbourIso σ e N) (J : Finset (Fin (Tag.rank .F4))) :
    ((centralizer (((leviTorus (fixSubfield σ) J).map
        (baseChangeGL (fixSubfield σ).subtype) : Subgroup (ModGL .F4 K)) : Set (ModGL .F4 K))).comap
          ((adjointGroup .F4 K).subtype.comp (N.levi K).subtype)).map
        ((neighbourCore e N).subtype.comp h.Φ.toMonoidHom) =
      neighbourCore e N ⊓ centralizer (modelToG e (leviTorus (fixSubfield σ) J) : Set G) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨(h.Φ x).2, mem_centralizer_iff.2 fun g' hg' => ?_⟩
    obtain ⟨d, hdT, rfl⟩ := (mem_modelToG e).1 hg'
    have hd : ((d : adjointGroup .F4 (fixSubfield σ)) : ModGL .F4 (fixSubfield σ)) ∈
        leviTorus (fixSubfield σ) ∅ := leviTorus_anti (Finset.empty_subset J) hdT
    have hc : Commute ((x : adjointGroup .F4 K) : ModGL .F4 K)
        (baseChangeGL (fixSubfield σ).subtype (d : ModGL .F4 (fixSubfield σ))) :=
      (mem_centralizer_iff.1 hx _ ⟨_, hdT, rfl⟩).symm
    exact ((h.commute_iff hd x).2 hc).symm.eq
  · intro hg
    obtain ⟨hgE, hgC⟩ := mem_inf.1 hg
    refine ⟨h.Φ.symm ⟨g, hgE⟩, mem_comap.2 (mem_centralizer_iff.2 ?_), by simp⟩
    rintro _ ⟨d₀, hd₀, rfl⟩
    have hd₀C : d₀ ∈ adjointGroup .F4 (fixSubfield σ) := leviTorus_le_adjointGroup J hd₀
    have hd : ((⟨d₀, hd₀C⟩ : adjointGroup .F4 (fixSubfield σ)) : ModGL .F4 (fixSubfield σ)) ∈
        leviTorus (fixSubfield σ) ∅ := leviTorus_anti (Finset.empty_subset J) hd₀
    have hgd := mem_centralizer_iff.1 hgC _ (symm_mem_modelToG e (x := ⟨d₀, hd₀C⟩) hd₀)
    have hc : Commute ((h.Φ (h.Φ.symm ⟨g, hgE⟩) : neighbourCore e N) : G)
        ((e.symm ⟨d₀, hd₀C⟩ : L) : G) := by
      rw [MulEquiv.apply_symm_apply]
      exact hgd.symm
    exact ((h.commute_iff hd _).1 hc).symm.eq

theorem FieldNeighbourIso.map_leviPiece [Finite G] {N : AmalgamNeighbour}
    (h : FieldNeighbourIso σ e N) (hq : 4 ≤ Nat.card (fixSubfield σ))
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2) :
    ((leviPiece K N J).map h.Φ.toMonoidHom).map (neighbourCore e N).subtype = pieceCore e J := by
  have : Finite (N.levi K) := Finite.of_equiv _ h.Φ.symm.toEquiv
  have : Finite (ModGL .F4 K) := CFSG.LieType.Chevalley.finite_modGL
  set j : N.levi K →* ModGL .F4 K := (adjointGroup .F4 K).subtype.comp (N.levi K).subtype with hj
  have hjinj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  set C' := (centralizer (((leviTorus (fixSubfield σ) J).map
    (baseChangeGL (fixSubfield σ).subtype) : Subgroup (ModGL .F4 K)) : Set (ModGL .F4 K))).comap j
    with hC'
  have hrange : (⊤ : Subgroup (N.levi K)).map j = (N.levi K).map (adjointGroup .F4 K).subtype := by
    rw [hj, ← map_map, ← MonoidHom.range_eq_map, range_subtype]
  have hmapC : C'.map j = (N.levi K).map (adjointGroup .F4 K).subtype ⊓
      centralizer (((leviTorus (fixSubfield σ) J).map
        (baseChangeGL (fixSubfield σ).subtype) : Subgroup (ModGL .F4 K)) : Set (ModGL .F4 K)) := by
    rw [hC', map_comap_eq, MonoidHom.range_eq_map, hrange, inf_comm]
  have hpiece : (leviPiece K N J).map j = rootSpan .F4 K (amalgamRoots J) := by
    have hle : rootSpan .F4 K (amalgamRoots J) ≤ (N.levi K).map (adjointGroup .F4 K).subtype := by
      rw [← map_subtype_levi_f4Datum J]
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
    exact perfectCore_levi_inf_centralizer_map_leviTorus (fixSubfield σ).subtype hq hJ2 N hJ
  rw [pieceCore_eq e N hJ, ← h.map_comap_centralizer J, ← CFSG.Quasithin.map_perfectCore, hP,
    ← map_map]

theorem FieldNeighbourIso.map_leviPiece_eq [Finite G] {N N' : AmalgamNeighbour}
    (hN : FieldNeighbourIso σ e N) (hN' : FieldNeighbourIso σ e N')
    (hq : 4 ≤ Nat.card (fixSubfield σ)) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes)
    (hJ' : J ⊆ N'.nodes) (hJ2 : J.card ≤ 2) :
    ((leviPiece K N J).map hN.Φ.toMonoidHom).map (neighbourCore e N).subtype =
      ((leviPiece K N' J).map hN'.Φ.toMonoidHom).map (neighbourCore e N').subtype := by
  rw [hN.map_leviPiece hq hJ hJ2, hN'.map_leviPiece hq hJ' hJ2]

end Images

end CFSG.SeitzReduction.F4Pilot
