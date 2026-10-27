module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapBasic
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignField

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG)

local instance e8PilotSwapPiecesNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

section Centralizer


variable (K : Type) [Field K]

@[expose] noncomputable def swapLeviCentralizer (N : E8Neighbour)
    (J : Finset (Fin (Tag.rank .E8))) : Subgroup (N.levi K) :=
  (centralizer (leviTorus K J : Set (ModGL .E8 K))).comap
    ((adjointGroup .E8 K).subtype.comp (N.levi K).subtype)

variable {K}

theorem mem_swapLeviCentralizer {N : E8Neighbour} {J : Finset (Fin (Tag.rank .E8))}
    {x : N.levi K} : x ∈ swapLeviCentralizer K N J ↔
      ∀ d ∈ leviTorus K J, Commute d ((x : adjointGroup .E8 K) : ModGL .E8 K) := by
  simp only [swapLeviCentralizer, mem_comap, mem_centralizer_iff, MonoidHom.coe_comp,
    coe_subtype, Function.comp_apply, SetLike.mem_coe]
  rfl

end Centralizer

section PiecesMain


variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E8 K} {t : G} {N : E8Neighbour}

theorem SwapNeighbourIso.map_centralizer_prod [Finite K] [CharP K 2]
    (h : SwapNeighbourIso e t N) (J : Finset (Fin (Tag.rank .E8))) :
    ((swapLeviCentralizer K N J).prod (swapLeviCentralizer K N J)).map
        ((neighbourCore e N).subtype.comp h.Φ.toMonoidHom) =
      neighbourCore e N ⊓ centralizer (modelToG e (leviTorus K J) : Set G) := by
  ext g
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    refine mem_inf.2 ⟨(h.Φ (x, y)).2, mem_centralizer_iff.2 fun g' hg' => ?_⟩
    obtain ⟨d, hdT, rfl⟩ := (mem_modelToG e).1 hg'
    have hd : (d : ModGL .E8 K) ∈ torusGroup .E8 K := leviTorus_le_torusGroup J hdT
    have hc := (h.commute_iff hd x y).2 ⟨(mem_swapLeviCentralizer.1 hx _ hdT).symm,
      (mem_swapLeviCentralizer.1 hy _ hdT).symm⟩
    exact hc.symm.eq
  · intro hg
    obtain ⟨hgE, hgC⟩ := mem_inf.1 hg
    refine ⟨h.Φ.symm ⟨g, hgE⟩, ⟨?_, ?_⟩, by simp⟩
    all_goals
      refine mem_swapLeviCentralizer.2 fun d₀ hd₀ => ?_
      have hd₀C : d₀ ∈ adjointGroup .E8 K := leviTorus_le_adjointGroup J hd₀
      have hd : ((⟨d₀, hd₀C⟩ : adjointGroup .E8 K) : ModGL .E8 K) ∈ torusGroup .E8 K :=
        leviTorus_le_torusGroup J hd₀
      have hgd := mem_centralizer_iff.1 hgC _ (symm_mem_modelToG e (x := ⟨d₀, hd₀C⟩) hd₀)
      have hc : Commute ((h.Φ (h.Φ.symm ⟨g, hgE⟩) : neighbourCore e N) : G)
          ((e.symm ⟨d₀, hd₀C⟩ : L) : G) := by
        rw [MulEquiv.apply_symm_apply]
        exact hgd.symm
      have hc' := (h.commute_iff hd _ _).1 hc
    · exact hc'.1.symm
    · exact hc'.2.symm

theorem SwapNeighbourIso.map_leviPiece [Finite G] [Finite K] [CharP K 2]
    (h : SwapNeighbourIso e t N) (hq : 4 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .E8))}
    (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2) :
    ((leviPiece K N J).prod (leviPiece K N J)).map
        ((neighbourCore e N).subtype.comp h.Φ.toMonoidHom) = pieceCore e J := by
  set j : N.levi K →* ModGL .E8 K := (adjointGroup .E8 K).subtype.comp (N.levi K).subtype with hj
  have hjinj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  have hrange : (⊤ : Subgroup (N.levi K)).map j = (N.levi K).map (adjointGroup .E8 K).subtype := by
    rw [hj, ← map_map, ← MonoidHom.range_eq_map, range_subtype]
  have hmapC : (swapLeviCentralizer K N J).map j = (N.levi K).map (adjointGroup .E8 K).subtype ⊓
      centralizer (leviTorus K J : Set (ModGL .E8 K)) := by
    rw [swapLeviCentralizer, ← hj, map_comap_eq, MonoidHom.range_eq_map, hrange, inf_comm]
  have hpiece : (leviPiece K N J).map j = rootSpan .E8 K (amalgamRoots J) := by
    have hle : rootSpan .E8 K (amalgamRoots J) ≤ (N.levi K).map (adjointGroup .E8 K).subtype := by
      rw [← map_subtype_levi_adjDatumE8 J]
      exact map_mono (levi_le_neighbourLevi hJ)
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hg
      obtain ⟨y, hy, rfl⟩ := hle hg
      exact ⟨⟨y, hy⟩, hg, rfl⟩
  have hP : perfectCore (swapLeviCentralizer K N J) = leviPiece K N J := by
    apply map_injective hjinj
    rw [CFSG.Quasithin.map_perfectCore, hmapC, hpiece]
    exact perfectCore_levi_inf_centralizer_leviTorus hq hJ2 N hJ
  rw [pieceCore_eq e N hJ, ← h.map_centralizer_prod J, ← CFSG.Quasithin.map_perfectCore,
    F4Pilot.perfectCore_subgroupProd, hP]

theorem mem_leviPiece_of_mem_levi {J : Finset (Fin (Tag.rank .E8))} (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J) :
    (⟨x, levi_le_neighbourLevi hJ x.2⟩ : N.levi K) ∈ leviPiece K N J :=
  mem_leviPiece.2 (mem_subgroupOf.1 ((levi_adjDatumE8_eq (K := K) J).le x.2))

theorem mem_levi_of_mem_leviPiece {J : Finset (Fin (Tag.rank .E8))} {z : N.levi K}
    (hz : z ∈ leviPiece K N J) :
    (z : adjointGroup .E8 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J := by
  rw [levi_adjDatumE8_eq, mem_subgroupOf]
  exact mem_leviPiece.1 hz

theorem SwapNeighbourIso.exists_eq_of_mem_pieceCore [Finite G] [Finite K] [CharP K 2]
    (h : SwapNeighbourIso e t N) (hq : 4 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .E8))}
    (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2) {g : G} (hg : g ∈ pieceCore e J) :
    ∃ x y : CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J,
      g = h.fst hJ x * h.snd hJ y := by
  rw [← h.map_leviPiece hq hJ hJ2] at hg
  obtain ⟨⟨z₁, z₂⟩, ⟨hz₁, hz₂⟩, rfl⟩ := hg
  exact ⟨⟨_, mem_levi_of_mem_leviPiece hz₁⟩, ⟨_, mem_levi_of_mem_leviPiece hz₂⟩,
    h.coe_apply_eq_mul z₁ z₂⟩

theorem SwapNeighbourIso.range_fst_sup_range_snd_le (h : SwapNeighbourIso e t N)
    {J : Finset (Fin (Tag.rank .E8))} (hJ : J ⊆ N.nodes) :
    (h.fst hJ).range ⊔ (h.snd hJ).range ≤ ((leviPiece K N J).prod (leviPiece K N J)).map
        ((neighbourCore e N).subtype.comp h.Φ.toMonoidHom) := by
  refine sup_le ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨(⟨x, levi_le_neighbourLevi hJ x.2⟩, 1), ⟨mem_leviPiece_of_mem_levi hJ x, one_mem _⟩,
      rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨(1, ⟨x, levi_le_neighbourLevi hJ x.2⟩), ⟨one_mem _, mem_leviPiece_of_mem_levi hJ x⟩,
      rfl⟩

theorem SwapNeighbourIso.range_fst_sup_range_snd [Finite G] [Finite K] [CharP K 2]
    (h : SwapNeighbourIso e t N) (hq : 4 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .E8))}
    (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2) :
    (h.fst hJ).range ⊔ (h.snd hJ).range = pieceCore e J := by
  refine le_antisymm ((h.range_fst_sup_range_snd_le hJ).trans (h.map_leviPiece hq hJ hJ2).le)
    fun g hg => ?_
  obtain ⟨x, y, rfl⟩ := h.exists_eq_of_mem_pieceCore hq hJ hJ2 hg
  exact mul_mem (mem_sup_left ⟨x, rfl⟩) (mem_sup_right ⟨y, rfl⟩)

theorem SwapNeighbourIso.range_fst_le_pieceCore [Finite G] [Finite K] [CharP K 2]
    (h : SwapNeighbourIso e t N) (hq : 4 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .E8))}
    (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2) : (h.fst hJ).range ≤ pieceCore e J :=
  le_sup_left.trans (h.range_fst_sup_range_snd hq hJ hJ2).le

theorem SwapNeighbourIso.range_snd_le_pieceCore [Finite G] [Finite K] [CharP K 2]
    (h : SwapNeighbourIso e t N) (hq : 4 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .E8))}
    (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2) : (h.snd hJ).range ≤ pieceCore e J :=
  le_sup_right.trans (h.range_fst_sup_range_snd hq hJ hJ2).le

end PiecesMain

end CFSG.SeitzReduction.E8Pilot
