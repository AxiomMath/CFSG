module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Final19C
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt19
public import CFSG.GH74.Uniqueness.SU.SU1BgNormalEp2
public import CFSG.GH74.GLS.Stage2.Local.Closed

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Setup

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_Ep2 (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (M : Subgroup G) (hr : 3 ≤ pRank p ↥(Op p M)) :
    ∃ U : Subgroup G, U ≤ Op p M ∧ (U.subgroupOf (Op p M)).Normal ∧ IsElementaryAbelian p ↥U ∧
      Nat.card ↥U = p ^ 2 := by
  have hpg : IsPGroup p ↥(Op p M) := (pCore_isPGroup (G := ↥M) (p := p)).map M.subtype
  have hrk : 2 ≤ pRank p ↥(⊤ : Subgroup ↥(Op p M)) := by
    rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp.out,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    omega
  rcases CFSG.GH74.Uniqueness.SU.SU1.b_normal_Ep2 p hp.out ↥(Op p M) hpg ⊤ inferInstance hrk with
    ⟨E, hEn, -, hEe, hEc⟩ | ⟨h2, -⟩
  · refine ⟨E.map (Op p M).subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
    · have h1 : (E.map (Op p M).subtype).subgroupOf (Op p M) = E :=
        Subgroup.comap_map_eq_self_of_injective (Op p M).subtype_injective E
      rw [h1]
      exact hEn
    · exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr
        (CFSG.SectionRank.isElemAbelian_map
          ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mp hEe) _)
    · rw [Subgroup.card_map_of_injective (Op p M).subtype_injective, hEc]
  · exact absurd h2 hp2

end Setup

section Assembly

theorem prop19_1_of_lemmas (h26 : Leaf_Lemma26) (h192 : Lemma19_2) (h195 : Lemma19_5) : Prop19_1 := by
  intro G _ _ z k S M h hM
  subst hM
  by_contra hcon
  have hfail : Fail17 G z k S (Cen z) := ⟨h, fun hc => hcon ⟨hc.1, hc.2.2⟩⟩
  obtain ⟨p, hp, hp2, hrk⟩ := h192 G z k S (Cen z) hfail
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, hUle, hUn, hUe, hUc⟩ := exists_normal_Ep2 p hp2 (Cen z) hrk
  have hP : CtxP G z k S (Cen z) p := ⟨hfail, hp, hp2, hrk⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z) := h.ctx.sylow
  have h195' : ∀ t ∈ S, IsConj z t → inSubgroup (oResidual p) ⁅Cen z, zpowers t⁆ ≤
      centralizer ((Fpi {r | r.Prime ∧ r ≠ 2} (Cen z) : Subgroup G) : Set G) := by
    intro t htS htc
    by_cases htz : t = z
    · subst htz
      rw [commutator_Cen_zpowers_self]
      exact (Subgroup.map_subtype_le _).trans bot_le
    · exact h195 G z k S (Cen z) p U t ⟨hP, hUle, hUn, hUe, hUc, htc, htS, htz⟩
  obtain ⟨hB1, hB2⟩ := part_B hSyl (h26 G z k S h.ctx) p hp2 h195'
  apply hcon
  refine ⟨?_, fun _ => ?_⟩
  · show pLayerOf 2 (Cen z) = Em (Cen z)
    rw [pLayerOf_eq_map, Em_eq]
    congr 1
    refine pLayer_eq_layer_of_centralizes fun j hj f hf => ?_
    have hj' : (j : G) ∈ pLayerOf 2 (Cen z) := by
      rw [pLayerOf_eq_map]
      exact ⟨j, hj, rfl⟩
    exact Subtype.ext (hB1 (j : G) hj' (f : G) ⟨f, hf, rfl⟩)
  · exact isInternalDirectProduct_of_sylow_of_centralizes hSyl fun s hs f hf => hB2 s hs f hf

end Assembly

end CFSG.GH74.GLS.Stage2.Final.Thm4
