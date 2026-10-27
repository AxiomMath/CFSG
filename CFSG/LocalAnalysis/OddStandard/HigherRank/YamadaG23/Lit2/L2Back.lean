module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBrCtx
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBrPhi
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBrT
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBrS3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2KP
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Main
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.SU43Transport

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1
  CFSG.GH74.GLS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {Gh Zh : Subgroup Γ}

private lemma l2_order_four (hZG : Zh ≤ Gh) (hZ4 : Nonempty (↥Zh ≃* Multiplicative (ZMod 4))) :
    ∃ z ∈ Zh.subgroupOf Gh, orderOf z = 4 := by
  obtain ⟨e⟩ := hZ4
  let w : ↥Zh := e.symm (Multiplicative.ofAdd 1)
  have hw : orderOf w = 4 := by
    rw [MulEquiv.orderOf_eq, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  refine ⟨⟨(w : Γ), hZG w.2⟩, Subgroup.mem_subgroupOf.mpr w.2, ?_⟩
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hw]

private lemma l2_centIn_map_subtype (H : Subgroup ↥Gh) :
    centIn Gh (H.map Gh.subtype) = (centralizer (H : Set ↥Gh)).map Gh.subtype := by
  ext c
  constructor
  · rintro ⟨hcG, hcC⟩
    rw [Subgroup.mem_map]
    refine ⟨⟨c, hcG⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    apply Subtype.ext
    have hmem : (a : Γ) ∈ (H.map Gh.subtype : Set Γ) := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have h := hcC (a : Γ) hmem
    simpa using h
  · rintro hc
    rcases Subgroup.mem_map.mp hc with ⟨d, hd, rfl⟩
    refine ⟨d.2, ?_⟩
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    have hda := (Subgroup.mem_centralizer_iff.mp hd) a ha
    simpa using congrArg (fun y : ↥Gh => (y : Γ)) hda

theorem lit2_back [Finite Γ] (hZG : Zh ≤ Gh) {H : Subgroup ↥Gh} (hchar : H.Characteristic)
    (hq : CFSG.IsQuasisimple ↥H) (hZH : Zh.subgroupOf Gh ≤ H)
    (hcent : centralizer (H : Set ↥Gh) = litP (Zh.subgroupOf Gh))
    (hgoal : IsSU43 (↥H ⧸ CFSG.oddCore ↥H)) :
    ∃ Hh : Subgroup Γ, Hh ≤ Gh ∧ (Hh.subgroupOf Gh).Characteristic ∧ CFSG.IsQuasisimple ↥Hh ∧
      Zh ≤ Hh ∧ centIn Gh Hh = Zh ⊔ (CFSG.oddCore ↥Gh).map Gh.subtype ∧
      IsSU43 (↥Hh ⧸ CFSG.oddCore ↥Hh) := by
  let Hh : Subgroup Γ := H.map Gh.subtype
  have hHh_le : Hh ≤ Gh := Subgroup.map_subtype_le H
  have hsub : Hh.subgroupOf Gh = H := by
    dsimp only [Hh]
    exact Subgroup.comap_map_eq_self_of_injective Gh.subtype_injective H
  have hchar' : (Hh.subgroupOf Gh).Characteristic := by
    rw [hsub]
    exact hchar
  have e : ↥H ≃* ↥Hh := Subgroup.equivMapOfInjective H Gh.subtype Gh.subtype_injective
  have hq' : CFSG.IsQuasisimple ↥Hh := lit_isQuasisimple_of_mulEquiv e hq
  have hZ_le : Zh ≤ Hh := by
    intro z hz
    change z ∈ H.map Gh.subtype
    rw [Subgroup.mem_map]
    refine ⟨⟨z, hZG hz⟩, ?_, rfl⟩
    have hzH : (⟨z, hZG hz⟩ : ↥Gh) ∈ Zh.subgroupOf Gh := hz
    exact hZH hzH
  have hcentIn : centIn Gh Hh = Zh ⊔ (CFSG.oddCore ↥Gh).map Gh.subtype := by
    dsimp only [Hh]
    rw [l2_centIn_map_subtype H, hcent]
    change (Zh.subgroupOf Gh ⊔ CFSG.oddCore ↥Gh).map Gh.subtype =
      Zh ⊔ (CFSG.oddCore ↥Gh).map Gh.subtype
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hZG]
  exact ⟨Hh, hHh_le, hchar', hq', hZ_le, hcentIn,
    isSU43_quotient_oddCore_of_mulEquiv e.symm hgoal⟩

theorem gomi1RKP_of_inputs (hTab : L2Tables) (hI : GomiOuterPSLU4 ∧
    GomiOuterM22) (hLS : L2NoPauliPSL)
    (hUS : L2NoPauliPSU) (hOS : L2NoPauliPOmega) : Gomi1RKP := by
  intro Γ _ _ Gh Zh Ah t hcat hZG hZc hZ4 hZA hAG hrel hcomm hsq hq hsyl heven hnab ht ht1 ht2 h5a
    h5b hT h7 h8
  have h4 := l2_order_four (Gh := Gh) hZG hZ4
  have hg : LitGam Gh Zh Ah t :=
    lit_gam_of_hyps hZG hZc hZ4 hZA hAG hrel hcomm hsyl ht ht1 ht2 h5a h5b h7
  haveI : (Zh.subgroupOf Gh).Normal := lit_normal_Z hZc
  have hc : LitCtx (Zh.subgroupOf Gh) (Ah.subgroupOf Gh) := lit_ctx_of_hyps hg hZ4 hsq heven
  obtain ⟨φ, hφs, hφk⟩ := lit_phi_of_quotIso hZc hAG hq
  have hO := lit_hO hc hg hq hT φ hφs hφk
  obtain ⟨hTs, h72⟩ := lit_T_data hc hg hT
  have ht2sq : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht] at this
    simpa [pow_two] using this
  obtain ⟨H, hchar, hqs, hZH, hcent, hgoal⟩ :=
    lit2_main hc (lit_nonab_subgroupOf hAG hnab) φ hφs hφk hO (litConj Gh t ht1)
      (litConj_invol ht1 ht2sq) (litConj_Z ht1 ht2) hTs h72 (lit_conj_ne hZG ht1 h8) h4
      (fun H hH => l2_catalog_sub hcat H hH) hTab hI hLS hUS hOS
  exact lit2_back hZG hchar hqs hZH hcent hgoal

end CFSG.OddStandard.HigherRank.YamadaG23
