module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.E3Z2Frame
public import CFSG.CGT.PushingUpLit.SolKNA.R4.E3Z2C269
public import CFSG.CGT.PushingUpLit.SolKNA.R4.E3Z2C264
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3Sec
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3F3

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

section Cit3


@[expose] def TightE3Z2Sec163R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3FrameR r n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoZ2 (E3.secΩ R u) W) →
        ¬ TightInO2 (E3.secT htu ht) → Concl163 (secR R u) (E3.secT htu ht)

theorem tightE3Z2Sec163R_of_four_le {r n : ℕ} (hr : 4 ≤ r)
    (hList : SmallListR) (hO : NoDatumOtherR r) (h6 : ∀ m, TightLargeEdgeSR r m)
    (hM : Perp22Rest.Model163R r) : TightE3Z2Sec163R r n := by
  intro Y _ _ R S t J u hF htu ht Sb hex hedge hμ hnE2
  obtain ⟨Sq, hdq, hcq⟩ := secDatumCls_of_frameR hF htu ht
  have hdb := hdq.ofSylow Sb
  have hcb : TightClsR r (SecQ R u) (secR R u) Sb (E3.secT htu ht) :=
    ⟨⟨(Sylow.equiv Sb Sq).trans hcq.1.some⟩, hcq.2⟩
  obtain ⟨hdich, hzn, -⟩ := Perp22Rest.layerAut hr hF.large.below hF.large.tbelow hList hO h6 hM
    hF.card_secQ_lt hdb hcb hnE2 hedge
  exact concl163_of_quotAut hdb hcb.2.1 hcb.2.2 hzn hdich

variable {r n : ℕ}

theorem tightE3Z2R_of_frame_facts (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n)
    (hD : CIT3Below n → TightBelowR r n → TightS26DichR r n)
    (hSec : TightE3Z2Sec163R r n) (hGen : TightSecGenS3R r n) : TightE3Z2R r n := by
  intro Y _ _ R S t hL hcn hsp hα J hJ u hu htu ht Sb hex hedge hμ
  have hF : E3FrameR r n R S t J u := ⟨hL, hcn, hsp, hα, hJ, hu⟩
  have hT4 : Thm4RBelow r n := h4 hL.below hL.tbelow
  by_contra hnE2
  have hLC : TightLambdaCommR r n := tightLambdaCommR_of_four_le hr hT4 hL.tbelow hNo
  have h163 := hSec Y R S t J u hF htu ht Sb hex hedge hμ hnE2
  have hOJ := hF.omegaNbr_subset_orbOf htu ht h163
  obtain ⟨g, Sd, S', R', T, W, hgJ, hgu, hs⟩ := hF.exists_std8
  have hcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  have hα' : TightSepAlpha (conjSub g R) u := hgu ▸ hF.alpha.conj g
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hmu : MuIsoE4 (CoreAssembly.conjClass (tightCore (conjSub g R))) W ∨
      MuIsoS4 (CoreAssembly.conjClass (tightCore (conjSub g R))) W := by
    refine hs.muIso_E4_or_S4_of_uniq ?_
    rw [hfam]
    exact hF.partnerUniq_of_oneOrbit hOJ hF.t_mem_centralizer hF.t_mem_secH hμ (hfam ▸ hs.hW.1)
  rcases hmu with hE4 | hS4
  · have h1 := c264One_of_four_le hr hNo hT4 hL.tbelow hs hE4
    exact hF.false_of_c264One hLC hOJ htu ht h163 hcore hs hE4
      (fun x hx => hF.not_cent_of_c264One hcore h1 hx)
      (fun x hx hxt hcomm => hF.le_sup_of_secGen hOJ htu ht
        (fun s hcomm' hne hconj =>
          hGen Y R S t J u hF htu ht Sb hex hedge hnE2 s hcomm' hne hconj) hx hxt hcomm)
  · exact hs.not_muIsoS4_of_alpha (hD hL.below hL.tbelow) hα' hS4

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
