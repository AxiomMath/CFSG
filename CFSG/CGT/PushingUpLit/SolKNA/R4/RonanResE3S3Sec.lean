module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3Defs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26Layer
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3Lift1
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3Lift2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3GenA
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Gen
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocGlue
public import CFSG.CGT.PushingUpLit.SolKNA.R4.EdgeFalseT

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem secDatumCls_of_frameR (hF : E3FrameR r n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u) :
    ∃ Sq : Sylow 2 ↥(secR R u), TightDatum (secR R u) Sq (E3.secT htu ht) ∧
      TightClsR r (SecQ R u) (secR R u) Sq (E3.secT htu ht) := by
  have hd := hF.large.datum
  have hq := hF.large.cls.1
  have hJ := hF.maxAdj.1.2
  obtain ⟨-, hu2, hut, -, huK, -⟩ := hd.edge_involution hJ hF.inv
  have hcomm : ∀ r ∈ R, ⁅u, r⁆ ∈ oddCoreImg R := (hd.act_eq_one_iff hut).mp huK
  have huN : u ∈ Subgroup.normalizer (R : Set Y) := hd.le_normalizer hut
  have huC : u ∈ centralizerModOdd ⊤ R :=
    ⟨Subgroup.mem_top u, huN, mem_normalizer_oddCore_of_mem_normalizer huN, hcomm⟩
  obtain ⟨S', hS'⟩ := hd.exists_sylow_le_centralizer
    (Balance.isPGroup_zpowers_of_mul_self_eq_one hu2) (Subgroup.zpowers_le.mpr huC)
  have hS'u : (S' : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({u} : Set Y) :=
    hS'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers u)))
  obtain ⟨S₁, hd₁, ⟨e₁⟩⟩ := (hd.ofSylow S').restrict hS'u
  have hq' : Nonempty (↥(S₁ : Subgroup (R.subgroupOf (Subgroup.centralizer ({u} : Set Y)))) ≃*
      QuaternionGroup (2 ^ (r - 2))) := ⟨e₁.trans ((Sylow.equiv S' S).trans hq.some)⟩
  obtain ⟨_ht, S₂, hd₂, -, hcls⟩ := exists_clsR_subnormalClosure hd₁ hq'
  exact ⟨_, OddQ.datum hd₂ (CFSG.ComponentClassification.OddCore.odd_card _), hcls⟩

theorem tightE3S3Sec163R_of_four_le (hr : 4 ≤ r)
    (hList : SmallListR) (hO : NoDatumOtherR r) (h6 : ∀ m, TightLargeEdgeSR r m)
    (hM : Perp22Rest.Model163R r) : TightE3S3Sec163R r n := by
  intro Y _ _ R S t J u hF htu ht Sb hex hedge hμ hnE2
  obtain ⟨Sq, hdq, hcq⟩ := secDatumCls_of_frameR hF htu ht
  have hdb := hdq.ofSylow Sb
  have hcb : TightClsR r (SecQ R u) (secR R u) Sb (E3.secT htu ht) :=
    ⟨⟨(Sylow.equiv Sb Sq).trans hcq.1.some⟩, hcq.2⟩
  obtain ⟨hdich, hzn, -⟩ := Perp22Rest.layerAut hr hF.large.below hF.large.tbelow hList hO h6 hM
    hF.card_secQ_lt hdb hcb hnE2 hedge
  exact concl163_of_quotAut hdb hcb.2.1 hcb.2.2 hzn hdich

@[expose] def L2GenR (r : ℕ) : Prop :=
  4 ≤ r → ∀ (A : Type) [Group A] [Finite A] (T : Subgroup A) [T.Normal],
    TA3.SmallL2 ↥T → Subgroup.centralizer (T : Set A) = ⊥ →
    ∀ {R : Subgroup A} {S : Sylow 2 R} {z : A}, TightDatum R S z → TightClsR r A R S z →
    ∀ {s : A}, z ∈ T → z * s = s * z → s ≠ z → (∃ g : A, s = g * z * g⁻¹) →
      Subgroup.centralizer ({z} : Set A) ⊔ Subgroup.centralizer ({s} : Set A) = ⊤

theorem tightSecGenS3R_of_four_le (hr : 4 ≤ r)
    (hList : SmallListR) (hO : NoDatumOtherR r) (h6 : ∀ m, TightLargeEdgeSR r m)
    (hL2 : L2GenR r) : TightSecGenS3R r n := by
  intro Y _ _ R S t J u hF htu ht Sb hex hedge hnE2 s hcomm hne hconj
  obtain ⟨Sq, hdq, hcq⟩ := secDatumCls_of_frameR hF htu ht
  have hdb := hdq.ofSylow Sb
  have hcb : TightClsR r (SecQ R u) (secR R u) Sb (E3.secT htu ht) :=
    ⟨⟨(Sylow.equiv Sb Sq).trans hcq.1.some⟩, hcq.2⟩
  obtain ⟨L, hLn, hLq, hLC, hzn, hnt, hd', hc', hnO', hE', hTs, hTab, hTC, hfam⟩ :=
    layerIdent hr hF.large.below hF.large.tbelow hList hO h6 hF.card_secQ_lt hdb hcb hnE2 hedge
  haveI := hLn
  obtain ⟨g, hg⟩ := hconj
  apply sup_centralizer_of_quot hnt ⟨g, hg⟩
  set z := E3.secT htu ht with hzdef
  have hz2 : z * z = 1 := by rw [← pow_two, ← hdb.order, pow_orderOf_eq_one]
  have hsz : (QuotientGroup.mk s : SecQ R u ⧸ Subgroup.center (SecQ R u)) ≠ QuotientGroup.mk z := by
    intro h
    apply hne
    rw [QuotientGroup.eq] at h
    have hm' : z⁻¹ * s ∈ Subgroup.center (SecQ R u) := by
      have := (Subgroup.center (SecQ R u)).inv_mem h
      simpa [mul_inv_rev] using this
    obtain ⟨m, hm, hsm⟩ : ∃ m ∈ Subgroup.center (SecQ R u), s = z * m :=
      ⟨z⁻¹ * s, hm', by group⟩
    have := hnt g m hm (by rw [← hg, hsm])
    rw [hsm, this, mul_one]
  have hAz : orderOf (QuotientGroup.mk' (Subgroup.center (SecQ R u)) z) = 2 := hd'.order
  have hcommA : (QuotientGroup.mk z : SecQ R u ⧸ Subgroup.center (SecQ R u)) * QuotientGroup.mk s =
      QuotientGroup.mk s * QuotientGroup.mk z := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]
  have hconjA : ∃ h : SecQ R u ⧸ Subgroup.center (SecQ R u),
      (QuotientGroup.mk s : SecQ R u ⧸ Subgroup.center (SecQ R u)) = h * QuotientGroup.mk z * h⁻¹ :=
    ⟨QuotientGroup.mk g, by rw [hg]; simp⟩
  rcases hfam with hL2' | hL3' | hU3'
  · have hzT := (TwinSocF4.z_mem_of_comm2 hr hTC (socleFactsR_l2 hL2').comm2 hd' hc').1
    exact hL2 hr _ (socleOf L) hL2' hTC hd' hc' hzT hcommA hsz hconjA
  · have hzT := (TwinSocF4.z_mem_of_comm2 hr hTC (socleFactsR_l3 hL3').comm2 hd' hc').1
    exact gen_l3_of_normal (socleOf L) (by obtain ⟨p, f, hp, hp2, hf, -, hm⟩ := hL3'; exact ⟨p, f, hp, hp2, hf, hm⟩)
      hzT hAz hcommA hsz hconjA
  · have hzT := (TwinSocF4.z_mem_of_comm2 hr hTC (socleFactsR_u3 hU3').comm2 hd' hc').1
    exact gen_u3_of_normal (socleOf L) (by obtain ⟨p, f, hp, hp2, hf, -, hm⟩ := hU3'; exact ⟨p, f, hp, hp2, hf, hm⟩)
      hzT hAz hcommA hsz hconjA

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
