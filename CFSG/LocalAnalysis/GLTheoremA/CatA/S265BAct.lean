module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResAll
import CFSG.GroupTheory.PLayer.Transfer
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCD
import CFSG.GroupTheory.PLayer.CenterQuotientAction

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup map_glaPLayer_fixSubgroup_eq)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient_apply_mk)

structure NLAct (p : ℕ) {Ω : Type} [Group Ω] (X J B D : Subgroup Ω) : Prop where
  comp : GLAPComponent p X J
  le : D ≤ B
  norm : B ≤ Subgroup.normalizer (J : Set Ω)
  ker : ∀ e ∈ B, ∀ he : e ∈ Subgroup.normalizer (J : Set Ω), chevAut p J ⟨e, he⟩ = 1 ↔ e ∈ D
  layer : ∀ e ∈ B, e ∉ D → ∀ he : e ∈ Subgroup.normalizer (J : Set Ω),
    GLAPLayer p (fixSubgroup (chevAut p J ⟨e, he⟩)) = ⊥

variable {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ}

private theorem layer_fix_chevAut_eq_bot (hp : p.Prime) {J : Subgroup Ω} {e : Ω}
    (he : e ∈ Subgroup.normalizer (J : Set Ω)) (hep : IsPGroup p (Subgroup.zpowers e))
    (hbot : GLAPLayer p (J ⊓ cx e) = ⊥) :
    GLAPLayer p (fixSubgroup (chevAut p J ⟨e, he⟩)) = ⊥ := by
  have h1 : GLAPLayer p (fixSubgroup (J.normalizerMonoidHom ⟨e, he⟩)) = ⊥ := by
    have hmap : (fixSubgroup (J.normalizerMonoidHom ⟨e, he⟩)).map J.subtype = J ⊓ cx e := by
      rw [fixSubgroup_normalizerMonoidHom he]
      exact Subgroup.map_subgroupOf_eq_of_le inf_le_left
    have h := CFSG.glaPLayer_map_eq_of_injective hp J.subtype J.subtype_injective
      (fixSubgroup (J.normalizerMonoidHom ⟨e, he⟩))
    rw [hmap, hbot] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).1 h
  have h2 : GLAPLayer p (fixSubgroup (barAut p J ⟨e, he⟩)) = ⊥ := by
    rw [← map_fixSubgroup_pQuotHom hp he hep]
    by_contra hne
    exact (CFSG.glaPLayer_ne_bot_iff_map_ne_bot_of_coprime_ker hp (pQuotHom p J)
      (coprime_card_inf_ker_pQuotHom hp J _)).2 hne h1
  rw [← map_glaPLayer_fixSubgroup_eq (QuotientGroup.mk' (Subgroup.center (PQuot p J)))
    (by rw [QuotientGroup.ker_mk']) (barAut p J ⟨e, he⟩) (chevAut p J ⟨e, he⟩)
    (fun k => (onCenterQuotient_apply_mk (barAut p J ⟨e, he⟩) k).symm)
    (QuotientGroup.mk'_surjective _) hp, h2, Subgroup.map_bot]

theorem nlAct_of_nl (hp : p.Prime) {X J B D : Subgroup Ω} (hB : IsElemAbelian p B)
    (hJ : GLAPComponent p X J) (hN : B ≤ Subgroup.normalizer (J : Set Ω))
    (hD : D ≤ B ⊓ Subgroup.centralizer (J : Set Ω))
    (hnl : ∀ e ∈ B, e ∉ D → GLAPLayer p (J ⊓ cx e) = ⊥) : NLAct p X J B D where
  comp := hJ
  le := fun _ hd => (hD hd).1
  norm := hN
  ker e heB he := by
    refine ⟨fun h1 => ?_, fun heD =>
      (chevAut_eq_one_iff hp hJ he).2 (centMod_of_mem_centralizer (hD heD).2)⟩
    by_contra heD
    exact glaPComponent_ne_bot' (glaPLayer_inf_centralizer hp hJ (isPGroup_zpowers_of_mem hB heB)
      ((chevAut_eq_one_iff hp hJ he).1 h1)).1 (hnl e heB heD)
  layer e heB heD he :=
    layer_fix_chevAut_eq_bot hp he (isPGroup_zpowers_of_mem hB heB) (hnl e heB heD)

theorem QSNL.nlAct {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSNL p S B T x D K)
    (hpK : p ∣ Nat.card ↥K) : NLAct p (S ⊓ cs D) K B D := by
  obtain ⟨-, -, -, -, -, hKcomp, hDK⟩ := h.cfg.std
  have hJ : GLAPComponent p (S ⊓ cs D) K :=
    glaPComponent_of_isSubnormal' h.cfg.prime hKcomp.2.1
      (T171Sh.glaPComponent_self_of_dvd_card h.cfg.prime hKcomp.2.2 hpK)
  have hSN : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ =>
    (Subgroup.normalizer_eq_top_iff.2 h.cfg.normal) ▸ Subgroup.mem_top g
  exact nlAct_of_nl h.cfg.prime h.cfg.elem hJ (S171.B_norm_K h.cfg.elem hSN h.cfg.std) hDK.le h.nl

section Certificates


theorem QUNL.nlAct {S B T : Subgroup Ω} {x b : Ω} (h : QUNL p S B T x b) :
    NLAct p (S ⊓ cx b) (Ipart p S b) B (Dgrp b x) := by
  have hc := h.cfg
  obtain ⟨hJ, -⟩ := FR.i91CompAt_holds (G := Ω) hc.prime hc.odd ⊤ S b hc.comp hc.chev
    (hc.elem.2 b hc.hb) hc.prop hc.ipart
  have hBb : B ≤ cx b := fun g hg => Subgroup.mem_centralizer_iff.2 fun y hy => by
    rw [Set.mem_singleton_iff.1 hy]
    exact isElemAbelian_commute hc.elem hc.hb hg
  have hBX : B ≤ Subgroup.normalizer ((S ⊓ cx b : Subgroup Ω) : Set Ω) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(Subgroup.normalizer_eq_top_iff.2 hc.normal) ▸ Subgroup.mem_top g,
        Subgroup.le_normalizer (hBb hg)⟩
  refine nlAct_of_nl hc.prime hc.elem hJ (P65.le_normalizer_glaPLayer hBX) ?_ h.nl
  refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨⟨hc.hb, ?_⟩,
    Set.singleton_subset_iff.2 ⟨hc.xB, Subgroup.mem_centralizer_iff.2 fun y _ => hc.xcen y⟩⟩)
  exact Subgroup.mem_centralizer_iff.2 fun y hy =>
    (Subgroup.mem_centralizer_iff.1 (hJ.1 hy).2 b (Set.mem_singleton b)).symm

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.S265

end
