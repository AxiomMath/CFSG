module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf
public import CFSG.Quasithin.Vol2.KGFactC31J4A
public import CFSG.Quasithin.Vol2.KGFactJ4M4Card
public import CFSG.Quasithin.Vol2.KGFactJ4M2Cent
public import CFSG.Quasithin.EmptyFaithful.ONanJ4ZCentGroup
public import CFSG.Quasithin.Vol2.KGFactC31J4M4Fac

public section

namespace CFSG.SectionRank.QTK.Insp443.J4

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Sporadic.J4 CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.J4 CFSG.Quasithin.KGC31.J4M4 CFSG.Quasithin.J4Loc
open CFSG.Assembly.LowTwoRank (StatedSL)

theorem iso_id : Iso (MonoidHom.id G₀) :=
  ⟨Function.injective_id, MonoidHom.range_eq_top.mpr Function.surjective_id⟩

theorem isSporadic_J :
    IsSporadic .J4 G₀ :=
  ⟨(CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat).symm⟩

theorem conclK_of_le_Hj
    {L V MK : Subgroup G₀} (hLH : L ≤ CFSG.Sporadic.J4.Hj)
    (hHL : CFSG.Sporadic.J4.Hj ≤ Subgroup.normalizer (L : Set G₀)) (hper : ⁅L, L⁆ = L)
    (hne : L ≠ ⊥) : ConclK G₀ L V MK := by
  have F := hFacts iso_id
  rw [Subgroup.map_id, Subgroup.map_id, Subgroup.map_id] at F
  have hLeq : L = CFSG.Sporadic.J4.Hj :=
    eq_of_perfect_normal F.EH F.NE.ge F.comm F.min F.max F.CE hLH hHL hper hne
  subst hLeq
  have hH2 : ¬ IsPGroup 2 ↥CFSG.Sporadic.J4.Hj := fun h2 =>
    hne (eq_bot_of_perfect_of_isPGroup hper h2)
  have hOE := pCoreOf_eq_of_max F.EH F.NE.ge F.pGroup F.max hH2
  obtain ⟨ψ, hψ, hψk⟩ := F.quot
  have hpc : CFSG.pCore 2 ↥CFSG.Sporadic.J4.Hj = ψ.ker := by
    rw [hψk, ← Hex.pCoreOf_subgroupOf', hOE]
  let eQ : ↥CFSG.Sporadic.J4.Hj ⧸ CFSG.pCore 2 ↥CFSG.Sporadic.J4.Hj ≃*
      CFSG.Quasithin.A312M24.G24 :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  exact Or.inr ⟨isSporadic_J, Or.inl ⟨eQ⟩⟩

theorem conclK_of_le_M4
    {L V MK : Subgroup G₀} (hLM : L ≤ CFSG.Quasithin.KGJ4.M4)
    (hML : CFSG.Quasithin.KGJ4.M4 ≤ Subgroup.normalizer (L : Set G₀)) (hper : ⁅L, L⁆ = L)
    (hne : L ≠ ⊥) : ConclK G₀ L V MK := by
  have hM := j4Facts.mat
  have hc := chkF_true
  have hcard := CFSG.Quasithin.J4M4Card.card_M4
  have hLeq : L = CFSG.Quasithin.KGJ4.M4 :=
    eq_of_perfect_normal (F4_le_M4 hM hc) (M4_le_eNorm hM hc)
      (fun a ha b hb => eSub_comm _ a b ha hb) (m4_min hM hc) (m4_max hM hc hcard)
      (m4_CE hM hc hcard) hLM hML hper hne
  subst hLeq
  have hpc : CFSG.pCore 2 ↥CFSG.Quasithin.KGJ4.M4 = (piM4 hM hc).ker := by
    rw [ker_piM4 hM hc hcard, ← Hex.pCoreOf_subgroupOf', pCoreOf_M4 hM hc hcard]
  let eQ : ↥CFSG.Quasithin.KGJ4.M4 ⧸ CFSG.pCore 2 ↥CFSG.Quasithin.KGJ4.M4 ≃*
      ↥(StatedSL 5 (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (piM4_surjective hM hc))
  exact Or.inr ⟨isSporadic_J, Or.inr (Or.inl ⟨by decide, isPSL_of_equiv5 eQ⟩)⟩

section M2

open CFSG.Quasithin.J4M2


theorem B0grp_le_of_normal {L : Subgroup G₀} (hLM : L ≤ M2)
    (hML : M2 ≤ Subgroup.normalizer (L : Set G₀)) (hper : ⁅L, L⁆ = L) (hne : L ≠ ⊥) :
    B0grp ≤ L := by
  have hF := j4Facts
  have : Group.IsPerfect ↥L := ⟨commutator_eq_top_of_perfect hper⟩
  set ρL : ↥L →* Equiv.Perm (Fin 77) := (rho hF).comp (Subgroup.inclusion hLM) with hρL
  have hρLr : ρL.range ≤ Mbar := by
    rw [← range_rho_eq hF]
    rintro _ ⟨l, rfl⟩
    exact ⟨_, rfl⟩
  have hidx : Nat.card ↥Mbar = 2 * Nat.card ↥MbarP := by rw [card_Mbar hF, card_MbarP]
  obtain ⟨-, hcomm, -⟩ := card_eq_two_mul_facts MbarP_le_Mbar hidx
  have hperR : ⁅ρL.range, ρL.range⁆ = ρL.range := by
    have h1 : commutator ↥L = ⊤ := commutator_eq_top_of_perfect hper
    calc ⁅ρL.range, ρL.range⁆ = ⁅(⊤ : Subgroup ↥L).map ρL, (⊤ : Subgroup ↥L).map ρL⁆ := by
          rw [MonoidHom.range_eq_map]
      _ = (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆).map ρL := (Subgroup.map_commutator _ _ _).symm
      _ = (⊤ : Subgroup ↥L).map ρL := by rw [← commutator_def, h1]
      _ = ρL.range := (MonoidHom.range_eq_map _).symm
  have hRP : ρL.range ≤ MbarP := by
    rw [← hperR, Subgroup.commutator_le]
    intro x hx y hy
    exact hcomm x (hρLr hx) y (hρLr hy)
  have hn : (ρL.range.subgroupOf MbarP).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨l, hl⟩ := ha
    have hg : (g : Equiv.Perm (Fin 77)) ∈ (rho hF).range := by
      rw [range_rho_eq hF]; exact MbarP_le_Mbar g.2
    obtain ⟨m, hm⟩ := hg
    have hml : (m : G₀) * l * (m : G₀)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hML m.2) l).mp l.2
    refine ⟨⟨_, hml⟩, ?_⟩
    have e : Subgroup.inclusion hLM ⟨_, hml⟩ = m * Subgroup.inclusion hLM l * m⁻¹ :=
      Subtype.ext rfl
    change rho hF (Subgroup.inclusion hLM ⟨_, hml⟩) = _
    rw [e, map_mul, map_mul, map_inv, hm]
    change _ * rho hF (Subgroup.inclusion hLM l) * _ = _
    rw [show rho hF (Subgroup.inclusion hLM l) = ρL l from rfl, hl]
    rfl
  have hsP : IsSimpleGroup ↥MbarP := isSimpleGroup_MbarP
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρL.range.subgroupOf MbarP) with hb | ht
  ·
    exfalso
    have hLK : L ≤ Kgrp := by
      intro l hl
      have h1 : ρL ⟨l, hl⟩ = 1 := by
        have hm : ρL ⟨l, hl⟩ ∈ ρL.range := ⟨_, rfl⟩
        have hm' : (⟨ρL ⟨l, hl⟩, hRP hm⟩ : ↥MbarP) ∈ ρL.range.subgroupOf MbarP :=
          Subgroup.mem_subgroupOf.mpr hm
        rw [hb, Subgroup.mem_bot] at hm'
        exact congrArg Subtype.val hm'
      exact (rho_eq_one_iff hF _).mp h1
    haveI : Group.IsSolvable ↥Kgrp := isSolvable_Kgrp hF
    haveI : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLK)
    haveI : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hne
    exact absurd (inferInstance : Group.IsSolvable ↥L) (Group.IsPerfect.not_isSolvable (G := ↥L))
  ·
    have hPR : MbarP ≤ ρL.range := fun g hg => by
      have : (⟨g, hg⟩ : ↥MbarP) ∈ ρL.range.subgroupOf MbarP := by rw [ht]; trivial
      exact Subgroup.mem_subgroupOf.mp this
    refine CFSG.Quasithin.J4ZCent.le_of_perfect_of_solvable (isSolvable_Kgrp hF)
      (fun k hk l hl => (Subgroup.mem_normalizer_iff.mp (hML (Kgrp_le_M2 hF hk)) l).mp hl)
      (fun b hb => ?_) (B0grp_perfect hF)
    obtain ⟨bm, hbm⟩ : ∃ bm : ↥M2, (bm : G₀) = b := ⟨⟨b, B0grp_le_M2 hF hb⟩, rfl⟩
    have hbP : rho hF bm ∈ MbarP := by
      rw [← map_B0grp_eq hF]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hbm ▸ hb))
    obtain ⟨l, hl⟩ := hPR hbP
    have hk : (rho hF) ((Subgroup.inclusion hLM l)⁻¹ * bm) = 1 := by
      rw [map_mul, map_inv]
      exact inv_mul_eq_one.mpr hl
    have hk' := (rho_eq_one_iff hF ((Subgroup.inclusion hLM l)⁻¹ * bm)).mp hk
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hbm] at hk'
    exact ⟨l, l.2, _, hk', by group⟩

theorem false_of_le_M2 {L V : Subgroup G₀} (hLM : L ≤ M2)
    (hML : M2 ≤ Subgroup.normalizer (L : Set G₀)) (hper : ⁅L, L⁆ = L)
    (hVO : V ≤ pCoreOf 2 L) (hOC : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G₀))
    (hLV : L ≤ Subgroup.normalizer (V : Set G₀)) (hVc : V = ⁅V, L⁆) (hVne : V ≠ ⊥) : False := by
  have hF := j4Facts
  have hne : L ≠ ⊥ := fun h => hVne (by rw [hVc, h, Subgroup.commutator_bot_right])
  have hB0 := B0grp_le_of_normal hLM hML hper hne
  have hQL : Qgrp ≤ L := Qgrp_le_Kgrp.trans (Kgrp_le_B0grp.trans hB0)
  have hQO : Qgrp ≤ pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQL
      (fun l hl => Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx =>
        Qgrp_conj_mem hF l (hLM hl) x hx, fun hx => by
          have h := Qgrp_conj_mem hF l⁻¹ (M2.inv_mem (hLM hl)) _ hx
          simpa [mul_assoc] using h⟩)
      (isPGroup_Qgrp hF.mat)
  have hVC : V ≤ Subgroup.centralizer (Qgrp : Set G₀) := by
    rw [Subgroup.le_centralizer_iff]
    exact hQO.trans hOC
  rw [← CFSG.Quasithin.J4M2Core.pCoreOf_M2_eq] at hVC
  have hVz : V ≤ Subgroup.zpowers z0 := hVC.trans CFSG.Quasithin.J4M2Core.centralizer_pCoreOf_M2_le
  have hz2 : Nat.card (Subgroup.zpowers z0) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [sq]; exact CFSG.Sporadic.J4.QT.eta_sq (CFSG.Sporadic.J4.QT.elem_uJ hF.mat) 1131)
  have hV4 : Nat.card V ≤ 4 := (Subgroup.card_le_of_le hVz).trans (hz2.trans (by norm_num))
  exact hVne (by rw [hVc]; exact comm_eq_bot_of_card_le_four hper hLV hV4)

end M2

end CFSG.SectionRank.QTK.Insp443.J4
