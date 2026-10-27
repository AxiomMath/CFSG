module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassYRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZBasic
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClasses

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff)

local instance e7ClassYBruhatNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def yAS : ModGL .E7 K := rootProd .E7 K yFrame fun _ => 1

@[expose] def yCoeff : (Fin Tag.E7.rank → ℤ) → K := fun β => if β ∈ yFrame then 1 else 0

theorem rootProd_yPsi_yCoeff : rootProd .E7 K yPsi yCoeff = yAS K := by
  rw [show (yCoeff : (Fin Tag.E7.rank → ℤ) → K) =
      fun ρ => if ρ ∈ yFrame then (fun _ => (1 : K)) ρ else 0 from rfl,
    E6Pilot.rootProd_ite_mem, yPsi_filter_yFrame]
  rfl

theorem coe_e7ASRep_one : (e7ASRep K 1 : ModGL .E7 K) = yAS K := rfl

theorem yCoeff_eq_zero_of_not_mem {β : Fin Tag.E7.rank → ℤ} (h : β ∉ yFrame) :
    (yCoeff β : K) = 0 := by
  simp only [yCoeff]
  rw [ite_eq_right h]

theorem yPsi_comm : RootCommFamily .E7 K yPsi := fun _ hβ _ hβ' s t =>
  CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (isRoot_of_mem_yPsi hβ)
    (isRoot_of_mem_yPsi hβ') (ne_neg_of_mem_yPsi hβ hβ') (yPsi_add_not_isRoot hβ hβ') s t

theorem conj_hyp_of_yLevel_nonneg {α : Fin Tag.E7.rank → ℤ} (hα0 : 0 ≤ yLevel α) :
    ∀ β ∈ yPsi, α ≠ -β ∧ (IsRoot .E7 (α + β) → α + β ∈ yPsi) := by
  intro β hβ
  have hβ2 := level_of_mem_yPsi hβ
  refine ⟨fun h => ?_, fun hr => mem_yPsi_of_level hr ?_⟩
  · have : yLevel α = -yLevel β := by rw [h, yLevel_neg]
    omega
  · rw [yLevel_add]
    omega

theorem conj_rootProd_yPsi [CharP K 2] {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α)
    (hα0 : 0 ≤ yLevel α) (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    pinnedX .E7 K α t * rootProd .E7 K yPsi c * (pinnedX .E7 K α t)⁻¹ =
      rootProd .E7 K yPsi (conjCoeff α t yPsi c) :=
  E6Pilot.conj_rootProd (Or.inr (Or.inr (Or.inl rfl))) CharTwo.two_eq_zero yPsi_nodup
    (fun _ hβ => isRoot_of_mem_yPsi hβ) yPsi_comm hα (conj_hyp_of_yLevel_nonneg hα0) t c

variable (K) in
@[expose] noncomputable def yInvSubgroup (P : ((Fin Tag.E7.rank → ℤ) → K) → Prop) :
    Subgroup (ModGL .E7 K) where
  carrier := {g | ∀ c, P c →
    (∃ c', g * rootProd .E7 K yPsi c * g⁻¹ = rootProd .E7 K yPsi c' ∧ P c') ∧
      (∃ c', g⁻¹ * rootProd .E7 K yPsi c * g = rootProd .E7 K yPsi c' ∧ P c')}
  mul_mem' := by
    intro g h hg hh c hc
    obtain ⟨⟨c1, e1, h1⟩, ⟨d1, f1, k1⟩⟩ := hh c hc
    obtain ⟨⟨c2, e2, h2⟩, -⟩ := hg c1 h1
    obtain ⟨-, ⟨d2, f2, k2⟩⟩ := hg c hc
    obtain ⟨-, ⟨d3, f3, k3⟩⟩ := hh d2 k2
    refine ⟨⟨c2, ?_, h2⟩, ⟨d3, ?_, k3⟩⟩
    · rw [← e2, ← e1]
      group
    · rw [← f3, ← f2]
      group
  one_mem' := fun c hc => ⟨⟨c, by group, hc⟩, ⟨c, by group, hc⟩⟩
  inv_mem' := by
    intro g hg c hc
    obtain ⟨⟨c1, e1, h1⟩, ⟨d1, f1, k1⟩⟩ := hg c hc
    exact ⟨⟨d1, by rw [inv_inv]; exact f1, k1⟩, ⟨c1, by rw [inv_inv]; exact e1, h1⟩⟩

theorem pinnedX_mem_yInvSubgroup {P : ((Fin Tag.E7.rank → ℤ) → K) → Prop}
    {α : Fin Tag.E7.rank → ℤ}
    (h : ∀ (t : K) c, P c → ∃ c', pinnedX .E7 K α t * rootProd .E7 K yPsi c *
      (pinnedX .E7 K α t)⁻¹ = rootProd .E7 K yPsi c' ∧ P c') (t : K) :
    pinnedX .E7 K α t ∈ yInvSubgroup K P := by
  intro c hc
  refine ⟨h t c hc, ?_⟩
  obtain ⟨c', e, hc'⟩ := h (-t) c hc
  refine ⟨c', ?_, hc'⟩
  rw [pinnedX_neg]
  rw [pinnedX_neg, neg_neg] at e
  exact e

theorem rootSpan_le_yInvSubgroup {P : ((Fin Tag.E7.rank → ℤ) → K) → Prop}
    {S : Set (Fin Tag.E7.rank → ℤ)}
    (h : ∀ α ∈ S, ∀ t : K, pinnedX .E7 K α t ∈ yInvSubgroup K P) :
    rootSpan .E7 K S ≤ yInvSubgroup K P :=
  iSup₂_le fun α hα => (Subgroup.closure_le _).2 (by
    rintro _ ⟨t, rfl⟩
    exact h α hα t)

theorem torusGroup_le_yInvSubgroup {P : ((Fin Tag.E7.rank → ℤ) → K) → Prop}
    (h : ∀ g ∈ torusGroup .E7 K, ∀ c, P c → P fun β => torusRootChar g β * c β) :
    torusGroup .E7 K ≤ yInvSubgroup K P := by
  intro g hg c hc
  have hr : ∀ β ∈ yPsi, IsRoot .E7 β := fun _ hβ => isRoot_of_mem_yPsi hβ
  refine ⟨⟨_, E6Pilot.conj_rootProd_of_mem_torusGroup hg hr c, h g hg c hc⟩,
    ⟨_, ?_, h _ (inv_mem hg) c hc⟩⟩
  have := E6Pilot.conj_rootProd_of_mem_torusGroup (inv_mem hg) hr c
  rwa [inv_inv] at this

@[expose] def yInvB (c : (Fin Tag.E7.rank → ℤ) → K) : Prop :=
  (∀ β ∈ yFrame, c β ≠ 0) ∧ ∀ β ∈ yLow, c β = 0

theorem yInvB_yCoeff : yInvB (yCoeff (K := K)) := by
  refine ⟨fun β hβ => ?_, fun β hβ => yCoeff_eq_zero_of_not_mem (yLowHigh_not_mem_yFrame.1 β hβ)⟩
  simp only [yCoeff]
  rw [ite_eq_left hβ]
  exact one_ne_zero

theorem conj_yInvB_of_pos {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α ∧ 0 < height α) (t : K)
    {c : (Fin Tag.E7.rank → ℤ) → K} (hc : yInvB c) : yInvB (conjCoeff α t yPsi c) := by
  have hfeed : ∀ ρ, (ρ ∈ yFrame ∨ ρ ∈ yLow) → ρ ∈ yPsi →
      conjCoeff α t yPsi c ρ = c ρ := fun ρ hρ hρΨ =>
    E6Pilot.conjCoeff_apply_of_forall yPsi_nodup t c hρΨ fun β hβ he =>
      hc.2 β (yLow_closed hρ hβ hα he)
  refine ⟨fun β hβ => ?_, fun β hβ => ?_⟩
  · rw [hfeed β (Or.inl hβ) (mem_yPsi_of_mem_yFrame hβ)]
    exact hc.1 β hβ
  · rw [hfeed β (Or.inr hβ) (mem_yPsi_of_mem_yLow hβ)]
    exact hc.2 β hβ

theorem yLevel_nonneg_of_pos {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α ∧ 0 < height α) :
    0 ≤ yLevel α :=
  (IsRoot.height_pos_iff hα.1).1 hα.2 5

theorem borelGroup_le_yInvSubgroup_yInvB [CharP K 2] :
    borelGroup .E7 K ≤ yInvSubgroup K yInvB := by
  refine sup_le (torusGroup_le_yInvSubgroup fun g hg c hc => ⟨fun β hβ => ?_, fun β hβ => ?_⟩)
    (rootSpan_le_yInvSubgroup fun α hα t => pinnedX_mem_yInvSubgroup (fun t c hc =>
      ⟨_, conj_rootProd_yPsi hα.1 (yLevel_nonneg_of_pos hα) t c, conj_yInvB_of_pos hα t hc⟩) t)
  · exact mul_ne_zero (torusRootChar_ne_zero (torusGroup_le_diagonalGroup hg) β) (hc.1 β hβ)
  · show torusRootChar g β * c β = 0
    rw [hc.2 β hβ, mul_zero]

theorem yPsi_map_comm (w : WeylGroup .E7) :
    RootCommFamily .E7 K (yPsi.map fun β => w • β) := by
  intro β hβ β' hβ' s t
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hβ
  obtain ⟨γ', hγ', rfl⟩ := List.mem_map.1 hβ'
  refine CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (IsRoot.smul (isRoot_of_mem_yPsi hγ) w)
    (IsRoot.smul (isRoot_of_mem_yPsi hγ') w) ?_ ?_ s t
  · rw [← smul_neg]
    exact fun h => ne_neg_of_mem_yPsi hγ hγ' (smul_left_cancel w h)
  · rw [← smul_add, isRoot_smul_iff]
    exact yPsi_add_not_isRoot hγ hγ'

theorem canonicalRep_mul_rootProd_yPsi [CharP K 2] (w : WeylGroup .E7)
    (c : (Fin Tag.E7.rank → ℤ) → K) :
    canonicalRep (coxeterSystem .E7) K w * rootProd .E7 K yPsi c *
        (canonicalRep (coxeterSystem .E7) K w)⁻¹ =
      rootProd .E7 K (yPsi.map fun β => w • β) fun ρ => c (w⁻¹ • ρ) := by
  rw [rootProd, E6Pilot.canonicalRep_mul_list_prod_mul_inv_of_charTwo w
    (fun _ hβ => isRoot_of_mem_yPsi hβ) c, rootProd, List.map_map]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  simp [inv_smul_smul]

theorem smul_yFrame_of_commute_yAS [CharP K 2] {g : ModGL .E7 K} {w : WeylGroup .E7}
    (hw : g ∈ bruhatCell .E7 K w) (hgy : g * yAS K = yAS K * g) :
    w ∈ parabolicWeylGroup .E7 yNodes ∧ ∀ β ∈ yFrame, w • β ∈ yFrame := by
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  set n := canonicalRep (coxeterSystem .E7) K w with hn
  obtain ⟨⟨cu, ecu, hcu⟩, -⟩ := borelGroup_le_yInvSubgroup_yInvB hb' yCoeff yInvB_yCoeff
  obtain ⟨-, ⟨cv, ecv, hcv⟩⟩ := borelGroup_le_yInvSubgroup_yInvB hb yCoeff yInvB_yCoeff
  rw [rootProd_yPsi_yCoeff] at ecu ecv
  have hkey : n * rootProd .E7 K yPsi cu * n⁻¹ = rootProd .E7 K yPsi cv := by
    rw [← ecu, ← ecv]
    have e : b * n * b' * yAS K * (b * n * b')⁻¹ = yAS K := by
      rw [hgy]
      group
    calc n * (b' * yAS K * b'⁻¹) * n⁻¹ = b⁻¹ * (b * n * b' * yAS K * (b * n * b')⁻¹) * b := by
          group
      _ = b⁻¹ * yAS K * b := by rw [e]
  rw [hn, canonicalRep_mul_rootProd_yPsi] at hkey
  refine mem_parabolicWeylGroup_of_smul_yFrame fun β hβ => ?_
  have hβΨ := mem_yPsi_of_mem_yFrame hβ
  have hLnd : (yPsi.map fun β => w • β).Nodup := yPsi_nodup.map (MulAction.injective w)
  have hLr : ∀ ρ ∈ yPsi.map (fun β => w • β), IsRoot .E7 ρ := by
    intro ρ hρ
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hρ
    exact IsRoot.smul (isRoot_of_mem_yPsi hγ) w
  obtain ⟨hmem, heq⟩ := E6Pilot.mem_and_eq_of_rootProd_eq hLnd hLr (yPsi_map_comm w) yPsi_nodup
    (fun _ hρ => pos_of_mem_yPsi hρ) yPsi_comm hkey (List.mem_map_of_mem hβΨ)
    (by rw [inv_smul_smul]; exact hcu.1 β hβ)
  rw [inv_smul_smul] at heq
  have hne : cv (w • β) ≠ 0 := by rw [heq]; exact hcu.1 β hβ
  have hnl : w • β ∉ yLow := fun h => hne (hcv.2 _ h)
  simp only [yPsi, List.mem_append] at hmem
  rcases hmem with (h | h) | h
  · exact Or.inl h
  · exact absurd h hnl
  · exact Or.inr h

theorem mem_parabolicSubgroup_of_commute_yAS [CharP K 2] {g : ModGL .E7 K}
    (hg : g ∈ adjointGroup .E7 K) (hgy : g * yAS K = yAS K * g) :
    g ∈ parabolicSubgroup .E7 K yNodes := by
  obtain ⟨w, hw⟩ := CFSG.SeitzReduction.exists_mem_bruhatCell_of_mem_adjointGroup hg
  have hmem : g ∈ (parabolicSubgroup .E7 K yNodes : Set (ModGL .E7 K)) := by
    rw [(standard_parabolic_cells .E7 K).1 yNodes]
    exact Set.mem_biUnion (smul_yFrame_of_commute_yAS hw hgy).1 hw
  exact hmem

theorem centralizer_e7ASRep_one_le_parabolic [CharP K 2] :
    centralizer ({e7ASRep K 1} : Set (adjointGroup .E7 K)) ≤
      (parabolicSubgroup .E7 K yNodes).subgroupOf (adjointGroup .E7 K) := by
  intro g hg
  rw [mem_centralizer_singleton_iff] at hg
  refine mem_subgroupOf.2 (mem_parabolicSubgroup_of_commute_yAS g.2 ?_)
  have h := congrArg Subtype.val hg
  rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_e7ASRep_one] at h

theorem yLevel_pos_of_mem_parabolicRadicalRoots {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ parabolicRadicalRoots .E7 yNodes) : 1 ≤ yLevel α := by
  obtain ⟨hpos, hnot⟩ := hα
  have hpos' : IsRoot .E7 α ∧ 0 < height α := hpos
  have h0 := yLevel_nonneg_of_pos hpos'
  by_contra hlt
  have h5 : α 5 = 0 := by
    simp only [yLevel] at h0 hlt
    omega
  refine hnot ⟨⟨hpos'.1, fun i hi => ?_⟩, hpos'⟩
  simp only [yNodes, Set.mem_ofPred_eq, not_not] at hi
  rw [hi]
  exact h5

theorem commute_pinnedX_rootProd_yPsi {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α)
    (hα1 : 1 ≤ yLevel α) (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    Commute (pinnedX .E7 K α t) (rootProd .E7 K yPsi c) := by
  refine Commute.list_prod_right _ _ fun x hx => ?_
  obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
  have hβ2 := level_of_mem_yPsi hβ
  refine CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv hα (isRoot_of_mem_yPsi hβ) ?_ ?_
    t (c β)
  · intro h
    have hlev : yLevel α = -yLevel β := by rw [h, yLevel_neg]
    rw [hβ2] at hlev
    omega
  · intro hr
    have hle := yLevel_le_two hr
    rw [yLevel_add, hβ2] at hle
    omega

theorem parabolicRadical_le_centralizer_rootProd_yPsi (c : (Fin Tag.E7.rank → ℤ) → K) :
    parabolicRadical .E7 K yNodes ≤
      centralizer ({rootProd .E7 K yPsi c} : Set (ModGL .E7 K)) :=
  iSup₂_le fun α hα => (Subgroup.closure_le _).2 (by
    rintro _ ⟨t, rfl⟩
    exact mem_centralizer_singleton_iff.2
      (commute_pinnedX_rootProd_yPsi hα.1.1 (yLevel_pos_of_mem_parabolicRadicalRoots hα) t c).eq)

end CFSG.SeitzReduction.E7Pilot
