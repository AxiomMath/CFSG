module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZBasic
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClasses

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff)

local instance e7ClassVBruhatNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def vAS : ModGL .E7 K := rootProd .E7 K vFrame fun _ => 1

@[expose] def vCoeff : (Fin Tag.E7.rank → ℤ) → K := fun β => if β ∈ vFrame then 1 else 0

theorem rootProd_vPsi_vCoeff : rootProd .E7 K vPsi vCoeff = vAS K := by
  rw [show (vCoeff : (Fin Tag.E7.rank → ℤ) → K) =
      fun ρ => if ρ ∈ vFrame then (fun _ => (1 : K)) ρ else 0 from rfl,
    E6Pilot.rootProd_ite_mem, vPsi_filter_vFrame]
  rfl

theorem coe_e7ASRep_four : (e7ASRep K 4 : ModGL .E7 K) = vAS K := rfl

theorem vCoeff_eq_zero_of_not_mem {β : Fin Tag.E7.rank → ℤ} (h : β ∉ vFrame) :
    (vCoeff β : K) = 0 := by
  simp only [vCoeff]
  rw [ite_eq_right h]

theorem vPsi_comm : RootCommFamily .E7 K vPsi := fun _ hβ _ hβ' s t =>
  CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (isRoot_of_mem_vPsi hβ)
    (isRoot_of_mem_vPsi hβ') (ne_neg_of_mem_vPsi hβ hβ') (vPsi_add_not_isRoot hβ hβ') s t

theorem conj_hyp_of_vLevel_nonneg {α : Fin Tag.E7.rank → ℤ} (hα0 : 0 ≤ vLevel α) :
    ∀ β ∈ vPsi, α ≠ -β ∧ (IsRoot .E7 (α + β) → α + β ∈ vPsi) := by
  intro β hβ
  have hβ2 := level_of_mem_vPsi hβ
  refine ⟨fun h => ?_, fun hr => mem_vPsi_of_level hr ?_⟩
  · have : vLevel α = -vLevel β := by rw [h, vLevel_neg]
    omega
  · rw [vLevel_add]
    omega

theorem conj_rootProd_vPsi [CharP K 2] {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α)
    (hα0 : 0 ≤ vLevel α) (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    pinnedX .E7 K α t * rootProd .E7 K vPsi c * (pinnedX .E7 K α t)⁻¹ =
      rootProd .E7 K vPsi (conjCoeff α t vPsi c) :=
  E6Pilot.conj_rootProd (Or.inr (Or.inr (Or.inl rfl))) CharTwo.two_eq_zero vPsi_nodup
    (fun _ hβ => isRoot_of_mem_vPsi hβ) vPsi_comm hα (conj_hyp_of_vLevel_nonneg hα0) t c

variable (K) in
@[expose] noncomputable def vInvSubgroup (P : ((Fin Tag.E7.rank → ℤ) → K) → Prop) :
    Subgroup (ModGL .E7 K) where
  carrier := {g | ∀ c, P c →
    (∃ c', g * rootProd .E7 K vPsi c * g⁻¹ = rootProd .E7 K vPsi c' ∧ P c') ∧
      (∃ c', g⁻¹ * rootProd .E7 K vPsi c * g = rootProd .E7 K vPsi c' ∧ P c')}
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

theorem pinnedX_mem_vInvSubgroup {P : ((Fin Tag.E7.rank → ℤ) → K) → Prop}
    {α : Fin Tag.E7.rank → ℤ}
    (h : ∀ (t : K) c, P c → ∃ c', pinnedX .E7 K α t * rootProd .E7 K vPsi c *
      (pinnedX .E7 K α t)⁻¹ = rootProd .E7 K vPsi c' ∧ P c') (t : K) :
    pinnedX .E7 K α t ∈ vInvSubgroup K P := by
  intro c hc
  refine ⟨h t c hc, ?_⟩
  obtain ⟨c', e, hc'⟩ := h (-t) c hc
  refine ⟨c', ?_, hc'⟩
  rw [pinnedX_neg]
  rw [pinnedX_neg, neg_neg] at e
  exact e

theorem rootSpan_le_vInvSubgroup {P : ((Fin Tag.E7.rank → ℤ) → K) → Prop}
    {S : Set (Fin Tag.E7.rank → ℤ)}
    (h : ∀ α ∈ S, ∀ t : K, pinnedX .E7 K α t ∈ vInvSubgroup K P) :
    rootSpan .E7 K S ≤ vInvSubgroup K P :=
  iSup₂_le fun α hα => (Subgroup.closure_le _).2 (by
    rintro _ ⟨t, rfl⟩
    exact h α hα t)

theorem torusGroup_le_vInvSubgroup {P : ((Fin Tag.E7.rank → ℤ) → K) → Prop}
    (h : ∀ g ∈ torusGroup .E7 K, ∀ c, P c → P fun β => torusRootChar g β * c β) :
    torusGroup .E7 K ≤ vInvSubgroup K P := by
  intro g hg c hc
  have hr : ∀ β ∈ vPsi, IsRoot .E7 β := fun _ hβ => isRoot_of_mem_vPsi hβ
  refine ⟨⟨_, E6Pilot.conj_rootProd_of_mem_torusGroup hg hr c, h g hg c hc⟩,
    ⟨_, ?_, h _ (inv_mem hg) c hc⟩⟩
  have := E6Pilot.conj_rootProd_of_mem_torusGroup (inv_mem hg) hr c
  rwa [inv_inv] at this

@[expose] def vInvB (c : (Fin Tag.E7.rank → ℤ) → K) : Prop :=
  (∀ β ∈ vFrame, c β ≠ 0) ∧ ∀ β ∈ vLow, c β = 0

theorem vInvB_vCoeff : vInvB (vCoeff (K := K)) := by
  refine ⟨fun β hβ => ?_, fun β hβ => vCoeff_eq_zero_of_not_mem (vLowHigh_not_mem_vFrame.1 β hβ)⟩
  simp only [vCoeff]
  rw [ite_eq_left hβ]
  exact one_ne_zero

theorem conj_vInvB_of_pos {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α ∧ 0 < height α) (t : K)
    {c : (Fin Tag.E7.rank → ℤ) → K} (hc : vInvB c) : vInvB (conjCoeff α t vPsi c) := by
  have hfeed : ∀ ρ, (ρ ∈ vFrame ∨ ρ ∈ vLow) → ρ ∈ vPsi →
      conjCoeff α t vPsi c ρ = c ρ := fun ρ hρ hρΨ =>
    E6Pilot.conjCoeff_apply_of_forall vPsi_nodup t c hρΨ fun β hβ he =>
      hc.2 β (vLow_closed hρ hβ hα he)
  refine ⟨fun β hβ => ?_, fun β hβ => ?_⟩
  · rw [hfeed β (Or.inl hβ) (mem_vPsi_of_mem_vFrame hβ)]
    exact hc.1 β hβ
  · rw [hfeed β (Or.inr hβ) (mem_vPsi_of_mem_vLow hβ)]
    exact hc.2 β hβ

theorem vLevel_nonneg_of_pos {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α ∧ 0 < height α) :
    0 ≤ vLevel α := by
  have h := (IsRoot.height_pos_iff hα.1).1 hα.2
  have h1 := h 1
  have h6 := h 6
  simp only [vLevel]
  omega

theorem borelGroup_le_vInvSubgroup_vInvB [CharP K 2] :
    borelGroup .E7 K ≤ vInvSubgroup K vInvB := by
  refine sup_le (torusGroup_le_vInvSubgroup fun g hg c hc => ⟨fun β hβ => ?_, fun β hβ => ?_⟩)
    (rootSpan_le_vInvSubgroup fun α hα t => pinnedX_mem_vInvSubgroup (fun t c hc =>
      ⟨_, conj_rootProd_vPsi hα.1 (vLevel_nonneg_of_pos hα) t c, conj_vInvB_of_pos hα t hc⟩) t)
  · exact mul_ne_zero (torusRootChar_ne_zero (torusGroup_le_diagonalGroup hg) β) (hc.1 β hβ)
  · show torusRootChar g β * c β = 0
    rw [hc.2 β hβ, mul_zero]

theorem vPsi_map_comm (w : WeylGroup .E7) :
    RootCommFamily .E7 K (vPsi.map fun β => w • β) := by
  intro β hβ β' hβ' s t
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hβ
  obtain ⟨γ', hγ', rfl⟩ := List.mem_map.1 hβ'
  refine CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (IsRoot.smul (isRoot_of_mem_vPsi hγ) w)
    (IsRoot.smul (isRoot_of_mem_vPsi hγ') w) ?_ ?_ s t
  · rw [← smul_neg]
    exact fun h => ne_neg_of_mem_vPsi hγ hγ' (smul_left_cancel w h)
  · rw [← smul_add, isRoot_smul_iff]
    exact vPsi_add_not_isRoot hγ hγ'

theorem canonicalRep_mul_rootProd_vPsi [CharP K 2] (w : WeylGroup .E7)
    (c : (Fin Tag.E7.rank → ℤ) → K) :
    canonicalRep (coxeterSystem .E7) K w * rootProd .E7 K vPsi c *
        (canonicalRep (coxeterSystem .E7) K w)⁻¹ =
      rootProd .E7 K (vPsi.map fun β => w • β) fun ρ => c (w⁻¹ • ρ) := by
  rw [rootProd, E6Pilot.canonicalRep_mul_list_prod_mul_inv_of_charTwo w
    (fun _ hβ => isRoot_of_mem_vPsi hβ) c, rootProd, List.map_map]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  simp [inv_smul_smul]

theorem smul_vFrame_of_commute_vAS [CharP K 2] {g : ModGL .E7 K} {w : WeylGroup .E7}
    (hw : g ∈ bruhatCell .E7 K w) (hgv : g * vAS K = vAS K * g) :
    w ∈ parabolicWeylGroup .E7 vNodes ∧ ∀ β ∈ vFrame, w • β ∈ vFrame := by
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  set n := canonicalRep (coxeterSystem .E7) K w with hn
  obtain ⟨⟨cu, ecu, hcu⟩, -⟩ := borelGroup_le_vInvSubgroup_vInvB hb' vCoeff vInvB_vCoeff
  obtain ⟨-, ⟨cv, ecv, hcv⟩⟩ := borelGroup_le_vInvSubgroup_vInvB hb vCoeff vInvB_vCoeff
  rw [rootProd_vPsi_vCoeff] at ecu ecv
  have hkey : n * rootProd .E7 K vPsi cu * n⁻¹ = rootProd .E7 K vPsi cv := by
    rw [← ecu, ← ecv]
    have e : b * n * b' * vAS K * (b * n * b')⁻¹ = vAS K := by
      rw [hgv]
      group
    calc n * (b' * vAS K * b'⁻¹) * n⁻¹ = b⁻¹ * (b * n * b' * vAS K * (b * n * b')⁻¹) * b := by
          group
      _ = b⁻¹ * vAS K * b := by rw [e]
  rw [hn, canonicalRep_mul_rootProd_vPsi] at hkey
  refine mem_parabolicWeylGroup_of_smul_vFrame fun β hβ => ?_
  have hβΨ := mem_vPsi_of_mem_vFrame hβ
  have hLnd : (vPsi.map fun β => w • β).Nodup := vPsi_nodup.map (MulAction.injective w)
  have hLr : ∀ ρ ∈ vPsi.map (fun β => w • β), IsRoot .E7 ρ := by
    intro ρ hρ
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hρ
    exact IsRoot.smul (isRoot_of_mem_vPsi hγ) w
  obtain ⟨hmem, heq⟩ := E6Pilot.mem_and_eq_of_rootProd_eq hLnd hLr (vPsi_map_comm w) vPsi_nodup
    (fun _ hρ => pos_of_mem_vPsi hρ) vPsi_comm hkey (List.mem_map_of_mem hβΨ)
    (by rw [inv_smul_smul]; exact hcu.1 β hβ)
  rw [inv_smul_smul] at heq
  have hne : cv (w • β) ≠ 0 := by rw [heq]; exact hcu.1 β hβ
  have hnl : w • β ∉ vLow := fun h => hne (hcv.2 _ h)
  simp only [vPsi, List.mem_append] at hmem
  rcases hmem with (h | h) | h
  · exact Or.inl h
  · exact absurd h hnl
  · exact Or.inr h

theorem mem_parabolicSubgroup_of_commute_vAS [CharP K 2] {g : ModGL .E7 K}
    (hg : g ∈ adjointGroup .E7 K) (hgv : g * vAS K = vAS K * g) :
    g ∈ parabolicSubgroup .E7 K vNodes := by
  obtain ⟨w, hw⟩ := CFSG.SeitzReduction.exists_mem_bruhatCell_of_mem_adjointGroup hg
  have hmem : g ∈ (parabolicSubgroup .E7 K vNodes : Set (ModGL .E7 K)) := by
    rw [(standard_parabolic_cells .E7 K).1 vNodes]
    exact Set.mem_biUnion (smul_vFrame_of_commute_vAS hw hgv).1 hw
  exact hmem

theorem centralizer_e7ASRep_four_le_parabolic [CharP K 2] :
    centralizer ({e7ASRep K 4} : Set (adjointGroup .E7 K)) ≤
      (parabolicSubgroup .E7 K vNodes).subgroupOf (adjointGroup .E7 K) := by
  intro g hg
  rw [mem_centralizer_singleton_iff] at hg
  refine mem_subgroupOf.2 (mem_parabolicSubgroup_of_commute_vAS g.2 ?_)
  have h := congrArg Subtype.val hg
  rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_e7ASRep_four] at h

variable (K) in
@[expose] noncomputable def parabolicV : Subgroup (adjointGroup .E7 K) :=
  ((parabolicSubgroup .E7 K vNodes).subgroupOf (adjointGroup .E7 K)).map
    (MulAut.conj (e7RepConj K 4)).toMonoidHom

@[expose] def vInvTop (c : (Fin Tag.E7.rank → ℤ) → K) : Prop :=
  ∀ β ∈ vPsi, vLevel β = 3 → c β = 0

@[expose] def vInvLevel2 (c₀ c : (Fin Tag.E7.rank → ℤ) → K) : Prop :=
  ∀ β ∈ vPsi, vLevel β = 2 → c β = c₀ β

theorem vInvTop_vCoeff : vInvTop (vCoeff (K := K)) := fun β _ hβ3 =>
  vCoeff_eq_zero_of_not_mem fun h => by
    have := vPsi_check.2.2 β (List.mem_append_left _ h)
    omega

theorem parabolicLevi_le_vInvSubgroup_vInvTop [CharP K 2] :
    parabolicLevi .E7 K vNodes ≤ vInvSubgroup K vInvTop := by
  have hgen : ∀ {α : Fin Tag.E7.rank → ℤ}, IsRoot .E7 α → vLevel α = 0 → ∀ t : K,
      pinnedX .E7 K α t ∈ vInvSubgroup K vInvTop := by
    intro α hα hα0 t
    refine pinnedX_mem_vInvSubgroup (fun t c hc => ⟨_, conj_rootProd_vPsi hα hα0.ge t c, ?_⟩) t
    intro ρ hρ hρ3
    rw [E6Pilot.conjCoeff_apply_of_forall vPsi_nodup t c hρ fun β hβ he => ?_]
    · exact hc ρ hρ hρ3
    · refine hc β hβ ?_
      have : vLevel (α + β) = vLevel α + vLevel β := vLevel_add α β
      rw [he, hα0, zero_add, hρ3] at this
      exact this.symm
  have hlev : ∀ j ∈ vNodes, vLevel (Pi.single j 1 : Fin Tag.E7.rank → ℤ) = 0 := by
    intro j hj
    simp only [vNodes, Set.mem_ofPred_eq] at hj
    simp only [vLevel]
    rw [Pi.single_eq_of_ne (Ne.symm hj.1), Pi.single_eq_of_ne (Ne.symm hj.2), add_zero]
  refine sup_le (torusGroup_le_vInvSubgroup fun g _ c hc β hβ hβ3 => by
      show torusRootChar g β * c β = 0
      rw [hc β hβ hβ3, mul_zero])
    ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, hj, t, rfl | rfl⟩
  · rw [← pinnedX_single]
    exact hgen (isRoot_single .E7 j) (hlev j hj) t
  · rw [← pinnedX_neg_single]
    exact hgen (isRoot_neg_single .E7 j) (by rw [vLevel_neg, hlev j hj, neg_zero]) t

theorem parabolicRadical_le_vInvSubgroup_vInvLevel2 [CharP K 2]
    (c₀ : (Fin Tag.E7.rank → ℤ) → K) :
    parabolicRadical .E7 K vNodes ≤ vInvSubgroup K (vInvLevel2 c₀) := by
  refine rootSpan_le_vInvSubgroup fun α hα t => ?_
  have hαpos : IsRoot .E7 α ∧ 0 < height α := hα.1
  have hnn := (IsRoot.height_pos_iff hαpos.1).1 hαpos.2
  have hα1 : 1 ≤ vLevel α := by
    have h0 := vLevel_nonneg_of_pos hαpos
    by_contra hlt
    have h1 : α 1 = 0 := by have := hnn 1; have := hnn 6; simp only [vLevel] at h0 hlt; omega
    have h6 : α 6 = 0 := by have := hnn 1; have := hnn 6; simp only [vLevel] at h0 hlt; omega
    refine hα.2 ⟨⟨hαpos.1, fun i hi => ?_⟩, hαpos⟩
    simp only [vNodes, Set.mem_ofPred_eq, not_and_or, not_not] at hi
    rcases hi with rfl | rfl
    · exact h1
    · exact h6
  refine pinnedX_mem_vInvSubgroup (fun t c hc =>
    ⟨_, conj_rootProd_vPsi hαpos.1 (vLevel_nonneg_of_pos hαpos) t c, ?_⟩) t
  intro ρ hρ hρ2
  rw [E6Pilot.conjCoeff_apply_of_forall vPsi_nodup t c hρ fun β hβ he => ?_]
  · exact hc ρ hρ hρ2
  · exfalso
    have hβ2 := level_of_mem_vPsi hβ
    have : vLevel (α + β) = vLevel α + vLevel β := vLevel_add α β
    rw [he, hρ2] at this
    omega

theorem commute_of_mul_commute_vAS [CharP K 2] {q m : ModGL .E7 K}
    (hq : q ∈ parabolicRadical .E7 K vNodes) (hm : m ∈ parabolicLevi .E7 K vNodes)
    (hgv : q * m * vAS K = vAS K * (q * m)) :
    m * vAS K = vAS K * m ∧ q * vAS K = vAS K * q := by
  obtain ⟨⟨c₁, e₁, h₁⟩, -⟩ := parabolicLevi_le_vInvSubgroup_vInvTop hm vCoeff vInvTop_vCoeff
  rw [rootProd_vPsi_vCoeff] at e₁
  obtain ⟨⟨c₂, e₂, h₂⟩, -⟩ := parabolicRadical_le_vInvSubgroup_vInvLevel2 c₁ hq c₁
    (fun _ _ _ => rfl)
  have hv : q * (m * vAS K * m⁻¹) * q⁻¹ = vAS K := by
    calc q * (m * vAS K * m⁻¹) * q⁻¹ = (q * m) * vAS K * (q * m)⁻¹ := by group
      _ = vAS K := by rw [hgv]; group
  rw [e₁, e₂, ← rootProd_vPsi_vCoeff] at hv
  have hc₂ := E6Pilot.rootProd_injective vPsi_nodup (fun _ hρ => pos_of_mem_vPsi hρ) hv
  have hc₁ : ∀ β ∈ vPsi, c₁ β = vCoeff β := by
    intro β hβ
    rcases vPsi_level_check β hβ with h2 | h3
    · rw [← h₂ β hβ h2, hc₂ β hβ]
    · rw [h₁ β hβ h3, vInvTop_vCoeff β hβ h3]
  have hmv : m * vAS K * m⁻¹ = vAS K := by
    rw [e₁, E6Pilot.rootProd_congr hc₁, rootProd_vPsi_vCoeff]
  have hm' : m * vAS K = vAS K * m := by
    calc m * vAS K = m * vAS K * m⁻¹ * m := by group
      _ = vAS K * m := by rw [hmv]
  refine ⟨hm', ?_⟩
  calc q * vAS K = q * m * vAS K * m⁻¹ := by
        rw [mul_assoc q m, hm', ← mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
    _ = vAS K * (q * m) * m⁻¹ := by rw [hgv]
    _ = vAS K * q := by group

variable (K) in
@[expose] noncomputable def radicalV : Subgroup (adjointGroup .E7 K) :=
  ((parabolicRadical .E7 K vNodes).subgroupOf (adjointGroup .E7 K)).map
    (MulAut.conj (e7RepConj K 4)).toMonoidHom

variable (K) in
@[expose] noncomputable def leviV : Subgroup (adjointGroup .E7 K) :=
  ((parabolicLevi .E7 K vNodes).subgroupOf (adjointGroup .E7 K)).map
    (MulAut.conj (e7RepConj K 4)).toMonoidHom

theorem exists_mul_eq_of_mem_centralizer_e7Rep_four [CharP K 2] {g : adjointGroup .E7 K}
    (hg : g ∈ centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K))) :
    ∃ q ∈ radicalV K, ∃ m ∈ leviV K,
      q ∈ centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K)) ∧
        m ∈ centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K)) ∧ g = q * m := by
  set n := e7RepConj K 4
  have hv : n * e7ASRep K 4 * n⁻¹ = e7Rep K 4 := e7RepConj_mul_e7ASRep_mul_inv (K := K) 4
  rw [mem_centralizer_singleton_iff] at hg
  have hc : (n⁻¹ * g * n) * e7ASRep K 4 = e7ASRep K 4 * (n⁻¹ * g * n) := by
    rw [← hv] at hg
    calc n⁻¹ * g * n * e7ASRep K 4 = n⁻¹ * (g * (n * e7ASRep K 4 * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * e7ASRep K 4 * n⁻¹) * g) * n := by rw [hg]
      _ = e7ASRep K 4 * (n⁻¹ * g * n) := by group
  have hc' : ((n⁻¹ * g * n : adjointGroup .E7 K) : ModGL .E7 K) * vAS K =
      vAS K * ((n⁻¹ * g * n : adjointGroup .E7 K) : ModGL .E7 K) := by
    have h := congrArg Subtype.val hc
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_e7ASRep_four] at h
  have hP := mem_parabolicSubgroup_of_commute_vAS (n⁻¹ * g * n).2 hc'
  obtain ⟨-, -, -, -, -, -, huniq, -⟩ := parabolic_root_radical_Levi_factors .E7 K vNodes
  obtain ⟨⟨q', m'⟩, ⟨hq', hm', he⟩, -⟩ := huniq _ hP
  simp only at hq' hm' he
  rw [he] at hc'
  obtain ⟨hmv, hqv⟩ := commute_of_mul_commute_vAS hq' hm' hc'
  have hqC : q' ∈ adjointGroup .E7 K :=
    posUnipotent_le_adjointGroup (parabolicRadical_le_posUnipotent _ hq')
  have hmC : m' ∈ adjointGroup .E7 K := parabolicLevi_le_adjointGroup .E7 K vNodes hm'
  set Q : adjointGroup .E7 K := ⟨q', hqC⟩
  set M : adjointGroup .E7 K := ⟨m', hmC⟩
  have hQv : Q * e7ASRep K 4 = e7ASRep K 4 * Q :=
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_e7ASRep_four]; exact hqv)
  have hMv : M * e7ASRep K 4 = e7ASRep K 4 * M :=
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_e7ASRep_four]; exact hmv)
  have hgQM : n⁻¹ * g * n = Q * M := Subtype.ext he
  refine ⟨n * Q * n⁻¹, ⟨Q, mem_subgroupOf.2 hq', rfl⟩, n * M * n⁻¹, ⟨M, mem_subgroupOf.2 hm', rfl⟩,
    ?_, ?_, ?_⟩
  · rw [mem_centralizer_singleton_iff, ← hv]
    calc n * Q * n⁻¹ * (n * e7ASRep K 4 * n⁻¹) = n * (Q * e7ASRep K 4) * n⁻¹ := by group
      _ = n * (e7ASRep K 4 * Q) * n⁻¹ := by rw [hQv]
      _ = n * e7ASRep K 4 * n⁻¹ * (n * Q * n⁻¹) := by group
  · rw [mem_centralizer_singleton_iff, ← hv]
    calc n * M * n⁻¹ * (n * e7ASRep K 4 * n⁻¹) = n * (M * e7ASRep K 4) * n⁻¹ := by group
      _ = n * (e7ASRep K 4 * M) * n⁻¹ := by rw [hMv]
      _ = n * e7ASRep K 4 * n⁻¹ * (n * M * n⁻¹) := by group
  · calc g = n * (n⁻¹ * g * n) * n⁻¹ := by group
      _ = n * (Q * M) * n⁻¹ := by rw [hgQM]
      _ = n * Q * n⁻¹ * (n * M * n⁻¹) := by group

end CFSG.SeitzReduction.E7Pilot
