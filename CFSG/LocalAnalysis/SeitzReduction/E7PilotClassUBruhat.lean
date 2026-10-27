module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassURoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZBasic
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClasses

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff)

local instance e7ClassUBruhatNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def uAS : ModGL .E7 K := rootProd .E7 K uFrame fun _ => 1

@[expose] def uCoeff : (Fin Tag.E7.rank → ℤ) → K := fun β => if β ∈ uFrame then 1 else 0

theorem rootProd_uPsi_uCoeff : rootProd .E7 K uPsi uCoeff = uAS K := by
  rw [show (uCoeff : (Fin Tag.E7.rank → ℤ) → K) =
      fun ρ => if ρ ∈ uFrame then (fun _ => (1 : K)) ρ else 0 from rfl,
    E6Pilot.rootProd_ite_mem, uPsi_filter_uFrame]
  rfl

theorem coe_e7ASRep_three : (e7ASRep K 3 : ModGL .E7 K) = uAS K := rfl

theorem uCoeff_eq_zero_of_not_mem {β : Fin Tag.E7.rank → ℤ} (h : β ∉ uFrame) :
    (uCoeff β : K) = 0 := by
  simp only [uCoeff]
  rw [ite_eq_right h]

theorem uPsi_comm : RootCommFamily .E7 K uPsi := fun _ hβ _ hβ' s t =>
  CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (isRoot_of_mem_uPsi hβ)
    (isRoot_of_mem_uPsi hβ') (ne_neg_of_mem_uPsi hβ hβ') (uPsi_add_not_isRoot hβ hβ') s t

theorem conj_hyp_of_uLevel_nonneg {α : Fin Tag.E7.rank → ℤ} (hα0 : 0 ≤ uLevel α) :
    ∀ β ∈ uPsi, α ≠ -β ∧ (IsRoot .E7 (α + β) → α + β ∈ uPsi) := by
  intro β hβ
  have hβ1 := level_of_mem_uPsi hβ
  refine ⟨fun h => ?_, fun hr => mem_uPsi_of_level hr ?_⟩
  · have : uLevel α = -uLevel β := by rw [h, uLevel_neg]
    omega
  · rw [uLevel_add]
    omega

theorem conj_rootProd_uPsi [CharP K 2] {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α)
    (hα0 : 0 ≤ uLevel α) (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    pinnedX .E7 K α t * rootProd .E7 K uPsi c * (pinnedX .E7 K α t)⁻¹ =
      rootProd .E7 K uPsi (conjCoeff α t uPsi c) :=
  E6Pilot.conj_rootProd (Or.inr (Or.inr (Or.inl rfl))) CharTwo.two_eq_zero uPsi_nodup
    (fun _ hβ => isRoot_of_mem_uPsi hβ) uPsi_comm hα (conj_hyp_of_uLevel_nonneg hα0) t c

variable (K) in
@[expose] noncomputable def uInvSubgroup (P : ((Fin Tag.E7.rank → ℤ) → K) → Prop) :
    Subgroup (ModGL .E7 K) where
  carrier := {g | ∀ c, P c →
    (∃ c', g * rootProd .E7 K uPsi c * g⁻¹ = rootProd .E7 K uPsi c' ∧ P c') ∧
      (∃ c', g⁻¹ * rootProd .E7 K uPsi c * g = rootProd .E7 K uPsi c' ∧ P c')}
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

theorem pinnedX_mem_uInvSubgroup {P : ((Fin Tag.E7.rank → ℤ) → K) → Prop}
    {α : Fin Tag.E7.rank → ℤ}
    (h : ∀ (t : K) c, P c → ∃ c', pinnedX .E7 K α t * rootProd .E7 K uPsi c *
      (pinnedX .E7 K α t)⁻¹ = rootProd .E7 K uPsi c' ∧ P c') (t : K) :
    pinnedX .E7 K α t ∈ uInvSubgroup K P := by
  intro c hc
  refine ⟨h t c hc, ?_⟩
  obtain ⟨c', e, hc'⟩ := h (-t) c hc
  refine ⟨c', ?_, hc'⟩
  rw [pinnedX_neg]
  rw [pinnedX_neg, neg_neg] at e
  exact e

theorem rootSpan_le_uInvSubgroup {P : ((Fin Tag.E7.rank → ℤ) → K) → Prop}
    {S : Set (Fin Tag.E7.rank → ℤ)}
    (h : ∀ α ∈ S, ∀ t : K, pinnedX .E7 K α t ∈ uInvSubgroup K P) :
    rootSpan .E7 K S ≤ uInvSubgroup K P :=
  iSup₂_le fun α hα => (Subgroup.closure_le _).2 (by
    rintro _ ⟨t, rfl⟩
    exact h α hα t)

theorem torusGroup_le_uInvSubgroup {P : ((Fin Tag.E7.rank → ℤ) → K) → Prop}
    (h : ∀ g ∈ torusGroup .E7 K, ∀ c, P c → P fun β => torusRootChar g β * c β) :
    torusGroup .E7 K ≤ uInvSubgroup K P := by
  intro g hg c hc
  have hr : ∀ β ∈ uPsi, IsRoot .E7 β := fun _ hβ => isRoot_of_mem_uPsi hβ
  refine ⟨⟨_, E6Pilot.conj_rootProd_of_mem_torusGroup hg hr c, h g hg c hc⟩,
    ⟨_, ?_, h _ (inv_mem hg) c hc⟩⟩
  have := E6Pilot.conj_rootProd_of_mem_torusGroup (inv_mem hg) hr c
  rwa [inv_inv] at this

@[expose] def uInvB (c : (Fin Tag.E7.rank → ℤ) → K) : Prop :=
  (∀ β ∈ uFrame, c β ≠ 0) ∧ ∀ β ∈ uLow, c β = 0

theorem uInvB_uCoeff : uInvB (uCoeff (K := K)) := by
  refine ⟨fun β hβ => ?_, fun β hβ => uCoeff_eq_zero_of_not_mem (uLowHigh_not_mem_uFrame.1 β hβ)⟩
  simp only [uCoeff]
  rw [ite_eq_left hβ]
  exact one_ne_zero

theorem conj_uInvB_of_pos {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α ∧ 0 < height α) (t : K)
    {c : (Fin Tag.E7.rank → ℤ) → K} (hc : uInvB c) : uInvB (conjCoeff α t uPsi c) := by
  have hfeed : ∀ ρ, (ρ ∈ uFrame ∨ ρ ∈ uLow) → ρ ∈ uPsi →
      conjCoeff α t uPsi c ρ = c ρ := fun ρ hρ hρΨ =>
    E6Pilot.conjCoeff_apply_of_forall uPsi_nodup t c hρΨ fun β hβ he =>
      hc.2 β (uLow_closed hρ hβ hα he)
  refine ⟨fun β hβ => ?_, fun β hβ => ?_⟩
  · rw [hfeed β (Or.inl hβ) (mem_uPsi_of_mem_uFrame hβ)]
    exact hc.1 β hβ
  · rw [hfeed β (Or.inr hβ) (mem_uPsi_of_mem_uLow hβ)]
    exact hc.2 β hβ

theorem uLevel_nonneg_of_pos {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α ∧ 0 < height α) :
    0 ≤ uLevel α :=
  (IsRoot.height_pos_iff hα.1).1 hα.2 6

theorem borelGroup_le_uInvSubgroup_uInvB [CharP K 2] :
    borelGroup .E7 K ≤ uInvSubgroup K uInvB := by
  refine sup_le (torusGroup_le_uInvSubgroup fun g hg c hc => ⟨fun β hβ => ?_, fun β hβ => ?_⟩)
    (rootSpan_le_uInvSubgroup fun α hα t => pinnedX_mem_uInvSubgroup (fun t c hc =>
      ⟨_, conj_rootProd_uPsi hα.1 (uLevel_nonneg_of_pos hα) t c, conj_uInvB_of_pos hα t hc⟩) t)
  · exact mul_ne_zero (torusRootChar_ne_zero (torusGroup_le_diagonalGroup hg) β) (hc.1 β hβ)
  · show torusRootChar g β * c β = 0
    rw [hc.2 β hβ, mul_zero]

theorem uPsi_map_comm (w : WeylGroup .E7) :
    RootCommFamily .E7 K (uPsi.map fun β => w • β) := by
  intro β hβ β' hβ' s t
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hβ
  obtain ⟨γ', hγ', rfl⟩ := List.mem_map.1 hβ'
  refine CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (IsRoot.smul (isRoot_of_mem_uPsi hγ) w)
    (IsRoot.smul (isRoot_of_mem_uPsi hγ') w) ?_ ?_ s t
  · rw [← smul_neg]
    exact fun h => ne_neg_of_mem_uPsi hγ hγ' (smul_left_cancel w h)
  · rw [← smul_add, isRoot_smul_iff]
    exact uPsi_add_not_isRoot hγ hγ'

theorem canonicalRep_mul_rootProd_uPsi [CharP K 2] (w : WeylGroup .E7)
    (c : (Fin Tag.E7.rank → ℤ) → K) :
    canonicalRep (coxeterSystem .E7) K w * rootProd .E7 K uPsi c *
        (canonicalRep (coxeterSystem .E7) K w)⁻¹ =
      rootProd .E7 K (uPsi.map fun β => w • β) fun ρ => c (w⁻¹ • ρ) := by
  rw [rootProd, E6Pilot.canonicalRep_mul_list_prod_mul_inv_of_charTwo w
    (fun _ hβ => isRoot_of_mem_uPsi hβ) c, rootProd, List.map_map]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  simp [inv_smul_smul]

theorem smul_uFrame_of_commute_uAS [CharP K 2] {g : ModGL .E7 K} {w : WeylGroup .E7}
    (hw : g ∈ bruhatCell .E7 K w) (hgu : g * uAS K = uAS K * g) :
    w ∈ parabolicWeylGroup .E7 uNodes ∧ ∀ β ∈ uFrame, w • β ∈ uFrame := by
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  set n := canonicalRep (coxeterSystem .E7) K w with hn
  obtain ⟨⟨cu, ecu, hcu⟩, -⟩ := borelGroup_le_uInvSubgroup_uInvB hb' uCoeff uInvB_uCoeff
  obtain ⟨-, ⟨cv, ecv, hcv⟩⟩ := borelGroup_le_uInvSubgroup_uInvB hb uCoeff uInvB_uCoeff
  rw [rootProd_uPsi_uCoeff] at ecu ecv
  have hkey : n * rootProd .E7 K uPsi cu * n⁻¹ = rootProd .E7 K uPsi cv := by
    rw [← ecu, ← ecv]
    have e : b * n * b' * uAS K * (b * n * b')⁻¹ = uAS K := by
      rw [hgu]
      group
    calc n * (b' * uAS K * b'⁻¹) * n⁻¹ = b⁻¹ * (b * n * b' * uAS K * (b * n * b')⁻¹) * b := by
          group
      _ = b⁻¹ * uAS K * b := by rw [e]
  rw [hn, canonicalRep_mul_rootProd_uPsi] at hkey
  refine mem_parabolicWeylGroup_of_smul_uFrame fun β hβ => ?_
  have hβΨ := mem_uPsi_of_mem_uFrame hβ
  have hLnd : (uPsi.map fun β => w • β).Nodup := uPsi_nodup.map (MulAction.injective w)
  have hLr : ∀ ρ ∈ uPsi.map (fun β => w • β), IsRoot .E7 ρ := by
    intro ρ hρ
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hρ
    exact IsRoot.smul (isRoot_of_mem_uPsi hγ) w
  obtain ⟨hmem, heq⟩ := E6Pilot.mem_and_eq_of_rootProd_eq hLnd hLr (uPsi_map_comm w) uPsi_nodup
    (fun _ hρ => pos_of_mem_uPsi hρ) uPsi_comm hkey (List.mem_map_of_mem hβΨ)
    (by rw [inv_smul_smul]; exact hcu.1 β hβ)
  rw [inv_smul_smul] at heq
  have hne : cv (w • β) ≠ 0 := by rw [heq]; exact hcu.1 β hβ
  have hnl : w • β ∉ uLow := fun h => hne (hcv.2 _ h)
  simp only [uPsi, List.mem_append] at hmem
  rcases hmem with (h | h) | h
  · exact Or.inl h
  · exact absurd h hnl
  · exact Or.inr h

theorem mem_parabolicSubgroup_of_commute_uAS [CharP K 2] {g : ModGL .E7 K}
    (hg : g ∈ adjointGroup .E7 K) (hgu : g * uAS K = uAS K * g) :
    g ∈ parabolicSubgroup .E7 K uNodes := by
  obtain ⟨w, hw⟩ := CFSG.SeitzReduction.exists_mem_bruhatCell_of_mem_adjointGroup hg
  have hmem : g ∈ (parabolicSubgroup .E7 K uNodes : Set (ModGL .E7 K)) := by
    rw [(standard_parabolic_cells .E7 K).1 uNodes]
    exact Set.mem_biUnion (smul_uFrame_of_commute_uAS hw hgu).1 hw
  exact hmem

theorem centralizer_e7ASRep_three_le_parabolic [CharP K 2] :
    centralizer ({e7ASRep K 3} : Set (adjointGroup .E7 K)) ≤
      (parabolicSubgroup .E7 K uNodes).subgroupOf (adjointGroup .E7 K) := by
  intro g hg
  rw [mem_centralizer_singleton_iff] at hg
  refine mem_subgroupOf.2 (mem_parabolicSubgroup_of_commute_uAS g.2 ?_)
  have h := congrArg Subtype.val hg
  rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_e7ASRep_three] at h

variable (K) in
@[expose] noncomputable def parabolicU : Subgroup (adjointGroup .E7 K) :=
  ((parabolicSubgroup .E7 K uNodes).subgroupOf (adjointGroup .E7 K)).map
    (MulAut.conj (e7RepConj K 3)).toMonoidHom

theorem conj_mem_centralizer_e7ASRep_three [CharP K 2] {g : adjointGroup .E7 K}
    (hg : g ∈ centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))) :
    (e7RepConj K 3)⁻¹ * g * e7RepConj K 3 ∈
      centralizer ({e7ASRep K 3} : Set (adjointGroup .E7 K)) := by
  rw [mem_centralizer_singleton_iff] at hg ⊢
  set n := e7RepConj K 3
  rw [← e7RepConj_mul_e7ASRep_mul_inv (K := K) 3] at hg
  calc n⁻¹ * g * n * e7ASRep K 3 = n⁻¹ * (g * (n * e7ASRep K 3 * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * e7ASRep K 3 * n⁻¹) * g) * n := by rw [hg]
    _ = e7ASRep K 3 * (n⁻¹ * g * n) := by group

theorem mem_uPsi_of_mem_parabolicRadicalRoots {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ parabolicRadicalRoots .E7 uNodes) : α ∈ uPsi := by
  obtain ⟨hpos, hnot⟩ := hα
  have hpos' : IsRoot .E7 α ∧ 0 < height α := hpos
  refine mem_uPsi_of_level hpos'.1 ?_
  have h0 := uLevel_nonneg_of_pos hpos'
  by_contra hlt
  have h6 : α 6 = 0 := by simp only [uLevel] at h0 hlt; omega
  refine hnot ⟨⟨hpos'.1, fun i hi => ?_⟩, hpos'⟩
  simp only [uNodes, Set.mem_ofPred_eq, not_not] at hi
  rw [hi]
  exact h6

theorem parabolicRadical_le_centralizer_rootProd (c : (Fin Tag.E7.rank → ℤ) → K) :
    parabolicRadical .E7 K uNodes ≤
      centralizer ({rootProd .E7 K uPsi c} : Set (ModGL .E7 K)) :=
  iSup₂_le fun α hα => (Subgroup.closure_le _).2 (by
    rintro _ ⟨t, rfl⟩
    exact mem_centralizer_singleton_iff.2
      (uPsi_comm.commute_rootProd (mem_uPsi_of_mem_parabolicRadicalRoots hα) t c).eq)

theorem parabolicRadical_le_centralizer_uAS :
    parabolicRadical .E7 K uNodes ≤ centralizer ({uAS K} : Set (ModGL .E7 K)) := by
  rw [← rootProd_uPsi_uCoeff]
  exact parabolicRadical_le_centralizer_rootProd uCoeff

theorem parabolicRadical_comm {a b : ModGL .E7 K} (ha : a ∈ parabolicRadical .E7 K uNodes)
    (hb : b ∈ parabolicRadical .E7 K uNodes) : a * b = b * a := by
  have key : ∀ α ∈ parabolicRadicalRoots .E7 uNodes, ∀ t : K,
      parabolicRadical .E7 K uNodes ≤
        centralizer ({pinnedX .E7 K α t} : Set (ModGL .E7 K)) := fun α hα t =>
    iSup₂_le fun β hβ => (Subgroup.closure_le _).2 (by
      rintro _ ⟨s, rfl⟩
      exact mem_centralizer_singleton_iff.2 (uPsi_comm _ (mem_uPsi_of_mem_parabolicRadicalRoots hβ)
        _ (mem_uPsi_of_mem_parabolicRadicalRoots hα) s t).eq)
  have hle : parabolicRadical .E7 K uNodes ≤
      centralizer (parabolicRadical .E7 K uNodes : Set (ModGL .E7 K)) :=
    iSup₂_le fun α hα => (Subgroup.closure_le _).2 (by
      rintro _ ⟨t, rfl⟩
      exact Subgroup.mem_centralizer_iff.2 fun h hh =>
        mem_centralizer_singleton_iff.1 (key α hα t hh))
  exact Subgroup.mem_centralizer_iff.1 (hle hb) a ha

theorem commute_of_mul_commute_uAS {q m : ModGL .E7 K}
    (hq : q ∈ parabolicRadical .E7 K uNodes) (hgu : q * m * uAS K = uAS K * (q * m)) :
    m * uAS K = uAS K * m := by
  have hqu := mem_centralizer_singleton_iff.1 (parabolicRadical_le_centralizer_uAS hq)
  calc m * uAS K = q⁻¹ * (q * m * uAS K) := by group
    _ = q⁻¹ * (uAS K * q * m) := by rw [hgu, mul_assoc]
    _ = q⁻¹ * (q * uAS K) * m := by rw [hqu]; group
    _ = uAS K * m := by group

variable (K) in
@[expose] noncomputable def radicalU : Subgroup (adjointGroup .E7 K) :=
  ((parabolicRadical .E7 K uNodes).subgroupOf (adjointGroup .E7 K)).map
    (MulAut.conj (e7RepConj K 3)).toMonoidHom

variable (K) in
@[expose] noncomputable def leviU : Subgroup (adjointGroup .E7 K) :=
  ((parabolicLevi .E7 K uNodes).subgroupOf (adjointGroup .E7 K)).map
    (MulAut.conj (e7RepConj K 3)).toMonoidHom

theorem conj_mem_centralizer_e7Rep_three [CharP K 2] {x : adjointGroup .E7 K}
    (hx : (x : ModGL .E7 K) * uAS K = uAS K * x) :
    e7RepConj K 3 * x * (e7RepConj K 3)⁻¹ ∈
      centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K)) := by
  set n := e7RepConj K 3
  have hX : x * e7ASRep K 3 = e7ASRep K 3 * x :=
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_e7ASRep_three]; exact hx)
  rw [mem_centralizer_singleton_iff, ← e7RepConj_mul_e7ASRep_mul_inv (K := K) 3]
  calc n * x * n⁻¹ * (n * e7ASRep K 3 * n⁻¹) = n * (x * e7ASRep K 3) * n⁻¹ := by group
    _ = n * (e7ASRep K 3 * x) * n⁻¹ := by rw [hX]
    _ = n * e7ASRep K 3 * n⁻¹ * (n * x * n⁻¹) := by group

theorem radicalU_le_centralizer [CharP K 2] :
    radicalU K ≤ centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K)) := by
  rintro _ ⟨x, hx, rfl⟩
  exact conj_mem_centralizer_e7Rep_three
    (mem_centralizer_singleton_iff.1 (parabolicRadical_le_centralizer_uAS (mem_subgroupOf.1 hx)))

theorem radicalU_comm {a b : adjointGroup .E7 K} (ha : a ∈ radicalU K) (hb : b ∈ radicalU K) :
    a * b = b * a := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have e : x * y = y * x :=
    Subtype.ext (parabolicRadical_comm (mem_subgroupOf.1 hx) (mem_subgroupOf.1 hy))
  calc e7RepConj K 3 * x * (e7RepConj K 3)⁻¹ * (e7RepConj K 3 * y * (e7RepConj K 3)⁻¹) =
        e7RepConj K 3 * (x * y) * (e7RepConj K 3)⁻¹ := by group
    _ = e7RepConj K 3 * (y * x) * (e7RepConj K 3)⁻¹ := by rw [e]
    _ = _ := by group

theorem exists_mul_eq_of_mem_centralizer_e7Rep_three [CharP K 2] {g : adjointGroup .E7 K}
    (hg : g ∈ centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))) :
    ∃ q ∈ radicalU K, ∃ m ∈ leviU K,
      m ∈ centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K)) ∧ g = q * m := by
  set n := e7RepConj K 3
  have hc := conj_mem_centralizer_e7ASRep_three hg
  rw [mem_centralizer_singleton_iff] at hc
  have hc' : ((n⁻¹ * g * n : adjointGroup .E7 K) : ModGL .E7 K) * uAS K =
      uAS K * ((n⁻¹ * g * n : adjointGroup .E7 K) : ModGL .E7 K) := by
    have h := congrArg Subtype.val hc
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_e7ASRep_three] at h
  have hP := mem_parabolicSubgroup_of_commute_uAS (n⁻¹ * g * n).2 hc'
  obtain ⟨-, -, -, -, -, -, huniq, -⟩ := parabolic_root_radical_Levi_factors .E7 K uNodes
  obtain ⟨⟨q', m'⟩, ⟨hq', hm', he⟩, -⟩ := huniq _ hP
  simp only at hq' hm' he
  rw [he] at hc'
  have hmu := commute_of_mul_commute_uAS hq' hc'
  have hqC : q' ∈ adjointGroup .E7 K :=
    posUnipotent_le_adjointGroup (parabolicRadical_le_posUnipotent _ hq')
  have hmC : m' ∈ adjointGroup .E7 K := parabolicLevi_le_adjointGroup .E7 K uNodes hm'
  set Q : adjointGroup .E7 K := ⟨q', hqC⟩
  set M : adjointGroup .E7 K := ⟨m', hmC⟩
  have hgQM : n⁻¹ * g * n = Q * M := Subtype.ext he
  refine ⟨n * Q * n⁻¹, ⟨Q, mem_subgroupOf.2 hq', rfl⟩, n * M * n⁻¹, ⟨M, mem_subgroupOf.2 hm', rfl⟩,
    conj_mem_centralizer_e7Rep_three hmu, ?_⟩
  calc g = n * (n⁻¹ * g * n) * n⁻¹ := by group
    _ = n * (Q * M) * n⁻¹ := by rw [hgQM]
    _ = n * Q * n⁻¹ * (n * M * n⁻¹) := by group

theorem centralizer_e7Rep_three_eq [CharP K 2] :
    centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K)) =
      radicalU K ⊔ (leviU K ⊓ centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K))) := by
  refine le_antisymm (fun g hg => ?_) (sup_le radicalU_le_centralizer inf_le_right)
  obtain ⟨q, hq, m, hm, hmC, rfl⟩ := exists_mul_eq_of_mem_centralizer_e7Rep_three hg
  exact mul_mem (mem_sup_left hq) (mem_sup_right (mem_inf.2 ⟨hm, hmC⟩))

end CFSG.SeitzReduction.E7Pilot
