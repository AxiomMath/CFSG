module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZBasic
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

local instance e6CentralizerZBruhatNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def zAS : ModGL .E6 K := rootProd .E6 K zFrame fun _ => 1

@[expose] def zCoeff : (Fin Tag.E6.rank → ℤ) → K := fun β => if β ∈ zFrame then 1 else 0

theorem zPsi_filter_zFrame : zPsi.filter (· ∈ zFrame) = zFrame := by
  decide +kernel

theorem rootProd_zPsi_zCoeff : rootProd .E6 K zPsi zCoeff = zAS K := by
  rw [show (zCoeff : (Fin Tag.E6.rank → ℤ) → K) =
      fun ρ => if ρ ∈ zFrame then (fun _ => (1 : K)) ρ else 0 from rfl,
    rootProd_ite_mem, zPsi_filter_zFrame]
  rfl

theorem coe_e6ASRep_two : (e6ASRep K 2 : ModGL .E6 K) = zAS K := rfl

theorem zPsi_comm : RootCommFamily .E6 K zPsi := fun _ hβ _ hβ' s t =>
  CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (isRoot_of_mem_zPsi hβ)
    (isRoot_of_mem_zPsi hβ') (ne_neg_of_mem_zPsi hβ hβ') (zPsi_add_not_isRoot hβ hβ') s t

theorem zPsi_level_check : ∀ β ∈ zPsi, β 3 = 2 ∨ β ∈ zTop := by
  decide +kernel

theorem zFrame_level {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ zFrame) : β 3 = 2 := by
  have h := zPsi_check.2.2.1 β
  simp only [List.mem_append] at h
  exact h (Or.inl (Or.inl hβ))

theorem not_mem_zFrame_of_mem_zTop {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ zTop) : β ∉ zFrame :=
  fun h => by
    have h1 := zFrame_level h
    have h2 := zPsi_check.2.2.2 β hβ
    omega

theorem conj_hyp_of_level_nonneg {α : Fin Tag.E6.rank → ℤ} (hα3 : 0 ≤ α 3) :
    ∀ β ∈ zPsi, α ≠ -β ∧ (IsRoot .E6 (α + β) → α + β ∈ zPsi) := by
  intro β hβ
  have hβ3 := level_of_mem_zPsi hβ
  refine ⟨fun h => ?_, fun hr => mem_zPsi_of_level hr ?_⟩
  · have : α 3 = -β 3 := by rw [h]; rfl
    omega
  · show 2 ≤ α 3 + β 3
    omega

theorem conj_rootProd_zPsi [CharP K 2] {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α)
    (hα3 : 0 ≤ α 3) (t : K) (c : (Fin Tag.E6.rank → ℤ) → K) :
    pinnedX .E6 K α t * rootProd .E6 K zPsi c * (pinnedX .E6 K α t)⁻¹ =
      rootProd .E6 K zPsi (conjCoeff α t zPsi c) :=
  conj_rootProd (Or.inr (Or.inl rfl)) CharTwo.two_eq_zero zPsi_nodup
    (fun _ hβ => isRoot_of_mem_zPsi hβ) zPsi_comm hα (conj_hyp_of_level_nonneg hα3) t c

variable (K) in
@[expose] noncomputable def zInvSubgroup (P : ((Fin Tag.E6.rank → ℤ) → K) → Prop) :
    Subgroup (ModGL .E6 K) where
  carrier := {g | ∀ c, P c →
    (∃ c', g * rootProd .E6 K zPsi c * g⁻¹ = rootProd .E6 K zPsi c' ∧ P c') ∧
      (∃ c', g⁻¹ * rootProd .E6 K zPsi c * g = rootProd .E6 K zPsi c' ∧ P c')}
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

theorem pinnedX_mem_zInvSubgroup {P : ((Fin Tag.E6.rank → ℤ) → K) → Prop}
    {α : Fin Tag.E6.rank → ℤ}
    (h : ∀ (t : K) c, P c → ∃ c', pinnedX .E6 K α t * rootProd .E6 K zPsi c *
      (pinnedX .E6 K α t)⁻¹ = rootProd .E6 K zPsi c' ∧ P c') (t : K) :
    pinnedX .E6 K α t ∈ zInvSubgroup K P := by
  intro c hc
  refine ⟨h t c hc, ?_⟩
  obtain ⟨c', e, hc'⟩ := h (-t) c hc
  refine ⟨c', ?_, hc'⟩
  rw [pinnedX_neg]
  rw [pinnedX_neg, neg_neg] at e
  exact e

theorem rootSpan_le_zInvSubgroup {P : ((Fin Tag.E6.rank → ℤ) → K) → Prop}
    {S : Set (Fin Tag.E6.rank → ℤ)}
    (h : ∀ α ∈ S, ∀ t : K, pinnedX .E6 K α t ∈ zInvSubgroup K P) :
    rootSpan .E6 K S ≤ zInvSubgroup K P :=
  iSup₂_le fun α hα => (Subgroup.closure_le _).2 (by
    rintro _ ⟨t, rfl⟩
    exact h α hα t)

theorem torusGroup_le_zInvSubgroup {P : ((Fin Tag.E6.rank → ℤ) → K) → Prop}
    (h : ∀ g ∈ torusGroup .E6 K, ∀ c, P c → P fun β => torusRootChar g β * c β) :
    torusGroup .E6 K ≤ zInvSubgroup K P := by
  intro g hg c hc
  have hr : ∀ β ∈ zPsi, IsRoot .E6 β := fun _ hβ => isRoot_of_mem_zPsi hβ
  refine ⟨⟨_, conj_rootProd_of_mem_torusGroup hg hr c, h g hg c hc⟩, ⟨_, ?_, h _ (inv_mem hg) c hc⟩⟩
  have := conj_rootProd_of_mem_torusGroup (inv_mem hg) hr c
  rwa [inv_inv] at this

@[expose] def zInvB (c : (Fin Tag.E6.rank → ℤ) → K) : Prop :=
  (∀ β ∈ zFrame, c β ≠ 0) ∧ ∀ β ∈ zLow, c β = 0

@[expose] def zInvTop (c : (Fin Tag.E6.rank → ℤ) → K) : Prop :=
  ∀ β ∈ zTop, c β = 0

@[expose] def zInvLevel2 (c₀ c : (Fin Tag.E6.rank → ℤ) → K) : Prop :=
  ∀ β ∈ zPsi, β 3 = 2 → c β = c₀ β

theorem zInvB_zCoeff : zInvB (zCoeff (K := K)) := by
  refine ⟨fun β hβ => ?_, fun β hβ => ?_⟩
  · simp only [zCoeff]
    rw [ite_eq_left hβ]
    exact one_ne_zero
  · have : β ∉ zFrame := fun h => by
      have h1 := zLow_check
      have hd : ∀ β ∈ zLow, β ∉ zFrame := by decide +kernel
      exact hd β hβ h
    simp only [zCoeff]
    rw [ite_eq_right this]

theorem zInvTop_zCoeff : zInvTop (zCoeff (K := K)) := fun β hβ => by
  simp only [zCoeff]
  rw [ite_eq_right (not_mem_zFrame_of_mem_zTop hβ)]

theorem conj_zInvB_of_pos [CharP K 2] {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot .E6 α ∧ 0 < height α) (t : K) {c : (Fin Tag.E6.rank → ℤ) → K}
    (hc : zInvB c) : zInvB (conjCoeff α t zPsi c) := by
  have hfeed : ∀ ρ, (ρ ∈ zFrame ∨ ρ ∈ zLow) → ρ ∈ zPsi →
      conjCoeff α t zPsi c ρ = c ρ := fun ρ hρ hρΨ =>
    conjCoeff_apply_of_forall zPsi_nodup t c hρΨ fun β hβ he =>
      hc.2 β (zLow_closed hρ hβ hα he)
  refine ⟨fun β hβ => ?_, fun β hβ => ?_⟩
  · rw [hfeed β (Or.inl hβ) (mem_zPsi_of_mem_zFrame hβ)]
    exact hc.1 β hβ
  · rw [hfeed β (Or.inr hβ) (mem_zPsi_of_mem_zLow hβ)]
    exact hc.2 β hβ

theorem level_nonneg_of_pos {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α ∧ 0 < height α) :
    0 ≤ α 3 := by
  rcases hα.1.nonneg_or_nonpos with h | h
  · exact h 3
  · exfalso
    have : height α ≤ 0 := by
      rw [height]
      exact Finset.sum_nonpos fun j _ => h j
    omega

theorem borelGroup_le_zInvSubgroup_zInvB [CharP K 2] :
    borelGroup .E6 K ≤ zInvSubgroup K zInvB := by
  refine sup_le (torusGroup_le_zInvSubgroup fun g hg c hc => ⟨fun β hβ => ?_, fun β hβ => ?_⟩)
    (rootSpan_le_zInvSubgroup fun α hα t => pinnedX_mem_zInvSubgroup (fun t c hc =>
      ⟨_, conj_rootProd_zPsi hα.1 (level_nonneg_of_pos hα) t c, conj_zInvB_of_pos hα t hc⟩) t)
  · exact mul_ne_zero (torusRootChar_ne_zero (torusGroup_le_diagonalGroup hg) β) (hc.1 β hβ)
  · show torusRootChar g β * c β = 0
    rw [hc.2 β hβ, mul_zero]

theorem parabolicLevi_le_zInvSubgroup_zInvTop [CharP K 2] :
    parabolicLevi .E6 K zNodes ≤ zInvSubgroup K zInvTop := by
  have hgen : ∀ {α : Fin Tag.E6.rank → ℤ}, IsRoot .E6 α → α 3 = 0 → ∀ t : K,
      pinnedX .E6 K α t ∈ zInvSubgroup K zInvTop := by
    intro α hα hα3 t
    refine pinnedX_mem_zInvSubgroup (fun t c hc => ⟨_, conj_rootProd_zPsi hα hα3.ge t c, ?_⟩) t
    intro ρ hρ
    rw [conjCoeff_apply_of_forall zPsi_nodup t c (mem_zPsi_of_mem_zTop hρ) fun β hβ he => ?_]
    · exact hc ρ hρ
    · refine hc β ?_
      rcases zPsi_level_check β hβ with h2 | ht
      · exfalso
        have h3 := zPsi_check.2.2.2 ρ hρ
        have : (α + β) 3 = α 3 + β 3 := rfl
        rw [he] at this
        omega
      · exact ht
  refine sup_le (torusGroup_le_zInvSubgroup fun g _ c hc β hβ => by
      show torusRootChar g β * c β = 0
      rw [hc β hβ, mul_zero])
    ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, hj, t, rfl | rfl⟩
  · rw [← pinnedX_single]
    refine hgen (isRoot_single .E6 j) ?_ t
    exact Pi.single_eq_of_ne (show (3 : Fin Tag.E6.rank) ≠ j from fun h => hj (h ▸ rfl)) _
  · rw [← pinnedX_neg_single]
    refine hgen (isRoot_neg_single .E6 j) ?_ t
    rw [Pi.neg_apply, Pi.single_eq_of_ne (show (3 : Fin Tag.E6.rank) ≠ j from fun h => hj (h ▸ rfl)),
      neg_zero]

theorem parabolicRadical_le_zInvSubgroup_zInvLevel2 [CharP K 2]
    (c₀ : (Fin Tag.E6.rank → ℤ) → K) :
    parabolicRadical .E6 K zNodes ≤ zInvSubgroup K (zInvLevel2 c₀) := by
  refine rootSpan_le_zInvSubgroup fun α hα t => ?_
  have hαpos : IsRoot .E6 α ∧ 0 < height α := hα.1
  have hα3 : 1 ≤ α 3 := by
    have h0 := level_nonneg_of_pos hαpos
    have hne : α 3 ≠ 0 := fun h0' => hα.2 ⟨⟨hαpos.1, fun i hi => by
      have : i = 3 := by simpa [zNodes] using hi
      rw [this]; exact h0'⟩, hαpos⟩
    omega
  refine pinnedX_mem_zInvSubgroup (fun t c hc =>
    ⟨_, conj_rootProd_zPsi hαpos.1 (level_nonneg_of_pos hαpos) t c, ?_⟩) t
  intro ρ hρ hρ2
  rw [conjCoeff_apply_of_forall zPsi_nodup t c hρ fun β hβ he => ?_]
  · exact hc ρ hρ hρ2
  · exfalso
    have hβ3 := level_of_mem_zPsi hβ
    have : (α + β) 3 = α 3 + β 3 := rfl
    rw [he] at this
    omega

theorem zPsi_map_comm (w : WeylGroup .E6) :
    RootCommFamily .E6 K (zPsi.map fun β => w • β) := by
  intro β hβ β' hβ' s t
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hβ
  obtain ⟨γ', hγ', rfl⟩ := List.mem_map.1 hβ'
  refine CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (IsRoot.smul (isRoot_of_mem_zPsi hγ) w)
    (IsRoot.smul (isRoot_of_mem_zPsi hγ') w) ?_ ?_ s t
  · rw [← smul_neg]
    exact fun h => ne_neg_of_mem_zPsi hγ hγ' (smul_left_cancel w h)
  · rw [← smul_add, isRoot_smul_iff]
    exact zPsi_add_not_isRoot hγ hγ'

theorem canonicalRep_mul_rootProd_zPsi [CharP K 2] (w : WeylGroup .E6)
    (c : (Fin Tag.E6.rank → ℤ) → K) :
    canonicalRep (coxeterSystem .E6) K w * rootProd .E6 K zPsi c *
        (canonicalRep (coxeterSystem .E6) K w)⁻¹ =
      rootProd .E6 K (zPsi.map fun β => w • β) fun ρ => c (w⁻¹ • ρ) := by
  rw [rootProd, canonicalRep_mul_list_prod_mul_inv_of_charTwo w
    (fun _ hβ => isRoot_of_mem_zPsi hβ) c, rootProd, List.map_map]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  simp [inv_smul_smul]

theorem smul_zFrame_of_commute_zAS [CharP K 2] {g : ModGL .E6 K} {w : WeylGroup .E6}
    (hw : g ∈ bruhatCell .E6 K w) (hgz : g * zAS K = zAS K * g) :
    w ∈ parabolicWeylGroup .E6 zNodes ∧ ∀ β ∈ zFrame, w • β ∈ zFrame := by
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  set n := canonicalRep (coxeterSystem .E6) K w with hn
  obtain ⟨⟨cu, ecu, hcu⟩, -⟩ := borelGroup_le_zInvSubgroup_zInvB hb' zCoeff zInvB_zCoeff
  obtain ⟨-, ⟨cv, ecv, hcv⟩⟩ := borelGroup_le_zInvSubgroup_zInvB hb zCoeff zInvB_zCoeff
  rw [rootProd_zPsi_zCoeff] at ecu ecv
  have hkey : n * rootProd .E6 K zPsi cu * n⁻¹ = rootProd .E6 K zPsi cv := by
    rw [← ecu, ← ecv]
    have e : b * n * b' * zAS K * (b * n * b')⁻¹ = zAS K := by
      rw [hgz]
      group
    calc n * (b' * zAS K * b'⁻¹) * n⁻¹ = b⁻¹ * (b * n * b' * zAS K * (b * n * b')⁻¹) * b := by
          group
      _ = b⁻¹ * zAS K * b := by rw [e]
  rw [hn, canonicalRep_mul_rootProd_zPsi] at hkey
  refine mem_parabolicWeylGroup_of_smul_zFrame fun β hβ => ?_
  have hβΨ := mem_zPsi_of_mem_zFrame hβ
  have hLnd : (zPsi.map fun β => w • β).Nodup := zPsi_nodup.map (MulAction.injective w)
  have hLr : ∀ ρ ∈ zPsi.map (fun β => w • β), IsRoot .E6 ρ := by
    intro ρ hρ
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hρ
    exact IsRoot.smul (isRoot_of_mem_zPsi hγ) w
  obtain ⟨hmem, heq⟩ := mem_and_eq_of_rootProd_eq hLnd hLr (zPsi_map_comm w) zPsi_nodup
    (fun _ hρ => pos_of_mem_zPsi hρ) zPsi_comm hkey (List.mem_map_of_mem hβΨ)
    (by rw [inv_smul_smul]; exact hcu.1 β hβ)
  rw [inv_smul_smul] at heq
  have hne : cv (w • β) ≠ 0 := by rw [heq]; exact hcu.1 β hβ
  have hnl : w • β ∉ zLow := fun h => hne (hcv.2 _ h)
  simp only [zPsi, zHigh, List.mem_append] at hmem ⊢
  rcases hmem with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd h hnl

theorem mem_parabolicSubgroup_of_commute_zAS [CharP K 2] {g : ModGL .E6 K}
    (hg : g ∈ adjointGroup .E6 K) (hgz : g * zAS K = zAS K * g) :
    g ∈ parabolicSubgroup .E6 K zNodes := by
  obtain ⟨w, hw⟩ := CFSG.SeitzReduction.exists_mem_bruhatCell_of_mem_adjointGroup hg
  have hmem : g ∈ (parabolicSubgroup .E6 K zNodes : Set (ModGL .E6 K)) := by
    rw [(standard_parabolic_cells .E6 K).1 zNodes]
    exact Set.mem_biUnion (smul_zFrame_of_commute_zAS hw hgz).1 hw
  exact hmem

theorem commute_of_mul_commute_zAS [CharP K 2] {q m : ModGL .E6 K}
    (hq : q ∈ parabolicRadical .E6 K zNodes) (hm : m ∈ parabolicLevi .E6 K zNodes)
    (hgz : q * m * zAS K = zAS K * (q * m)) :
    m * zAS K = zAS K * m ∧ q * zAS K = zAS K * q := by
  obtain ⟨⟨c₁, e₁, h₁⟩, -⟩ := parabolicLevi_le_zInvSubgroup_zInvTop hm zCoeff zInvTop_zCoeff
  rw [rootProd_zPsi_zCoeff] at e₁
  obtain ⟨⟨c₂, e₂, h₂⟩, -⟩ := parabolicRadical_le_zInvSubgroup_zInvLevel2 c₁ hq c₁
    (fun _ _ _ => rfl)
  have hz : q * (m * zAS K * m⁻¹) * q⁻¹ = zAS K := by
    calc q * (m * zAS K * m⁻¹) * q⁻¹ = (q * m) * zAS K * (q * m)⁻¹ := by group
      _ = zAS K := by rw [hgz]; group
  rw [e₁, e₂, ← rootProd_zPsi_zCoeff] at hz
  have hc₂ := rootProd_injective zPsi_nodup (fun _ hρ => pos_of_mem_zPsi hρ) hz
  have hc₁ : ∀ β ∈ zPsi, c₁ β = zCoeff β := by
    intro β hβ
    rcases zPsi_level_check β hβ with h2 | ht
    · rw [← h₂ β hβ h2, hc₂ β hβ]
    · rw [h₁ β ht]
      simp only [zCoeff]
      rw [ite_eq_right (not_mem_zFrame_of_mem_zTop ht)]
  have hmz : m * zAS K * m⁻¹ = zAS K := by
    rw [e₁, rootProd_congr hc₁, rootProd_zPsi_zCoeff]
  have hm' : m * zAS K = zAS K * m := by
    calc m * zAS K = m * zAS K * m⁻¹ * m := by group
      _ = zAS K * m := by rw [hmz]
  refine ⟨hm', ?_⟩
  calc q * zAS K = q * m * zAS K * m⁻¹ := by
        rw [mul_assoc q m, hm', ← mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
    _ = zAS K * (q * m) * m⁻¹ := by rw [hgz]
    _ = zAS K * q := by group

theorem centralizer_zAS_inf_eq [CharP K 2] :
    centralizer ({zAS K} : Set (ModGL .E6 K)) ⊓ adjointGroup .E6 K =
      (parabolicRadical .E6 K zNodes ⊓ centralizer ({zAS K} : Set (ModGL .E6 K))) ⊔
        (parabolicLevi .E6 K zNodes ⊓ centralizer ({zAS K} : Set (ModGL .E6 K))) := by
  refine le_antisymm (fun g hg => ?_) (sup_le (fun q hq => ?_) (fun m hm => ?_))
  · obtain ⟨hgC, hgG⟩ := mem_inf.1 hg
    have hgz : g * zAS K = zAS K * g := (mem_centralizer_singleton_iff.1 hgC)
    have hgP := mem_parabolicSubgroup_of_commute_zAS hgG hgz
    obtain ⟨-, -, -, -, -, -, huniq, -⟩ := parabolic_root_radical_Levi_factors .E6 K zNodes
    obtain ⟨⟨q, m⟩, ⟨hq, hm, rfl⟩, -⟩ := huniq g hgP
    obtain ⟨hmz, hqz⟩ := commute_of_mul_commute_zAS hq hm hgz
    exact mul_mem (mem_sup_left (mem_inf.2 ⟨hq, mem_centralizer_singleton_iff.2 hqz⟩))
      (mem_sup_right (mem_inf.2 ⟨hm, mem_centralizer_singleton_iff.2 hmz⟩))
  · exact mem_inf.2 ⟨(mem_inf.1 hq).2, posUnipotent_le_adjointGroup
      (parabolicRadical_le_posUnipotent _ (mem_inf.1 hq).1)⟩
  · exact mem_inf.2 ⟨(mem_inf.1 hm).2, parabolicLevi_le_adjointGroup .E6 K zNodes (mem_inf.1 hm).1⟩

end CFSG.SeitzReduction.E6Pilot
