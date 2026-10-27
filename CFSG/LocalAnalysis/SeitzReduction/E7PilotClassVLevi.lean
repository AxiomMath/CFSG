module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVSp6
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVBruhat

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)

theorem e7A5_long_check : ∀ I : Fin 6, ∀ β ∈ vFrame,
    isRootB .E7 (e7A5Root I (Fin.rev I) + β) = false := by
  decide +kernel

@[expose] def e7A5PairB (I J : Fin 6) : Bool :=
  vFrame.any fun β₀ => vFrame.any fun β₁ =>
    isRootB .E7 (e7A5Root I J + β₀) &&
      (vFrame.all fun β => β == β₀ || !isRootB .E7 (e7A5Root I J + β)) &&
      isRootB .E7 (e7A5Root (Fin.rev J) (Fin.rev I) + β₁) &&
      (vFrame.all fun β => β == β₁ || !isRootB .E7 (e7A5Root (Fin.rev J) (Fin.rev I) + β)) &&
      (e7A5Root I J + β₀ == e7A5Root (Fin.rev J) (Fin.rev I) + β₁) &&
      !isRootB .E7 (e7A5Root I J + (e7A5Root I J + β₀))

theorem e7A5PairB_check : ∀ I J : Fin 6, I ≠ J → J ≠ Fin.rev I → e7A5PairB I J = true := by
  decide +kernel

theorem e7A5_pair_check {I J : Fin 6} (hIJ : I ≠ J) (hJI : J ≠ Fin.rev I) :
    ∃ β₀ ∈ vFrame, ∃ β₁ ∈ vFrame, isRootB .E7 (e7A5Root I J + β₀) = true ∧
      (∀ β ∈ vFrame, β ≠ β₀ → isRootB .E7 (e7A5Root I J + β) = false) ∧
      isRootB .E7 (e7A5Root (Fin.rev J) (Fin.rev I) + β₁) = true ∧
      (∀ β ∈ vFrame, β ≠ β₁ → isRootB .E7 (e7A5Root (Fin.rev J) (Fin.rev I) + β) = false) ∧
      e7A5Root I J + β₀ = e7A5Root (Fin.rev J) (Fin.rev I) + β₁ ∧
      isRootB .E7 (e7A5Root I J + (e7A5Root I J + β₀)) = false := by
  have h := e7A5PairB_check I J hIJ hJI
  simp only [e7A5PairB, List.any_eq_true, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨β₀, h₀, β₁, h₁, ⟨⟨⟨⟨⟨hr0, hu0⟩, hr1⟩, hu1⟩, hs⟩, hn⟩⟩ := h
  refine ⟨β₀, h₀, β₁, h₁, hr0, fun β hβ hne => ?_, hr1, fun β hβ hne => ?_, hs, hn⟩
  · rcases hu0 β hβ with h | h
    · exact absurd h hne
    · exact h
  · rcases hu1 β hβ with h | h
    · exact absurd h hne
    · exact h

variable {K : Type} [Field K]

theorem ne_of_vLevel_zero {a β : Fin Tag.E7.rank → ℤ} (ha0 : vLevel a = 0) (hβ : β ∈ vPsi) :
    a ≠ β ∧ a ≠ -β := by
  have h2 := level_of_mem_vPsi hβ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at ha0
    omega
  · rw [h, vLevel_neg] at ha0
    omega

theorem conj_list_prod_pinnedX_vPsi [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hF : ∀ β ∈ F, β ∈ vPsi) (hnd : F.Nodup) {a β₀ : Fin Tag.E7.rank → ℤ} (ha : IsRoot .E7 a)
    (ha0 : vLevel a = 0) (hβ₀ : β₀ ∈ vPsi) (hab : IsRoot .E7 (a + β₀))
    (huniq : ∀ β ∈ F, β ≠ β₀ → ¬IsRoot .E7 (a + β)) (t : K) :
    pinnedX .E7 K a t * (F.map fun β => pinnedX .E7 K β 1).prod * (pinnedX .E7 K a t)⁻¹ =
      (if β₀ ∈ F then pinnedX .E7 K (a + β₀) t else 1) * (F.map fun β => pinnedX .E7 K β 1).prod := by
  have hρΨ : a + β₀ ∈ vPsi := mem_vPsi_of_level hab (by
    rw [vLevel_add, ha0, zero_add]
    exact level_of_mem_vPsi hβ₀)
  induction F with
  | nil => simp
  | cons β F ih =>
    rw [List.nodup_cons] at hnd
    have hβΨ := hF β List.mem_cons_self
    have ih' := ih (fun γ hγ => hF γ (List.mem_cons_of_mem _ hγ)) hnd.2
      (fun γ hγ hne => huniq γ (List.mem_cons_of_mem _ hγ) hne)
    have hsplit : pinnedX .E7 K a t * ((β :: F).map fun β => pinnedX .E7 K β 1).prod *
        (pinnedX .E7 K a t)⁻¹ =
        (pinnedX .E7 K a t * pinnedX .E7 K β 1 * (pinnedX .E7 K a t)⁻¹) *
          (pinnedX .E7 K a t * (F.map fun β => pinnedX .E7 K β 1).prod * (pinnedX .E7 K a t)⁻¹) := by
      rw [List.map_cons, List.prod_cons]
      group
    rw [hsplit, ih', List.map_cons, List.prod_cons]
    by_cases hβ : β = β₀
    · subst hβ
      have hcomm := CFSG.SeitzReduction.commutatorElement_pinnedX_of_oddDerivLaced
        CharTwo.two_eq_zero oddDerivLacedCheck_E7 ha (isRoot_of_mem_vPsi hβΨ)
        (ne_of_vLevel_zero ha0 hβΨ).1 (ne_of_vLevel_zero ha0 hβΨ).2 hab t (1 : K)
      rw [mul_one, commutatorElement_def] at hcomm
      have e : pinnedX .E7 K a t * pinnedX .E7 K β 1 * (pinnedX .E7 K a t)⁻¹ =
          pinnedX .E7 K (a + β) t * pinnedX .E7 K β 1 := by
        rw [← hcomm]
        group
      rw [e, ite_eq_right hnd.1, ite_eq_left List.mem_cons_self, one_mul, mul_assoc]
    · have hc : Commute (pinnedX .E7 K a t) (pinnedX .E7 K β 1) :=
        CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv ha (isRoot_of_mem_vPsi hβΨ)
          (ne_of_vLevel_zero ha0 hβΨ).2 (huniq β List.mem_cons_self hβ) t 1
      rw [hc.eq, mul_inv_cancel_right]
      have hmem : (β₀ ∈ β :: F) ↔ β₀ ∈ F := by
        rw [List.mem_cons]
        exact ⟨fun h => h.resolve_left (Ne.symm hβ), Or.inr⟩
      by_cases h₀ : β₀ ∈ F
      · rw [ite_eq_left h₀, ite_eq_left (hmem.2 h₀), ← mul_assoc, ← mul_assoc,
          (vPsi_comm β hβΨ (a + β₀) hρΨ 1 t).eq]
      · rw [ite_eq_right h₀, ite_eq_right (fun h => h₀ (hmem.1 h)), one_mul, one_mul]

theorem vAS_eq_prod : vAS K = (vFrame.map fun β => pinnedX .E7 K β 1).prod := rfl

theorem conj_vAS_of_unique [CharP K 2] {a β₀ : Fin Tag.E7.rank → ℤ} (ha : IsRoot .E7 a)
    (ha0 : vLevel a = 0) (hβ₀ : β₀ ∈ vFrame) (hab : IsRoot .E7 (a + β₀))
    (huniq : ∀ β ∈ vFrame, β ≠ β₀ → ¬IsRoot .E7 (a + β)) (t : K) :
    pinnedX .E7 K a t * vAS K * (pinnedX .E7 K a t)⁻¹ = pinnedX .E7 K (a + β₀) t * vAS K := by
  rw [vAS_eq_prod, conj_list_prod_pinnedX_vPsi (fun β hβ => mem_vPsi_of_mem_vFrame hβ)
    vFrame_pairwise.1 ha ha0 (mem_vPsi_of_mem_vFrame hβ₀) hab huniq t, ite_eq_left hβ₀]

theorem commute_vAS_of_forall {a : Fin Tag.E7.rank → ℤ} (ha : IsRoot .E7 a)
    (ha0 : vLevel a = 0) (h : ∀ β ∈ vFrame, ¬IsRoot .E7 (a + β)) (t : K) :
    Commute (pinnedX .E7 K a t) (vAS K) := by
  rw [vAS_eq_prod]
  exact Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
    exact CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv ha
      (isRoot_of_mem_vPsi (mem_vPsi_of_mem_vFrame hβ))
      (ne_of_vLevel_zero ha0 (mem_vPsi_of_mem_vFrame hβ)).2 (h β hβ) t 1

theorem commute_e7A5Elt_long (I : Fin 6) (t : K) :
    Commute (e7A5Elt K I (Fin.rev I) t) (e7ASRep K 4) := by
  have hI : I ≠ Fin.rev I := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_rev] at this
    omega
  refine Subtype.ext ?_
  have h := commute_vAS_of_forall (K := K) (isRoot_e7A5Root hI) (vLevel_e7A5Root hI)
    (fun β hβ hr => by
      have := e7A5_long_check I β hβ
      rw [← isRootB_iff, this] at hr
      exact Bool.false_ne_true hr) t
  simp only [Subgroup.coe_mul, coe_e7A5Elt, coe_e7ASRep_four]
  exact h.eq

theorem commute_e7A5Elt_pair [CharP K 2] {I J : Fin 6} (hIJ : I ≠ J) (hJI : J ≠ Fin.rev I)
    (t : K) :
    Commute (e7A5Elt K I J t * e7A5Elt K (Fin.rev J) (Fin.rev I) t) (e7ASRep K 4) := by
  obtain ⟨β₀, h₀, β₁, h₁, hr0, hu0, hr1, hu1, hs, hn⟩ := e7A5_pair_check hIJ hJI
  have hIJ' : Fin.rev J ≠ Fin.rev I := fun h => hIJ (Fin.rev_injective h).symm
  set b := e7A5Root I J
  set b' := e7A5Root (Fin.rev J) (Fin.rev I)
  have hb := isRoot_e7A5Root hIJ
  have hb' := isRoot_e7A5Root hIJ'
  have hb0 := vLevel_e7A5Root hIJ
  have hb0' := vLevel_e7A5Root hIJ'
  have notroot : ∀ {γ : Fin Tag.E7.rank → ℤ}, isRootB .E7 γ = false → ¬IsRoot .E7 γ :=
    fun h hr => by rw [← isRootB_iff, h] at hr; exact Bool.false_ne_true hr
  have e1 := conj_vAS_of_unique (K := K) hb' hb0' h₁ (isRootB_iff.1 hr1)
    (fun β hβ hne => notroot (hu1 β hβ hne)) t
  have e2 := conj_vAS_of_unique (K := K) hb hb0 h₀ (isRootB_iff.1 hr0)
    (fun β hβ hne => notroot (hu0 β hβ hne)) t
  rw [← hs] at e1
  have hρΨ : b + β₀ ∈ vPsi := mem_vPsi_of_level (isRootB_iff.1 hr0) (by
    rw [vLevel_add, hb0, zero_add]
    exact level_of_mem_vPsi (mem_vPsi_of_mem_vFrame h₀))
  have e3 : Commute (pinnedX .E7 K b t) (pinnedX .E7 K (b + β₀) t) :=
    CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv hb (isRootB_iff.1 hr0)
      (ne_of_vLevel_zero hb0 hρΨ).2 (notroot hn) t t
  have key : (pinnedX .E7 K b t * pinnedX .E7 K b' t) * vAS K *
      (pinnedX .E7 K b t * pinnedX .E7 K b' t)⁻¹ = vAS K := by
    calc (pinnedX .E7 K b t * pinnedX .E7 K b' t) * vAS K *
          (pinnedX .E7 K b t * pinnedX .E7 K b' t)⁻¹ =
          pinnedX .E7 K b t * (pinnedX .E7 K b' t * vAS K * (pinnedX .E7 K b' t)⁻¹) *
            (pinnedX .E7 K b t)⁻¹ := by group
      _ = pinnedX .E7 K (b + β₀) t * (pinnedX .E7 K b t * vAS K * (pinnedX .E7 K b t)⁻¹) := by
          rw [e1, ← mul_assoc, e3.eq]
          group
      _ = pinnedX .E7 K (b + β₀) (t + t) * vAS K := by
          rw [e2, ← mul_assoc, ← pinnedX_add]
      _ = vAS K := by
          rw [CharTwo.add_self_eq_zero, pinnedX_zero, one_mul]
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, coe_e7A5Elt, coe_e7ASRep_four]
  calc (pinnedX .E7 K b t * pinnedX .E7 K b' t) * vAS K =
        ((pinnedX .E7 K b t * pinnedX .E7 K b' t) * vAS K *
          (pinnedX .E7 K b t * pinnedX .E7 K b' t)⁻¹) *
            (pinnedX .E7 K b t * pinnedX .E7 K b' t) := by group
    _ = vAS K * (pinnedX .E7 K b t * pinnedX .E7 K b' t) := by rw [key]

section Finite

variable [Finite K] [CharP K 2]

theorem spToAdjointE7_elt_mem_centralizer (r : TauCeti.GLSymplecticFin.RootSubgroupIndex 3)
    (c : K) :
    spToAdjointE7 K (elt r c) ∈ centralizer ({e7ASRep K 4} : Set (adjointGroup .E7 K)) := by
  rw [mem_centralizer_singleton_iff]
  cases r with
  | positiveLong i =>
    rw [spToAdjointE7_positiveLong, spIdx_inr]
    exact (commute_e7A5Elt_long _ c).eq
  | negativeLong i =>
    rw [spToAdjointE7_negativeLong, spIdx_inl]
    exact (commute_e7A5Elt_long _ c).eq
  | difference i j hij =>
    have h := commute_e7A5Elt_pair (K := K) (I := e7SpIdx (.inl i)) (J := e7SpIdx (.inl j))
      (spIdx_ne (by simpa using hij)) (by rw [← spIdx_inr]; exact spIdx_ne Sum.inl_ne_inr) c
    rw [← spIdx_inr, ← spIdx_inr] at h
    rw [spToAdjointE7_difference]
    exact h.eq
  | positiveSum i j hij =>
    have h := commute_e7A5Elt_pair (K := K) (I := e7SpIdx (.inl i)) (J := e7SpIdx (.inr j))
      (spIdx_ne Sum.inl_ne_inr) (by rw [← spIdx_inr]; exact spIdx_ne (by simpa using hij.ne'))
      c
    rw [← spIdx_inl, ← spIdx_inr] at h
    rw [spToAdjointE7_positiveSum]
    exact h.eq
  | negativeSum i j hij =>
    have h := commute_e7A5Elt_pair (K := K) (I := e7SpIdx (.inr i)) (J := e7SpIdx (.inl j))
      (spIdx_ne Sum.inr_ne_inl) (by rw [← spIdx_inl]; exact spIdx_ne (by simpa using hij.ne'))
      c
    rw [← spIdx_inr, ← spIdx_inl] at h
    rw [spToAdjointE7_negativeSum]
    exact h.eq

theorem range_spToAdjointE7_le_centralizer :
    (spToAdjointE7 K).range ≤ centralizer ({e7ASRep K 4} : Set (adjointGroup .E7 K)) := by
  have htop : (centralizer ({e7ASRep K 4} : Set (adjointGroup .E7 K))).comap
      (spToAdjointE7 K) = ⊤ :=
    eq_top_of_elt_mem fun r c => spToAdjointE7_elt_mem_centralizer r c
  rintro _ ⟨A, rfl⟩
  have hA : A ∈ (centralizer ({e7ASRep K 4} : Set (adjointGroup .E7 K))).comap
      (spToAdjointE7 K) := by
    rw [htop]
    exact Subgroup.mem_top A
  exact hA

theorem e7A5Root_alpha4 : e7A5Root 2 3 = e7RepPreHigh 4 ∧ e7A5Root 3 2 = -e7RepPreHigh 4 ∧
    e7SpIdx (.inl 2) = 2 ∧ e7SpIdx (.inr 2) = 3 := by
  decide +kernel

theorem rootSL2_alpha4_le_range :
    rootSubgroup .E7 K (e7RepPreHigh 4) ⊔ rootSubgroup .E7 K (-e7RepPreHigh 4) ≤
      (spToAdjointE7 K).range.map (adjointGroup .E7 K).subtype := by
  obtain ⟨h1, h2, h3, h4⟩ := e7A5Root_alpha4
  refine sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨c, rfl⟩
    refine ⟨spToAdjointE7 K (elt (.positiveLong 2) c), ⟨_, rfl⟩, ?_⟩
    rw [spToAdjointE7_positiveLong, h3, h4]
    simp only [Subgroup.subtype_apply, coe_e7A5Elt, h1]
  · rintro _ ⟨c, rfl⟩
    refine ⟨spToAdjointE7 K (elt (.negativeLong 2) c), ⟨_, rfl⟩, ?_⟩
    rw [spToAdjointE7_negativeLong, h3, h4]
    simp only [Subgroup.subtype_apply, coe_e7A5Elt, h2]

variable (K) in
@[expose] noncomputable def vLevi : Subgroup (adjointGroup .E7 K) :=
  (spToAdjointE7 K).range.map (MulAut.conj (e7RepConj K 4)).toMonoidHom

theorem vLevi_le_centralizer :
    vLevi K ≤ centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K)) := by
  rintro _ ⟨l, hl, rfl⟩
  have hl' := mem_centralizer_singleton_iff.1 (range_spToAdjointE7_le_centralizer hl)
  rw [mem_centralizer_singleton_iff, ← e7RepConj_mul_e7ASRep_mul_inv (K := K) 4]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc e7RepConj K 4 * l * (e7RepConj K 4)⁻¹ *
        (e7RepConj K 4 * e7ASRep K 4 * (e7RepConj K 4)⁻¹) =
        e7RepConj K 4 * (l * e7ASRep K 4) * (e7RepConj K 4)⁻¹ := by group
    _ = e7RepConj K 4 * (e7ASRep K 4 * l) * (e7RepConj K 4)⁻¹ := by rw [hl']
    _ = e7RepConj K 4 * e7ASRep K 4 * (e7RepConj K 4)⁻¹ *
        (e7RepConj K 4 * l * (e7RepConj K 4)⁻¹) := by group

theorem highRootSL2_le_vLevi :
    (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) ≤ vLevi K := by
  intro h hh
  rw [mem_subgroupOf, ← map_conj_e7RepConj_rootSL2_preHigh (K := K) 4] at hh
  obtain ⟨y, hy, hyh⟩ := hh
  obtain ⟨l, hl, rfl⟩ := rootSL2_alpha4_le_range hy
  refine ⟨l, hl, Subtype.ext ?_⟩
  rw [← hyh]
  rfl

variable (K) in
@[expose] noncomputable def vLeviEquiv : StatedSp 3 K ≃* vLevi K :=
  (MonoidHom.ofInjective spToAdjointE7_injective).trans
    ((MulAut.conj (e7RepConj K 4)).subgroupMap (spToAdjointE7 K).range)

theorem isSimpleGroup_vLevi : IsSimpleGroup (vLevi K) := by
  have := isSimpleGroup_statedSp_three K
  exact (vLeviEquiv K).symm.isSimpleGroup

end Finite

end CFSG.SeitzReduction.E7Pilot
