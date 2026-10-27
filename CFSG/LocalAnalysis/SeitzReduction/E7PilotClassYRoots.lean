module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.Chevalley.StandardParabolic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivationE7Frames

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)

local instance e7ClassYNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

@[expose] def yFrame : List (Fin Tag.E7.rank → ℤ) := oddDerivE7YFrame

@[expose] def yLow : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 1, 1, 2, 2, 2, 1], ![1, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 2, 2, 1],
    ![1, 1, 2, 3, 2, 2, 1]]

@[expose] def yHigh : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 2, 2, 3, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1],
    ![2, 2, 3, 4, 3, 2, 1]]

@[expose] def yPsi : List (Fin Tag.E7.rank → ℤ) := yFrame ++ yLow ++ yHigh

@[expose] def yOmega : Fin Tag.E7.rank → ℤ := ![2, 3, 4, 6, 5, 4, 2]

@[expose] def yNodes : Set (Fin Tag.E7.rank) := {j | j ≠ 5}

@[expose] def yLevel (β : Fin Tag.E7.rank → ℤ) : ℤ := β 5

theorem yLevel_add (β β' : Fin Tag.E7.rank → ℤ) : yLevel (β + β') = yLevel β + yLevel β' := by
  simp only [yLevel, Pi.add_apply]

theorem yLevel_neg (β : Fin Tag.E7.rank → ℤ) : yLevel (-β) = -yLevel β := by
  simp only [yLevel, Pi.neg_apply]

theorem yPsi_check :
    yPsi.Nodup ∧ ∀ β ∈ yPsi, isRootB .E7 β = true ∧ 0 < height β ∧ yLevel β = 2 := by
  decide +kernel

theorem yPsi_filter_yFrame : yPsi.filter (· ∈ yFrame) = yFrame := by
  decide +kernel

theorem yPsi_complete_check : ∀ k < Tag.E7.rootCertificate.roots.length,
    2 ≤ yLevel (Tag.E7.rootCertificate.root k) → Tag.E7.rootCertificate.root k ∈ yPsi := by
  decide +kernel

theorem yPsi_add_check : ∀ β ∈ yPsi, ∀ β' ∈ yPsi, isRootB .E7 (β + β') = false := by
  decide +kernel

theorem yLow_check : ∀ ρ ∈ yFrame ++ yLow, ∀ β ∈ yPsi,
    isRootB .E7 (ρ - β) = true → 0 < height (ρ - β) → β ∈ yLow := by
  decide +kernel

theorem yLowHigh_not_mem_yFrame : (∀ β ∈ yLow, β ∉ yFrame) ∧ ∀ β ∈ yHigh, β ∉ yFrame := by
  decide +kernel

@[expose] def yPairB : Bool :=
  (yFrame ++ yHigh).all fun a => (yFrame ++ yHigh).all fun b =>
    !(iform a b == 0 && a != b) || (yFrame.contains a && yFrame.contains b)

theorem yPairB_eq_true : yPairB = true := by
  decide +kernel

theorem yPair_check {a b : Fin Tag.E7.rank → ℤ} (ha : a ∈ yFrame ++ yHigh)
    (hb : b ∈ yFrame ++ yHigh) (hab : iform a b = 0) (hne : a ≠ b) :
    a ∈ yFrame ∧ b ∈ yFrame := by
  have h := yPairB_eq_true
  simp only [yPairB, List.all_eq_true] at h
  have h2 := h a ha b hb
  have e : (a != b) = true := bne_iff_ne.2 hne
  simp only [hab, beq_self_eq_true, e, Bool.and_true, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, List.contains_iff_mem] at h2
  exact h2

theorem yFrame_pairwise :
    yFrame.Nodup ∧ yFrame.Pairwise fun β β' => iform β β' = 0 := by
  decide +kernel

theorem yFrame_sum : yFrame.sum = yOmega := by
  decide +kernel

theorem iform_single_yOmega (j : Fin Tag.E7.rank) :
    iform (Pi.single j 1) yOmega = if j = 5 then 1 else 0 := by
  revert j
  decide +kernel

theorem reflect_yOmega : ∀ j : Fin Tag.E7.rank, j ≠ 5 → reflect .E7 j yOmega = yOmega := by
  decide +kernel

theorem yPsi_nodup : yPsi.Nodup := yPsi_check.1

theorem isRoot_of_mem_yPsi {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ yPsi) : IsRoot .E7 β :=
  isRootB_iff.1 (yPsi_check.2 β hβ).1

theorem pos_of_mem_yPsi {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ yPsi) :
    IsRoot .E7 β ∧ 0 < height β :=
  ⟨isRoot_of_mem_yPsi hβ, (yPsi_check.2 β hβ).2.1⟩

theorem level_of_mem_yPsi {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ yPsi) : yLevel β = 2 :=
  (yPsi_check.2 β hβ).2.2

theorem mem_yPsi_of_mem_yFrame {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ yFrame) : β ∈ yPsi := by
  simp only [yPsi, List.mem_append]
  exact Or.inl (Or.inl hβ)

theorem mem_yPsi_of_mem_yLow {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ yLow) : β ∈ yPsi := by
  simp only [yPsi, List.mem_append]
  exact Or.inl (Or.inr hβ)

theorem mem_yPsi_of_level {ρ : Fin Tag.E7.rank → ℤ} (hρ : IsRoot .E7 ρ) (h : 2 ≤ yLevel ρ) :
    ρ ∈ yPsi := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hρ
  exact yPsi_complete_check k hk h

theorem yLevel_le_two {ρ : Fin Tag.E7.rank → ℤ} (hρ : IsRoot .E7 ρ) : yLevel ρ ≤ 2 := by
  by_cases h : 2 ≤ yLevel ρ
  · rw [level_of_mem_yPsi (mem_yPsi_of_level hρ h)]
  · omega

theorem yPsi_add_not_isRoot {β β' : Fin Tag.E7.rank → ℤ} (hβ : β ∈ yPsi) (hβ' : β' ∈ yPsi) :
    ¬IsRoot .E7 (β + β') := by
  rw [← isRootB_iff, yPsi_add_check β hβ β' hβ']
  exact Bool.false_ne_true

theorem ne_neg_of_mem_yPsi {β β' : Fin Tag.E7.rank → ℤ} (hβ : β ∈ yPsi) (hβ' : β' ∈ yPsi) :
    β ≠ -β' := by
  intro h
  have h1 := (pos_of_mem_yPsi hβ).2
  have h2 := (pos_of_mem_yPsi hβ').2
  rw [h, height_neg] at h1
  omega

theorem yLow_closed {ρ β α : Fin Tag.E7.rank → ℤ} (hρ : ρ ∈ yFrame ∨ ρ ∈ yLow)
    (hβ : β ∈ yPsi) (hα : IsRoot .E7 α ∧ 0 < height α) (h : α + β = ρ) : β ∈ yLow := by
  have e : ρ - β = α := by rw [← h]; abel
  refine yLow_check ρ (List.mem_append.2 hρ) β hβ ?_ ?_
  · rw [e]
    exact isRootB_iff.2 hα.1
  · rw [e]
    exact hα.2

@[expose] def yφ : Fin Tag.E7.rank → ℤ := ![1, 1, 2, 3, 3, 2, 1]
@[expose] def yψ : Fin Tag.E7.rank → ℤ := ![1, 2, 2, 3, 2, 2, 1]

theorem yFrame_eq : yFrame = [yφ, yψ] := rfl

theorem mem_yFrame {β : Fin Tag.E7.rank → ℤ} :
    β ∈ yFrame ↔ β = yφ ∨ β = yψ := by
  simp [yFrame_eq]

theorem yFrame_iform_ne : iform yφ yψ = 0 ∧ yφ ≠ yψ := by
  decide +kernel

theorem smul_mem_yFrame_of_mem_yFrameHigh {w : WeylGroup .E7}
    (h : ∀ β ∈ yFrame, w • β ∈ yFrame ∨ w • β ∈ yHigh) :
    ∀ β ∈ yFrame, w • β ∈ yFrame := by
  have hm : ∀ β ∈ yFrame, w • β ∈ yFrame ++ yHigh := fun β hβ => List.mem_append.2 (h β hβ)
  have hne : ∀ {β β' : Fin Tag.E7.rank → ℤ}, β ≠ β' → w • β ≠ w • β' :=
    fun hb e => hb (smul_left_cancel w e)
  have ho : ∀ {β β' : Fin Tag.E7.rank → ℤ}, iform β β' = 0 → iform (w • β) (w • β') = 0 :=
    fun hb => by rw [iform_smul]; exact hb
  obtain ⟨o, n⟩ := yFrame_iform_ne
  obtain ⟨k1, k2⟩ := yPair_check (hm yφ (mem_yFrame.2 (Or.inl rfl)))
    (hm yψ (mem_yFrame.2 (Or.inr rfl))) (ho o) (hne n)
  intro β hβ
  rcases mem_yFrame.1 hβ with rfl | rfl
  · exact k1
  · exact k2

theorem smul_yOmega_of_smul_mem_yFrame {w : WeylGroup .E7}
    (h : ∀ β ∈ yFrame, w • β ∈ yFrame) : w • yOmega = yOmega := by
  have hnd : (yFrame.map (w • ·)).Nodup := yFrame_pairwise.1.map (MulAction.injective w)
  have hsub : yFrame.map (w • ·) ⊆ yFrame := fun β hβ => by
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hβ
    exact h γ hγ
  have hperm : (yFrame.map (w • ·)).Perm yFrame :=
    (List.subperm_of_subset hnd hsub).perm_of_length_le (by rw [List.length_map])
  rw [← yFrame_sum, List.smul_sum, hperm.sum_eq]

theorem mem_parabolicWeylGroup_of_smul_yOmega :
    ∀ (n : ℕ) (w : WeylGroup .E7), (coxeterSystem .E7).length w = n → w • yOmega = yOmega →
      w ∈ parabolicWeylGroup .E7 yNodes := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hlen hw
    by_cases hw1 : w = 1
    · rw [hw1]
      exact one_mem _
    obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one hw1
    have hroot := IsRoot.smul (isRoot_single .E7 i) w
    have hdesc : (coxeterSystem .E7).IsRightDescent w i :=
      (smul_single_mem_negRoots_iff w i).1 ⟨hroot, hi⟩
    have hl := (isRightDescent_iff_length w i).1 hdesc
    have hcoef := (IsRoot.height_neg_iff hroot).1 hi
    have hzero : iform (Pi.single i 1) yOmega = 0 := by
      have e : iform (w • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) yOmega =
          iform (Pi.single i 1) yOmega := by
        conv_lhs => rw [← hw]
        exact iform_smul w _ _
      have hle : iform (w • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) yOmega ≤ 0 := by
        rw [iform_comm, F4Pilot.iform_eq_sum_mul_iform_single]
        refine Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (hcoef j) ?_
        rw [iform_comm, iform_single_yOmega]
        split_ifs <;> omega
      have hge : 0 ≤ iform (Pi.single i 1) yOmega := by
        rw [iform_single_yOmega]
        split_ifs <;> omega
      omega
    have hiJ : i ∈ yNodes := by
      rw [iform_single_yOmega] at hzero
      intro h5
      rw [ite_eq_left h5] at hzero
      exact one_ne_zero hzero
    have hsi : simple .E7 i ∈ parabolicWeylGroup .E7 yNodes :=
      Subgroup.subset_closure ⟨i, hiJ, rfl⟩
    have hws : (w * simple .E7 i) • yOmega = yOmega := by
      rw [mul_smul, simple_smul, reflect_yOmega i hiJ, hw]
    have hmem := ih _ (by omega) (w * simple .E7 i) rfl hws
    have := mul_mem hmem hsi
    rwa [mul_assoc, simple_mul_simple_self, mul_one] at this

theorem mem_parabolicWeylGroup_of_smul_yFrame {w : WeylGroup .E7}
    (h : ∀ β ∈ yFrame, w • β ∈ yFrame ∨ w • β ∈ yHigh) :
    w ∈ parabolicWeylGroup .E7 yNodes ∧ ∀ β ∈ yFrame, w • β ∈ yFrame :=
  ⟨mem_parabolicWeylGroup_of_smul_yOmega _ w rfl
    (smul_yOmega_of_smul_mem_yFrame (smul_mem_yFrame_of_mem_yFrameHigh h)),
    smul_mem_yFrame_of_mem_yFrameHigh h⟩

end CFSG.SeitzReduction.E7Pilot
