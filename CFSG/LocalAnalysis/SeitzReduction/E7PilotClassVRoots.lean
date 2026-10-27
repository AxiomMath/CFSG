module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.Chevalley.StandardParabolic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivationE7Frames

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)

local instance e7ClassVNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

@[expose] def vFrame : List (Fin Tag.E7.rank → ℤ) := oddDerivE7VFrame

@[expose] def vLow : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 1, 0, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 1, 1],
    ![0, 1, 1, 2, 2, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 1, 1]]

@[expose] def vHigh : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 2, 1],
    ![1, 1, 2, 3, 2, 1, 1], ![1, 1, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 2, 1, 1],
    ![1, 1, 2, 3, 3, 2, 1], ![1, 2, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 3, 2, 1],
    ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1]]

@[expose] def vPsi : List (Fin Tag.E7.rank → ℤ) := vFrame ++ vLow ++ vHigh

@[expose] def vOmega : Fin Tag.E7.rank → ℤ := ![3, 5, 6, 9, 7, 5, 3]

@[expose] def vNodes : Set (Fin Tag.E7.rank) := {j | j ≠ 1 ∧ j ≠ 6}

@[expose] def vLevel (β : Fin Tag.E7.rank → ℤ) : ℤ := β 1 + β 6

theorem vLevel_add (β β' : Fin Tag.E7.rank → ℤ) : vLevel (β + β') = vLevel β + vLevel β' := by
  simp only [vLevel, Pi.add_apply]
  ring

theorem vLevel_neg (β : Fin Tag.E7.rank → ℤ) : vLevel (-β) = -vLevel β := by
  simp only [vLevel, Pi.neg_apply]
  ring

theorem vPsi_check :
    vPsi.Nodup ∧ (∀ β ∈ vPsi, isRootB .E7 β = true ∧ 0 < height β ∧ 2 ≤ vLevel β) ∧
      (∀ β ∈ vFrame ++ vLow, vLevel β = 2) := by
  decide +kernel

theorem vPsi_level_check : ∀ β ∈ vPsi, vLevel β = 2 ∨ vLevel β = 3 := by
  decide +kernel

theorem vPsi_filter_vFrame : vPsi.filter (· ∈ vFrame) = vFrame := by
  decide +kernel

theorem vPsi_complete_check : ∀ k < Tag.E7.rootCertificate.roots.length,
    2 ≤ vLevel (Tag.E7.rootCertificate.root k) → Tag.E7.rootCertificate.root k ∈ vPsi := by
  decide +kernel

theorem vPsi_add_check : ∀ β ∈ vPsi, ∀ β' ∈ vPsi, isRootB .E7 (β + β') = false := by
  decide +kernel

theorem vLow_check : ∀ ρ ∈ vFrame ++ vLow, ∀ β ∈ vPsi,
    isRootB .E7 (ρ - β) = true → 0 < height (ρ - β) → β ∈ vLow := by
  decide +kernel

theorem vLowHigh_not_mem_vFrame : (∀ β ∈ vLow, β ∉ vFrame) ∧ ∀ β ∈ vHigh, β ∉ vFrame := by
  decide +kernel

@[expose] def vQuadB : Bool :=
  (vFrame ++ vHigh).all fun a => (vFrame ++ vHigh).all fun b =>
    !(iform a b == 0) || (vFrame ++ vHigh).all fun c =>
      !(iform a c == 0 && iform b c == 0) || (vFrame ++ vHigh).all fun d =>
        !(iform a d == 0 && iform b d == 0 && iform c d == 0 &&
            a != b && a != c && a != d && b != c && b != d && c != d) ||
          (vFrame.contains a && vFrame.contains b && vFrame.contains c && vFrame.contains d)

theorem vQuadB_eq_true : vQuadB = true := by
  decide +kernel

theorem vQuad_check {a b c d : Fin Tag.E7.rank → ℤ} (ha : a ∈ vFrame ++ vHigh)
    (hb : b ∈ vFrame ++ vHigh) (hc : c ∈ vFrame ++ vHigh) (hd : d ∈ vFrame ++ vHigh)
    (hab : iform a b = 0) (hac : iform a c = 0) (had : iform a d = 0) (hbc : iform b c = 0)
    (hbd : iform b d = 0) (hcd : iform c d = 0) (hab' : a ≠ b) (hac' : a ≠ c) (had' : a ≠ d)
    (hbc' : b ≠ c) (hbd' : b ≠ d) (hcd' : c ≠ d) :
    a ∈ vFrame ∧ b ∈ vFrame ∧ c ∈ vFrame ∧ d ∈ vFrame := by
  have h := vQuadB_eq_true
  simp only [vQuadB, List.all_eq_true] at h
  have h4 := h a ha b hb
  simp only [hab, beq_self_eq_true, Bool.not_true, Bool.false_or, List.all_eq_true] at h4
  have h5 := h4 c hc
  simp only [hac, hbc, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
    List.all_eq_true] at h5
  have h6 := h5 d hd
  have e1 : (a != b) = true := bne_iff_ne.2 hab'
  have e2 : (a != c) = true := bne_iff_ne.2 hac'
  have e3 : (a != d) = true := bne_iff_ne.2 had'
  have e4 : (b != c) = true := bne_iff_ne.2 hbc'
  have e5 : (b != d) = true := bne_iff_ne.2 hbd'
  have e6 : (c != d) = true := bne_iff_ne.2 hcd'
  simp only [had, hbd, hcd, beq_self_eq_true, Bool.and_true, e1, e2, e3, e4, e5,
    e6, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.contains_iff_mem] at h6
  exact ⟨h6.1.1.1, h6.1.1.2, h6.1.2, h6.2⟩

theorem vFrame_pairwise :
    vFrame.Nodup ∧ vFrame.Pairwise fun β β' => iform β β' = 0 := by
  decide +kernel

theorem vFrame_sum : vFrame.sum = vOmega := by
  decide +kernel

theorem iform_single_vOmega (j : Fin Tag.E7.rank) :
    iform (Pi.single j 1) vOmega = if j = 1 ∨ j = 6 then 1 else 0 := by
  revert j
  decide +kernel

theorem reflect_vOmega : ∀ j : Fin Tag.E7.rank, j ≠ 1 → j ≠ 6 → reflect .E7 j vOmega = vOmega := by
  decide +kernel

theorem vPsi_nodup : vPsi.Nodup := vPsi_check.1

theorem isRoot_of_mem_vPsi {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ vPsi) : IsRoot .E7 β :=
  isRootB_iff.1 (vPsi_check.2.1 β hβ).1

theorem pos_of_mem_vPsi {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ vPsi) :
    IsRoot .E7 β ∧ 0 < height β :=
  ⟨isRoot_of_mem_vPsi hβ, (vPsi_check.2.1 β hβ).2.1⟩

theorem level_of_mem_vPsi {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ vPsi) : 2 ≤ vLevel β :=
  (vPsi_check.2.1 β hβ).2.2

theorem mem_vPsi_of_mem_vFrame {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ vFrame) : β ∈ vPsi := by
  simp only [vPsi, List.mem_append]
  exact Or.inl (Or.inl hβ)

theorem mem_vPsi_of_mem_vLow {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ vLow) : β ∈ vPsi := by
  simp only [vPsi, List.mem_append]
  exact Or.inl (Or.inr hβ)

theorem mem_vPsi_of_level {ρ : Fin Tag.E7.rank → ℤ} (hρ : IsRoot .E7 ρ) (h : 2 ≤ vLevel ρ) :
    ρ ∈ vPsi := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hρ
  exact vPsi_complete_check k hk h

theorem vPsi_add_not_isRoot {β β' : Fin Tag.E7.rank → ℤ} (hβ : β ∈ vPsi) (hβ' : β' ∈ vPsi) :
    ¬IsRoot .E7 (β + β') := by
  rw [← isRootB_iff, vPsi_add_check β hβ β' hβ']
  exact Bool.false_ne_true

theorem ne_neg_of_mem_vPsi {β β' : Fin Tag.E7.rank → ℤ} (hβ : β ∈ vPsi) (hβ' : β' ∈ vPsi) :
    β ≠ -β' := by
  intro h
  have h1 := (pos_of_mem_vPsi hβ).2
  have h2 := (pos_of_mem_vPsi hβ').2
  rw [h, height_neg] at h1
  omega

theorem vLow_closed {ρ β α : Fin Tag.E7.rank → ℤ} (hρ : ρ ∈ vFrame ∨ ρ ∈ vLow) (hβ : β ∈ vPsi)
    (hα : IsRoot .E7 α ∧ 0 < height α) (h : α + β = ρ) : β ∈ vLow := by
  have e : ρ - β = α := by rw [← h]; abel
  refine vLow_check ρ (List.mem_append.2 hρ) β hβ ?_ ?_
  · rw [e]
    exact isRootB_iff.2 hα.1
  · rw [e]
    exact hα.2

@[expose] def vγ : Fin Tag.E7.rank → ℤ := ![1, 2, 2, 3, 2, 1, 0]
@[expose] def vθ : Fin Tag.E7.rank → ℤ := ![0, 1, 1, 2, 2, 2, 1]
@[expose] def vψ : Fin Tag.E7.rank → ℤ := ![1, 1, 2, 2, 1, 1, 1]
@[expose] def vφ : Fin Tag.E7.rank → ℤ := ![1, 1, 1, 2, 2, 1, 1]

theorem vFrame_eq : vFrame = [vγ, vθ, vψ, vφ] := rfl

theorem mem_vFrame {β : Fin Tag.E7.rank → ℤ} :
    β ∈ vFrame ↔ β = vγ ∨ β = vθ ∨ β = vψ ∨ β = vφ := by
  simp [vFrame_eq]

theorem vFrame_iform_ne :
    (iform vγ vθ = 0 ∧ iform vγ vψ = 0 ∧ iform vγ vφ = 0 ∧ iform vθ vψ = 0 ∧ iform vθ vφ = 0 ∧
      iform vψ vφ = 0) ∧ (vγ ≠ vθ ∧ vγ ≠ vψ ∧ vγ ≠ vφ ∧ vθ ≠ vψ ∧ vθ ≠ vφ ∧ vψ ≠ vφ) := by
  decide +kernel

theorem smul_mem_vFrame_of_mem_vFrameHigh {w : WeylGroup .E7}
    (h : ∀ β ∈ vFrame, w • β ∈ vFrame ∨ w • β ∈ vHigh) :
    ∀ β ∈ vFrame, w • β ∈ vFrame := by
  have hm : ∀ β ∈ vFrame, w • β ∈ vFrame ++ vHigh := fun β hβ => List.mem_append.2 (h β hβ)
  have hne : ∀ {β β' : Fin Tag.E7.rank → ℤ}, β ≠ β' → w • β ≠ w • β' :=
    fun hb e => hb (smul_left_cancel w e)
  have ho : ∀ {β β' : Fin Tag.E7.rank → ℤ}, iform β β' = 0 → iform (w • β) (w • β') = 0 :=
    fun hb => by rw [iform_smul]; exact hb
  obtain ⟨⟨o1, o2, o3, o4, o5, o6⟩, ⟨n1, n2, n3, n4, n5, n6⟩⟩ := vFrame_iform_ne
  obtain ⟨k1, k2, k3, k4⟩ := vQuad_check (hm vγ (mem_vFrame.2 (Or.inl rfl)))
    (hm vθ (mem_vFrame.2 (Or.inr (Or.inl rfl)))) (hm vψ (mem_vFrame.2 (Or.inr (Or.inr (Or.inl rfl)))))
    (hm vφ (mem_vFrame.2 (Or.inr (Or.inr (Or.inr rfl))))) (ho o1) (ho o2) (ho o3) (ho o4) (ho o5)
    (ho o6) (hne n1) (hne n2) (hne n3) (hne n4) (hne n5) (hne n6)
  intro β hβ
  rcases mem_vFrame.1 hβ with rfl | rfl | rfl | rfl
  · exact k1
  · exact k2
  · exact k3
  · exact k4

theorem smul_vOmega_of_smul_mem_vFrame {w : WeylGroup .E7}
    (h : ∀ β ∈ vFrame, w • β ∈ vFrame) : w • vOmega = vOmega := by
  have hnd : (vFrame.map (w • ·)).Nodup := vFrame_pairwise.1.map (MulAction.injective w)
  have hsub : vFrame.map (w • ·) ⊆ vFrame := fun β hβ => by
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hβ
    exact h γ hγ
  have hperm : (vFrame.map (w • ·)).Perm vFrame :=
    (List.subperm_of_subset hnd hsub).perm_of_length_le (by rw [List.length_map])
  rw [← vFrame_sum, List.smul_sum, hperm.sum_eq]

theorem mem_parabolicWeylGroup_of_smul_vOmega :
    ∀ (n : ℕ) (w : WeylGroup .E7), (coxeterSystem .E7).length w = n → w • vOmega = vOmega →
      w ∈ parabolicWeylGroup .E7 vNodes := by
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
    have hzero : iform (Pi.single i 1) vOmega = 0 := by
      have e : iform (w • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) vOmega =
          iform (Pi.single i 1) vOmega := by
        conv_lhs => rw [← hw]
        exact iform_smul w _ _
      have hle : iform (w • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) vOmega ≤ 0 := by
        rw [iform_comm, F4Pilot.iform_eq_sum_mul_iform_single]
        refine Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (hcoef j) ?_
        rw [iform_comm, iform_single_vOmega]
        split_ifs <;> omega
      have hge : 0 ≤ iform (Pi.single i 1) vOmega := by
        rw [iform_single_vOmega]
        split_ifs <;> omega
      omega
    have hiJ : i ∈ vNodes := by
      rw [iform_single_vOmega] at hzero
      by_contra hJ
      simp only [vNodes, Set.mem_ofPred_eq, not_and_or, not_not] at hJ
      rw [ite_eq_left (hJ.elim Or.inl Or.inr)] at hzero
      exact one_ne_zero hzero
    have hsi : simple .E7 i ∈ parabolicWeylGroup .E7 vNodes :=
      Subgroup.subset_closure ⟨i, hiJ, rfl⟩
    have hws : (w * simple .E7 i) • vOmega = vOmega := by
      rw [mul_smul, simple_smul, reflect_vOmega i hiJ.1 hiJ.2, hw]
    have hmem := ih _ (by omega) (w * simple .E7 i) rfl hws
    have := mul_mem hmem hsi
    rwa [mul_assoc, simple_mul_simple_self, mul_one] at this

theorem mem_parabolicWeylGroup_of_smul_vFrame {w : WeylGroup .E7}
    (h : ∀ β ∈ vFrame, w • β ∈ vFrame ∨ w • β ∈ vHigh) :
    w ∈ parabolicWeylGroup .E7 vNodes ∧ ∀ β ∈ vFrame, w • β ∈ vFrame :=
  ⟨mem_parabolicWeylGroup_of_smul_vOmega _ w rfl
    (smul_vOmega_of_smul_mem_vFrame (smul_mem_vFrame_of_mem_vFrameHigh h)),
    smul_mem_vFrame_of_mem_vFrameHigh h⟩

end CFSG.SeitzReduction.E7Pilot
