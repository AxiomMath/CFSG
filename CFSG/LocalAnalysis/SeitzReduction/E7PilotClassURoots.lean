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

local instance e7ClassUNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

@[expose] def uFrame : List (Fin Tag.E7.rank → ℤ) := oddDerivE7UFrame

@[expose] def uLow : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1, 1],
    ![0, 1, 1, 1, 1, 1, 1], ![1, 0, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 2, 1, 1], ![1, 1, 1, 2, 1, 1, 1]]

@[expose] def uHigh : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 2, 1],
    ![1, 1, 2, 3, 2, 1, 1], ![1, 1, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 2, 1, 1],
    ![1, 1, 2, 3, 3, 2, 1], ![1, 2, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 3, 2, 1],
    ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1]]

@[expose] def uPsi : List (Fin Tag.E7.rank → ℤ) := uFrame ++ uLow ++ uHigh

@[expose] def uOmega : Fin Tag.E7.rank → ℤ := ![2, 3, 4, 6, 5, 4, 3]

@[expose] def uNodes : Set (Fin Tag.E7.rank) := {j | j ≠ 6}

@[expose] def uLevel (β : Fin Tag.E7.rank → ℤ) : ℤ := β 6

theorem uLevel_add (β β' : Fin Tag.E7.rank → ℤ) : uLevel (β + β') = uLevel β + uLevel β' := by
  simp only [uLevel, Pi.add_apply]

theorem uLevel_neg (β : Fin Tag.E7.rank → ℤ) : uLevel (-β) = -uLevel β := by
  simp only [uLevel, Pi.neg_apply]

theorem uPsi_check :
    uPsi.Nodup ∧ ∀ β ∈ uPsi, isRootB .E7 β = true ∧ 0 < height β ∧ uLevel β = 1 := by
  decide +kernel

theorem uPsi_filter_uFrame : uPsi.filter (· ∈ uFrame) = uFrame := by
  decide +kernel

theorem uPsi_complete_check : ∀ k < Tag.E7.rootCertificate.roots.length,
    1 ≤ uLevel (Tag.E7.rootCertificate.root k) → Tag.E7.rootCertificate.root k ∈ uPsi := by
  decide +kernel

theorem uPsi_add_check : ∀ β ∈ uPsi, ∀ β' ∈ uPsi, isRootB .E7 (β + β') = false := by
  decide +kernel

theorem uLow_check : ∀ ρ ∈ uFrame ++ uLow, ∀ β ∈ uPsi,
    isRootB .E7 (ρ - β) = true → 0 < height (ρ - β) → β ∈ uLow := by
  decide +kernel

theorem uLowHigh_not_mem_uFrame : (∀ β ∈ uLow, β ∉ uFrame) ∧ ∀ β ∈ uHigh, β ∉ uFrame := by
  decide +kernel

@[expose] def uTripleB : Bool :=
  (uFrame ++ uHigh).all fun a => (uFrame ++ uHigh).all fun b =>
    !(iform a b == 0) || (uFrame ++ uHigh).all fun c =>
      !(iform a c == 0 && iform b c == 0 && a != b && a != c && b != c) ||
        (uFrame.contains a && uFrame.contains b && uFrame.contains c)

theorem uTripleB_eq_true : uTripleB = true := by
  decide +kernel

theorem uTriple_check {a b c : Fin Tag.E7.rank → ℤ} (ha : a ∈ uFrame ++ uHigh)
    (hb : b ∈ uFrame ++ uHigh) (hc : c ∈ uFrame ++ uHigh)
    (hab : iform a b = 0) (hac : iform a c = 0) (hbc : iform b c = 0)
    (hab' : a ≠ b) (hac' : a ≠ c) (hbc' : b ≠ c) :
    a ∈ uFrame ∧ b ∈ uFrame ∧ c ∈ uFrame := by
  have h := uTripleB_eq_true
  simp only [uTripleB, List.all_eq_true] at h
  have h4 := h a ha b hb
  simp only [hab, beq_self_eq_true, Bool.not_true, Bool.false_or, List.all_eq_true] at h4
  have h5 := h4 c hc
  have e1 : (a != b) = true := bne_iff_ne.2 hab'
  have e2 : (a != c) = true := bne_iff_ne.2 hac'
  have e3 : (b != c) = true := bne_iff_ne.2 hbc'
  simp only [hac, hbc, beq_self_eq_true, Bool.and_true, e1, e2, e3, Bool.not_true,
    Bool.false_or, Bool.and_eq_true, List.contains_iff_mem] at h5
  exact ⟨h5.1.1, h5.1.2, h5.2⟩

theorem uFrame_pairwise :
    uFrame.Nodup ∧ uFrame.Pairwise fun β β' => iform β β' = 0 := by
  decide +kernel

theorem uFrame_sum : uFrame.sum = uOmega := by
  decide +kernel

theorem iform_single_uOmega (j : Fin Tag.E7.rank) :
    iform (Pi.single j 1) uOmega = if j = 6 then 2 else 0 := by
  revert j
  decide +kernel

theorem reflect_uOmega : ∀ j : Fin Tag.E7.rank, j ≠ 6 → reflect .E7 j uOmega = uOmega := by
  decide +kernel


theorem uPsi_nodup : uPsi.Nodup := uPsi_check.1

theorem isRoot_of_mem_uPsi {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ uPsi) : IsRoot .E7 β :=
  isRootB_iff.1 (uPsi_check.2 β hβ).1

theorem pos_of_mem_uPsi {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ uPsi) :
    IsRoot .E7 β ∧ 0 < height β :=
  ⟨isRoot_of_mem_uPsi hβ, (uPsi_check.2 β hβ).2.1⟩

theorem level_of_mem_uPsi {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ uPsi) : uLevel β = 1 :=
  (uPsi_check.2 β hβ).2.2

theorem mem_uPsi_of_mem_uFrame {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ uFrame) : β ∈ uPsi := by
  simp only [uPsi, List.mem_append]
  exact Or.inl (Or.inl hβ)

theorem mem_uPsi_of_mem_uLow {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ uLow) : β ∈ uPsi := by
  simp only [uPsi, List.mem_append]
  exact Or.inl (Or.inr hβ)

theorem mem_uPsi_of_mem_uHigh {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ uHigh) : β ∈ uPsi := by
  simp only [uPsi, List.mem_append]
  exact Or.inr hβ

theorem mem_uPsi_of_level {ρ : Fin Tag.E7.rank → ℤ} (hρ : IsRoot .E7 ρ) (h : 1 ≤ uLevel ρ) :
    ρ ∈ uPsi := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hρ
  exact uPsi_complete_check k hk h

theorem uPsi_add_not_isRoot {β β' : Fin Tag.E7.rank → ℤ} (hβ : β ∈ uPsi) (hβ' : β' ∈ uPsi) :
    ¬IsRoot .E7 (β + β') := by
  rw [← isRootB_iff, uPsi_add_check β hβ β' hβ']
  exact Bool.false_ne_true

theorem ne_neg_of_mem_uPsi {β β' : Fin Tag.E7.rank → ℤ} (hβ : β ∈ uPsi) (hβ' : β' ∈ uPsi) :
    β ≠ -β' := by
  intro h
  have h1 := (pos_of_mem_uPsi hβ).2
  have h2 := (pos_of_mem_uPsi hβ').2
  rw [h, height_neg] at h1
  omega

theorem uLow_closed {ρ β α : Fin Tag.E7.rank → ℤ} (hρ : ρ ∈ uFrame ∨ ρ ∈ uLow) (hβ : β ∈ uPsi)
    (hα : IsRoot .E7 α ∧ 0 < height α) (h : α + β = ρ) : β ∈ uLow := by
  have e : ρ - β = α := by rw [← h]; abel
  refine uLow_check ρ (List.mem_append.2 hρ) β hβ ?_ ?_
  · rw [e]
    exact isRootB_iff.2 hα.1
  · rw [e]
    exact hα.2

@[expose] def uφ : Fin Tag.E7.rank → ℤ := ![1, 1, 1, 2, 2, 1, 1]
@[expose] def uψ : Fin Tag.E7.rank → ℤ := ![1, 1, 2, 2, 1, 1, 1]
@[expose] def uθ : Fin Tag.E7.rank → ℤ := ![0, 1, 1, 2, 2, 2, 1]

theorem uFrame_eq : uFrame = [uφ, uψ, uθ] := rfl

theorem mem_uFrame {β : Fin Tag.E7.rank → ℤ} :
    β ∈ uFrame ↔ β = uφ ∨ β = uψ ∨ β = uθ := by
  simp [uFrame_eq]

theorem uFrame_iform_ne :
    (iform uφ uψ = 0 ∧ iform uφ uθ = 0 ∧ iform uψ uθ = 0) ∧ (uφ ≠ uψ ∧ uφ ≠ uθ ∧ uψ ≠ uθ) := by
  decide +kernel

theorem smul_mem_uFrame_of_mem_uFrameHigh {w : WeylGroup .E7}
    (h : ∀ β ∈ uFrame, w • β ∈ uFrame ∨ w • β ∈ uHigh) :
    ∀ β ∈ uFrame, w • β ∈ uFrame := by
  have hm : ∀ β ∈ uFrame, w • β ∈ uFrame ++ uHigh := fun β hβ => List.mem_append.2 (h β hβ)
  have hne : ∀ {β β' : Fin Tag.E7.rank → ℤ}, β ≠ β' → w • β ≠ w • β' :=
    fun hb e => hb (smul_left_cancel w e)
  have ho : ∀ {β β' : Fin Tag.E7.rank → ℤ}, iform β β' = 0 → iform (w • β) (w • β') = 0 :=
    fun hb => by rw [iform_smul]; exact hb
  obtain ⟨⟨o1, o2, o3⟩, ⟨n1, n2, n3⟩⟩ := uFrame_iform_ne
  obtain ⟨k1, k2, k3⟩ := uTriple_check (hm uφ (mem_uFrame.2 (Or.inl rfl)))
    (hm uψ (mem_uFrame.2 (Or.inr (Or.inl rfl)))) (hm uθ (mem_uFrame.2 (Or.inr (Or.inr rfl))))
    (ho o1) (ho o2) (ho o3) (hne n1) (hne n2) (hne n3)
  intro β hβ
  rcases mem_uFrame.1 hβ with rfl | rfl | rfl
  · exact k1
  · exact k2
  · exact k3

theorem smul_uOmega_of_smul_mem_uFrame {w : WeylGroup .E7}
    (h : ∀ β ∈ uFrame, w • β ∈ uFrame) : w • uOmega = uOmega := by
  have hnd : (uFrame.map (w • ·)).Nodup := uFrame_pairwise.1.map (MulAction.injective w)
  have hsub : uFrame.map (w • ·) ⊆ uFrame := fun β hβ => by
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hβ
    exact h γ hγ
  have hperm : (uFrame.map (w • ·)).Perm uFrame :=
    (List.subperm_of_subset hnd hsub).perm_of_length_le (by rw [List.length_map])
  rw [← uFrame_sum, List.smul_sum, hperm.sum_eq]

theorem mem_parabolicWeylGroup_of_smul_uOmega :
    ∀ (n : ℕ) (w : WeylGroup .E7), (coxeterSystem .E7).length w = n → w • uOmega = uOmega →
      w ∈ parabolicWeylGroup .E7 uNodes := by
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
    have hzero : iform (Pi.single i 1) uOmega = 0 := by
      have e : iform (w • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) uOmega =
          iform (Pi.single i 1) uOmega := by
        conv_lhs => rw [← hw]
        exact iform_smul w _ _
      have hle : iform (w • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) uOmega ≤ 0 := by
        rw [iform_comm, F4Pilot.iform_eq_sum_mul_iform_single]
        refine Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (hcoef j) ?_
        rw [iform_comm, iform_single_uOmega]
        split_ifs <;> omega
      have hge : 0 ≤ iform (Pi.single i 1) uOmega := by
        rw [iform_single_uOmega]
        split_ifs <;> omega
      omega
    have hiJ : i ∈ uNodes := by
      rw [iform_single_uOmega] at hzero
      intro h6
      rw [ite_eq_left h6] at hzero
      exact absurd hzero (by decide)
    have hsi : simple .E7 i ∈ parabolicWeylGroup .E7 uNodes :=
      Subgroup.subset_closure ⟨i, hiJ, rfl⟩
    have hws : (w * simple .E7 i) • uOmega = uOmega := by
      rw [mul_smul, simple_smul, reflect_uOmega i hiJ, hw]
    have hmem := ih _ (by omega) (w * simple .E7 i) rfl hws
    have := mul_mem hmem hsi
    rwa [mul_assoc, simple_mul_simple_self, mul_one] at this

theorem mem_parabolicWeylGroup_of_smul_uFrame {w : WeylGroup .E7}
    (h : ∀ β ∈ uFrame, w • β ∈ uFrame ∨ w • β ∈ uHigh) :
    w ∈ parabolicWeylGroup .E7 uNodes ∧ ∀ β ∈ uFrame, w • β ∈ uFrame :=
  ⟨mem_parabolicWeylGroup_of_smul_uOmega _ w rfl
    (smul_uOmega_of_smul_mem_uFrame (smul_mem_uFrame_of_mem_uFrameHigh h)),
    smul_mem_uFrame_of_mem_uFrameHigh h⟩

end CFSG.SeitzReduction.E7Pilot
