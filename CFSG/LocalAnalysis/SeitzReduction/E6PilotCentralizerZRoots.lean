module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.Chevalley.ParabolicWeylStabilizer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)

local instance e6CentralizerZNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def zγ : Fin Tag.E6.rank → ℤ := ![0, 1, 1, 2, 2, 1]

@[expose] def zδ : Fin Tag.E6.rank → ℤ := ![1, 1, 1, 2, 1, 1]

@[expose] def zε : Fin Tag.E6.rank → ℤ := ![1, 1, 2, 2, 1, 0]

@[expose] def zFrame : List (Fin Tag.E6.rank → ℤ) := [zγ, zδ, zε]

@[expose] def zUp : List (Fin Tag.E6.rank → ℤ) :=
  [![1, 1, 1, 2, 2, 1], ![1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 1]]

@[expose] def zTop : List (Fin Tag.E6.rank → ℤ) :=
  [![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1]]

@[expose] def zLow : List (Fin Tag.E6.rank → ℤ) :=
  [![0, 1, 1, 2, 1, 0], ![0, 1, 1, 2, 1, 1], ![1, 1, 1, 2, 1, 0]]

@[expose] def zHigh : List (Fin Tag.E6.rank → ℤ) := zUp ++ zTop

@[expose] def zPsi : List (Fin Tag.E6.rank → ℤ) := zFrame ++ zUp ++ zTop ++ zLow

@[expose] def zOmega : Fin Tag.E6.rank → ℤ := ![2, 3, 4, 6, 4, 2]

@[expose] def zNodes : Set (Fin Tag.E6.rank) := {j | j ≠ 3}

theorem zPsi_check :
    zPsi.Nodup ∧ (∀ β ∈ zPsi, isRootB .E6 β = true ∧ 0 < height β ∧ 2 ≤ β 3) ∧
      (∀ β ∈ zFrame ++ zUp ++ zLow, β 3 = 2) ∧ (∀ β ∈ zTop, β 3 = 3) := by
  decide +kernel

theorem zPsi_nodup : zPsi.Nodup := zPsi_check.1

theorem isRoot_of_mem_zPsi {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ zPsi) : IsRoot .E6 β :=
  isRootB_iff.1 (zPsi_check.2.1 β hβ).1

theorem pos_of_mem_zPsi {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ zPsi) :
    IsRoot .E6 β ∧ 0 < height β :=
  ⟨isRoot_of_mem_zPsi hβ, (zPsi_check.2.1 β hβ).2.1⟩

theorem level_of_mem_zPsi {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ zPsi) : 2 ≤ β 3 :=
  (zPsi_check.2.1 β hβ).2.2

theorem mem_zPsi_of_mem_zFrame {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ zFrame) : β ∈ zPsi := by
  simp only [zPsi, List.mem_append]
  exact Or.inl (Or.inl (Or.inl hβ))

theorem mem_zPsi_of_mem_zHigh {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ zHigh) : β ∈ zPsi := by
  simp only [zPsi, zHigh, List.mem_append] at hβ ⊢
  rcases hβ with h | h
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)

theorem mem_zPsi_of_mem_zLow {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ zLow) : β ∈ zPsi := by
  simp only [zPsi, List.mem_append]
  exact Or.inr hβ

theorem mem_zPsi_of_mem_zTop {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ zTop) : β ∈ zPsi := by
  simp only [zPsi, List.mem_append]
  exact Or.inl (Or.inr hβ)

theorem zPsi_complete_check : ∀ k < Tag.E6.rootCertificate.roots.length,
    2 ≤ Tag.E6.rootCertificate.root k 3 → Tag.E6.rootCertificate.root k ∈ zPsi := by
  decide +kernel

theorem mem_zPsi_of_level {ρ : Fin Tag.E6.rank → ℤ} (hρ : IsRoot .E6 ρ) (h : 2 ≤ ρ 3) :
    ρ ∈ zPsi := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E6) hρ
  exact zPsi_complete_check k hk h

theorem zPsi_add_check : ∀ β ∈ zPsi, ∀ β' ∈ zPsi, isRootB .E6 (β + β') = false := by
  decide +kernel

theorem zPsi_add_not_isRoot {β β' : Fin Tag.E6.rank → ℤ} (hβ : β ∈ zPsi) (hβ' : β' ∈ zPsi) :
    ¬IsRoot .E6 (β + β') := by
  rw [← isRootB_iff, zPsi_add_check β hβ β' hβ']
  exact Bool.false_ne_true

theorem ne_neg_of_mem_zPsi {β β' : Fin Tag.E6.rank → ℤ} (hβ : β ∈ zPsi) (hβ' : β' ∈ zPsi) :
    β ≠ -β' := by
  intro h
  have h1 := (pos_of_mem_zPsi hβ).2
  have h2 := (pos_of_mem_zPsi hβ').2
  rw [h, height_neg] at h1
  omega

theorem zLow_check : ∀ ρ ∈ zFrame ++ zLow, ∀ β ∈ zPsi,
    isRootB .E6 (ρ - β) = true → 0 < height (ρ - β) → β ∈ zLow := by
  decide +kernel

theorem zLow_closed {ρ β α : Fin Tag.E6.rank → ℤ} (hρ : ρ ∈ zFrame ∨ ρ ∈ zLow) (hβ : β ∈ zPsi)
    (hα : IsRoot .E6 α ∧ 0 < height α) (h : α + β = ρ) : β ∈ zLow := by
  have e : ρ - β = α := by rw [← h]; abel
  refine zLow_check ρ (List.mem_append.2 hρ) β hβ ?_ ?_
  · rw [e]
    exact isRootB_iff.2 hα.1
  · rw [e]
    exact hα.2

theorem zHigh_check : ∀ ρ ∈ zFrame ++ zHigh, ∀ β ∈ zPsi,
    isRootB .E6 (β - ρ) = true → (β - ρ) 3 = 0 → 0 < height (β - ρ) → β ∈ zHigh := by
  decide +kernel

theorem zHigh_closed {ρ β α : Fin Tag.E6.rank → ℤ} (hρ : ρ ∈ zFrame ∨ ρ ∈ zHigh) (hβ : β ∈ zPsi)
    (hα : IsRoot .E6 α ∧ 0 < height α) (hα3 : α 3 = 0) (h : -α + β = ρ) : β ∈ zHigh := by
  have e : β - ρ = α := by rw [← h]; abel
  refine zHigh_check ρ (List.mem_append.2 hρ) β hβ ?_ ?_ ?_
  · rw [e]
    exact isRootB_iff.2 hα.1
  · rw [e]
    exact hα3
  · rw [e]
    exact hα.2

theorem zTriple_check : ∀ a ∈ zFrame ++ zHigh, ∀ b ∈ zFrame ++ zHigh, ∀ c ∈ zFrame ++ zHigh,
    iform a b = 0 → iform a c = 0 → iform b c = 0 → a ≠ b → a ≠ c → b ≠ c →
      a ∈ zFrame ∧ b ∈ zFrame ∧ c ∈ zFrame := by
  decide +kernel

theorem zFrame_iform : iform zγ zδ = 0 ∧ iform zγ zε = 0 ∧ iform zδ zε = 0 := by
  decide +kernel

theorem zFrame_ne : zγ ≠ zδ ∧ zγ ≠ zε ∧ zδ ≠ zε := by
  decide +kernel

theorem zFrame_sum : zγ + zδ + zε = zOmega := by
  decide +kernel

theorem mem_zFrame {β : Fin Tag.E6.rank → ℤ} : β ∈ zFrame ↔ β = zγ ∨ β = zδ ∨ β = zε := by
  simp [zFrame]

theorem iform_zOmega_single (j : Fin Tag.E6.rank) :
    iform zOmega (Pi.single j 1) = if j = 3 then 1 else 0 := by
  revert j
  decide +kernel

theorem iform_zOmega (v : Fin Tag.E6.rank → ℤ) : iform zOmega v = v 3 := by
  rw [F4Pilot.iform_eq_sum_mul_iform_single]
  simp only [iform_zOmega_single, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem smul_mem_zFrame_of_mem_zFrameHigh {w : WeylGroup .E6}
    (h : ∀ β ∈ zFrame, w • β ∈ zFrame ∨ w • β ∈ zHigh) :
    ∀ β ∈ zFrame, w • β ∈ zFrame := by
  have hmem' : ∀ β ∈ zFrame, w • β ∈ zFrame ++ zHigh := fun β hβ =>
    List.mem_append.2 (h β hβ)
  obtain ⟨h1, h2, h3⟩ := zTriple_check (w • zγ) (hmem' zγ (mem_zFrame.2 (Or.inl rfl)))
    (w • zδ) (hmem' zδ (mem_zFrame.2 (Or.inr (Or.inl rfl))))
    (w • zε) (hmem' zε (mem_zFrame.2 (Or.inr (Or.inr rfl))))
    (by rw [iform_smul]; exact zFrame_iform.1) (by rw [iform_smul]; exact zFrame_iform.2.1)
    (by rw [iform_smul]; exact zFrame_iform.2.2)
    (fun e => zFrame_ne.1 (smul_left_cancel w e)) (fun e => zFrame_ne.2.1 (smul_left_cancel w e))
    (fun e => zFrame_ne.2.2 (smul_left_cancel w e))
  intro β hβ
  rcases mem_zFrame.1 hβ with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem smul_zOmega_of_smul_mem_zFrame {w : WeylGroup .E6}
    (h : ∀ β ∈ zFrame, w • β ∈ zFrame) : w • zOmega = zOmega := by
  have hγ := mem_zFrame.1 (h zγ (mem_zFrame.2 (Or.inl rfl)))
  have hδ := mem_zFrame.1 (h zδ (mem_zFrame.2 (Or.inr (Or.inl rfl))))
  have hε := mem_zFrame.1 (h zε (mem_zFrame.2 (Or.inr (Or.inr rfl))))
  have hne : w • zγ ≠ w • zδ ∧ w • zγ ≠ w • zε ∧ w • zδ ≠ w • zε :=
    ⟨fun e => zFrame_ne.1 (smul_left_cancel w e), fun e => zFrame_ne.2.1 (smul_left_cancel w e),
      fun e => zFrame_ne.2.2 (smul_left_cancel w e)⟩
  rw [← zFrame_sum, smul_add, smul_add]
  rcases hγ with h1 | h1 | h1 <;> rcases hδ with h2 | h2 | h2 <;> rcases hε with h3 | h3 | h3 <;>
    first
    | (exfalso; exact hne.1 (h1.trans h2.symm))
    | (exfalso; exact hne.2.1 (h1.trans h3.symm))
    | (exfalso; exact hne.2.2 (h2.trans h3.symm))
    | (rw [h1, h2, h3]; try abel)

theorem mem_parabolicWeylGroup_of_smul_zOmega {w : WeylGroup .E6} (h : w • zOmega = zOmega) :
    w ∈ parabolicWeylGroup .E6 zNodes := by
  have hinv : w⁻¹ • zOmega = zOmega := by
    rw [← h, inv_smul_smul, h]
  have hmem : w ∈ (parabolicWeylGroup .E6 zNodes : Set (WeylGroup .E6)) := by
    rw [(parabolic_Weyl_coordinate_stabilizer .E6 zNodes).1]
    intro v i hi
    have hi3 : i = 3 := by simpa [zNodes] using hi
    subst hi3
    rw [← iform_zOmega (w • v), ← iform_zOmega v, ← iform_smul w⁻¹, inv_smul_smul, hinv]
  exact hmem

theorem mem_parabolicWeylGroup_of_smul_zFrame {w : WeylGroup .E6}
    (h : ∀ β ∈ zFrame, w • β ∈ zFrame ∨ w • β ∈ zHigh) :
    w ∈ parabolicWeylGroup .E6 zNodes ∧ ∀ β ∈ zFrame, w • β ∈ zFrame :=
  ⟨mem_parabolicWeylGroup_of_smul_zOmega
    (smul_zOmega_of_smul_mem_zFrame (smul_mem_zFrame_of_mem_zFrameHigh h)),
    smul_mem_zFrame_of_mem_zFrameHigh h⟩

end CFSG.SeitzReduction.E6Pilot
