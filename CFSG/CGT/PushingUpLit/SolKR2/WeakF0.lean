module

public import CFSG.CGT.PushingUpLit.SolKR2.WeakF0Core
public import CFSG.CGT.PushingUpLit.SolKR2.WeakNames
import CFSG.CGT.PushingUpLit.SolKR2.Pair
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen
public import CFSG.CGT.PushingUpLit.SolKR2.WeakDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.RankThree.GF2n.Tim78S31
import CFSG.Timmesfeld.Moufang.Three
import CFSG.Timmesfeld.RankOne
import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup IsTI BenderCenterInput
  UnitaryTwoGenerationInput)
open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)
open CFSG.CGT.T75N (benderCenterInput unitaryTwoGenerationInput)

section Names

variable {G : Type} [Group G] {M B : Subgroup G}

theorem omega_conj_sD1 (h : R2 M B) (g m : G) :
    omegaOneSub (conjSubgroup (m * g⁻¹) (sD1 B g)) = sA0 B m := by
  show omegaOneSub (conjSubgroup (m * g⁻¹) (conjSubgroup g (omegaTwoSub B))) =
    conjSubgroup m (omegaOneSub B)
  rw [← conjSubgroup_mul, inv_mul_cancel_right, Pair.omegaOne_conj_U h m]

theorem sS_eq (h : R2 M B) (g m x : G) : sS B g m x = dS (sD1 B g) (m * g⁻¹) x := by
  show dS2 (sD1 B g) x ⊓ Subgroup.centralizer (sA0 B m : Set G) =
    dS2 (sD1 B g) x ⊓ Subgroup.centralizer
      (omegaOneSub (conjSubgroup (m * g⁻¹) (sD1 B g)) : Set G)
  rw [omega_conj_sD1 h g m]

theorem sF0_eq (h : R2 M B) (g m x : G) : sF0 B g m x = dF0 (sD1 B g) (m * g⁻¹) x := by
  show (dX (sD1 B g) x ⊔ sA0 B m) ⊓ Subgroup.centralizer (dX (sD1 B g) x : Set G) =
    (dX (sD1 B g) x ⊔ omegaOneSub (conjSubgroup (m * g⁻¹) (sD1 B g))) ⊓
      Subgroup.centralizer (dX (sD1 B g) x : Set G)
  rw [omega_conj_sD1 h g m]

theorem sE_eq (h : R2 M B) (g m x : G) :
    sE B g m x = dS (sD1 B g) (m * g⁻¹) x ⊔ dF0 (sD1 B g) (m * g⁻¹) x := by
  show sS B g m x ⊔ sF0 B g m x = _
  rw [sS_eq h g m x, sF0_eq h g m x]

namespace R2StarData

variable {h : R2 M B} {g m α x : G} (d : R2StarData h g m α x)
include d

set_option linter.unusedSectionVars false in
theorem card_C1 : Nat.card ↥(sC1 B g x) = 16 := by
  show Nat.card ↥(conjSubgroup x (conjSubgroup g (omegaTwoSub B))) = 16
  rw [card_conjSubgroup]
  exact Pair.card_conj_U h g

set_option linter.unusedSectionVars false in
theorem card_C0 : Nat.card ↥(sC0 B g x) = 4 := by
  show Nat.card ↥(omegaOneSub (conjSubgroup x (conjSubgroup g (omegaTwoSub B)))) = 4
  rw [← conjSubgroup_mul, Pair.omegaOne_conj_U h (x * g)]
  exact Pair.card_conj_B0 h (x * g)

theorem exists_C1_not_C0 : ∃ c ∈ sC1 B g x, c ∉ sC0 B g x := exists_C_not_C0 d.data31

theorem A0_inf_X : ∀ a ∈ omegaOneSub (conjSubgroup (m * g⁻¹) (sD1 B g)),
    a ∈ dX (sD1 B g) x → a = 1 := by
  intro a ha haX
  rw [omega_conj_sD1 h g m] at ha
  exact d.inf_cent a ha (sup_le d.centr d.cent_C haX)

end R2StarData

end Names

section Certificates34

variable {G : Type} [Group G] [Finite G] {M B : Subgroup G}

namespace R2StarData

variable {h : R2 M B} {g m α x : G} (d : R2StarData h g m α x)
include d

theorem card_F0 : Nat.card ↥(sF0 B g m x) = 4 := by
  have h1 := Inner.card_dF0 d.data31 benderCenterInput unitaryTwoGenerationInput (A0_inf_X d)
  rw [sF0_eq h g m x]
  refine h1.trans ?_
  rw [omega_conj_sD1 h g m]
  exact Pair.card_conj_B0 h m

theorem isElemAbelian_F0 : CFSG.Open.IsElemAbelian 2 (sF0 B g m x) := by
  rw [sF0_eq h g m x]
  exact isElemAbelian_two
    (fun a ha b hb => Inner.dF0_comm d.data31 benderCenterInput unitaryTwoGenerationInput ha hb)
    (fun a ha => Inner.dF0_sq d.data31 benderCenterInput unitaryTwoGenerationInput ha)

theorem F0_inf_X : sF0 B g m x ⊓ sX B g x = ⊥ := by
  rw [sF0_eq h g m x]
  exact Inner.dF0_inf_dX d.data31 benderCenterInput unitaryTwoGenerationInput

theorem exists_mul_X_F0 : ∀ a ∈ sA0 B m, ∃ z ∈ sX B g x, ∃ f ∈ sF0 B g m x, a = z * f := by
  intro a ha
  rw [← omega_conj_sD1 h g m] at ha
  obtain ⟨s, hs, f, hf, hsf⟩ := Inner.exists_mul_S_dF0 d.data31 benderCenterInput
    unitaryTwoGenerationInput ha
  exact ⟨s, dS2_le_dX _ x (dS_le_dS2 _ _ x hs), f, by rw [sF0_eq h g m x]; exact hf, hsf⟩

theorem exists_mul_S_F0 : ∀ a ∈ sA0 B m, ∃ s ∈ sS B g m x, ∃ f ∈ sF0 B g m x, a = s * f := by
  intro a ha
  rw [← omega_conj_sD1 h g m] at ha
  obtain ⟨s, hs, f, hf, hsf⟩ := Inner.exists_mul_S_dF0 d.data31 benderCenterInput
    unitaryTwoGenerationInput ha
  exact ⟨s, by rw [sS_eq h g m x]; exact hs, f, by rw [sF0_eq h g m x]; exact hf, hsf⟩

theorem exists_A0_of_F0 : ∀ f ∈ sF0 B g m x, ∃ a ∈ sA0 B m, ∃ s ∈ sS B g m x, a = s * f := by
  intro f hf
  rw [sF0_eq h g m x] at hf
  obtain ⟨a, ha, s, hs, has⟩ := Inner.exists_A0_of_dF0 d.data31 benderCenterInput
    unitaryTwoGenerationInput hf
  refine ⟨a, ?_, s, ?_, has⟩
  · rw [← omega_conj_sD1 h g m]
    exact ha
  · rw [sS_eq h g m x]
    exact hs

theorem S_mul_F0 : ∀ s ∈ sS B g m x, ∀ f ∈ sF0 B g m x, s * f ∈ sA0 B m → s * f ≠ 1 →
    s ∉ sC0 B g x ∧ f ≠ 1 := by
  intro s hs f hf ha h1
  rw [sS_eq h g m x] at hs
  rw [sF0_eq h g m x] at hf
  rw [← omega_conj_sD1 h g m] at ha
  obtain ⟨hsN, hf1⟩ := Inner.S_mul_F0 d.data31 benderCenterInput unitaryTwoGenerationInput
    (A0_inf_X d) hs hf ha h1
  exact ⟨fun hs0 => hsN (Subgroup.mem_sup_right hs0), hf1⟩

theorem S_inf_F0 : sS B g m x ⊓ sF0 B g m x = ⊥ := by
  rw [sS_eq h g m x, sF0_eq h g m x]
  exact Inner.dS_inf_dF0 d.data31 benderCenterInput unitaryTwoGenerationInput

theorem isElemAbelian_S : CFSG.Open.IsElemAbelian 2 (sS B g m x) := by
  rw [sS_eq h g m x]
  exact isElemAbelian_two
    (fun a ha b hb => Inner.S_comm d.data31 benderCenterInput unitaryTwoGenerationInput ha hb)
    (fun a ha => Inner.S_sq d.data31 benderCenterInput unitaryTwoGenerationInput ha)

theorem card_S : Nat.card ↥(sS B g m x) = 16 := by
  rw [sS_eq h g m x]
  exact (Inner.card_dS d.data31 benderCenterInput unitaryTwoGenerationInput).trans (card_C1 d)

theorem S_inf_N : sS B g m x ⊓ sN B g x = sC0 B g x := by
  rw [sS_eq h g m x, inf_comm]
  exact Inner.inf_dN_dS d.data31 benderCenterInput unitaryTwoGenerationInput

theorem card_N : Nat.card ↥(sN B g x) = 16 := by
  have h1 : Nat.card ↥(sN B g x) =
      Nat.card ↥(omegaOneSub (sD1 B g)) * Nat.card ↥(sC0 B g x) :=
    Inner.card_dN d.data31 benderCenterInput unitaryTwoGenerationInput
  have h2 : Nat.card ↥(omegaOneSub (sD1 B g)) = 4 := by
    show Nat.card ↥(omegaOneSub (conjSubgroup g (omegaTwoSub B))) = 4
    rw [Pair.omegaOne_conj_U h g]
    exact Pair.card_conj_B0 h g
  rw [h1, h2, card_C0 d]

theorem card_S2 : Nat.card ↥(sS2 B g x) = 64 := by
  have h1 : Nat.card ↥(sS2 B g x) * Nat.card ↥(sC0 B g x) =
      Nat.card ↥(sN B g x) * Nat.card ↥(sC1 B g x) :=
    Inner.card_dS2 d.data31 benderCenterInput unitaryTwoGenerationInput
  rw [card_C0 d, card_N d, card_C1 d] at h1
  omega

theorem isElemAbelian_E : CFSG.Open.IsElemAbelian 2 (sE B g m x) := by
  rw [sE_eq h g m x]
  exact isElemAbelian_two
    (fun a ha b hb => Inner.dE_comm d.data31 benderCenterInput unitaryTwoGenerationInput ha hb)
    (fun a ha => Inner.dE_sq d.data31 benderCenterInput unitaryTwoGenerationInput ha)

theorem card_E : Nat.card ↥(sE B g m x) = 64 := by
  have h1 := Inner.card_dE d.data31 benderCenterInput unitaryTwoGenerationInput
  have h2 := card_S d
  have h3 := card_F0 d
  rw [sS_eq h g m x] at h2
  rw [sF0_eq h g m x] at h3
  rw [sE_eq h g m x, h1, h2, h3]

theorem comm_C1_E : ∀ c ∈ sC1 B g x, ∀ e ∈ sE B g m x, c * e * c⁻¹ * e⁻¹ ∈ sC0 B g x := by
  intro c hc e he
  rw [sE_eq h g m x] at he
  exact Inner.comm_C_E d.data31 benderCenterInput unitaryTwoGenerationInput hc he

theorem cent_E : ∀ c ∈ sC1 B g x, c ∉ sC0 B g x → ∀ e ∈ sE B g m x, c * e = e * c →
    e ∈ sV B g m x := by
  intro c hc hc0 e he hce
  rw [sE_eq h g m x] at he
  have key := Inner.cent_E d.data31 benderCenterInput unitaryTwoGenerationInput hc hc0 he hce
  show e ∈ sC0 B g x ⊔ sF0 B g m x
  rw [sF0_eq h g m x]
  exact key

theorem F0_faithful :
    ∀ f ∈ sF0 B g m x, f ∈ Subgroup.centralizer (omegaTwoSub B : Set G) → f = 1 := by
  intro f hf hfc
  rw [sF0_eq h g m x] at hf
  have hXZ : dX (sD1 B g) x ≤ Subgroup.centralizer (omegaTwoSub B : Set G) :=
    sup_le d.centr d.cent_C
  have hAZ : ∀ a ∈ omegaOneSub (conjSubgroup (m * g⁻¹) (sD1 B g)),
      a ∈ Subgroup.centralizer (omegaTwoSub B : Set G) → a = 1 := by
    intro a ha
    rw [omega_conj_sD1 h g m] at ha
    exact d.inf_cent a ha
  have key := Inner.dF0_inf_eq_bot d.data31 benderCenterInput unitaryTwoGenerationInput hXZ hAZ
  exact Subgroup.mem_bot.mp (key.le (Subgroup.mem_inf.mpr ⟨hf, hfc⟩))

end R2StarData

end Certificates34

end CFSG.CGT.PushingUpLit.SolKR2
