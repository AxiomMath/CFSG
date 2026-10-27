module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux14
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Coords

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8 CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false


theorem caseA_extra : dA0 ≠ -dA1 ∧ dA0 ≠ 0 ∧ dA1 ≠ 0 := by decide +kernel

theorem caseB_extra : dB0 ≠ -dB1 ∧ dB0 ≠ 0 ∧ dB1 ≠ 0 := by decide +kernel

@[expose] def stepA : StepData 1 2 where
  β₀ := bA0
  β₁ := bA1
  u₀ := uA0
  u₁ := uA1
  δ₀ := dA0
  δ₁ := dA1
  v₀ := vA0
  v₁ := vA1
  μ₀ := mA0
  hβ₀ := caseA_beta.1
  hβ₁ := caseA_beta.2.1
  hcβ₀ := by have := caseA_beta.2.2.1; omega
  hcβ₁ := by have := caseA_beta.2.2.2.1; omega
  hwβ₀ := caseA_beta.2.2.2.2.1
  hwβ₁ := caseA_beta.2.2.2.2.2.1
  hβne := caseA_beta.2.2.2.2.2.2.1
  hβsum := caseA_beta.2.2.2.2.2.2.2
  hu₀ := caseA_u.1
  hu₁ := caseA_u.2.1
  hcu₀ := by have := caseA_u.2.2.1; omega
  hcu₁ := by have := caseA_u.2.2.2.1; omega
  hνu₀ := caseA_u.2.2.2.2.1
  hνu₁ := caseA_u.2.2.2.2.2.1
  hune := caseA_u.2.2.2.2.2.2
  hδ₀ := caseA_delta.1
  hδ₀7 := caseA_delta.2.1
  hδ₁ := caseA_delta.2.2.1
  hδ₁7 := caseA_delta.2.2.2.1
  hwδ₀ := caseA_delta.2.2.2.2.1
  hwδ₁ := caseA_delta.2.2.2.2.2.1
  hδne := caseA_delta.2.2.2.2.2.2.1
  hδneg := caseA_extra.1
  hδsum := caseA_delta.2.2.2.2.2.2.2
  hδ0 := caseA_extra.2.1
  hδ1 := caseA_extra.2.2
  hv₀ := caseA_v.1
  hv₁ := caseA_v.2.1
  hcv₀ := by have := caseA_v.2.2.1; omega
  hcv₁ := by have := caseA_v.2.2.2.1; omega
  hνv₀ := caseA_v.2.2.2.2.1
  hνv₁ := caseA_v.2.2.2.2.2.1
  hvne := caseA_v.2.2.2.2.2.2
  hμ₀ := caseA_mu.1
  hcμ₀ := by have := caseA_mu.2.1; omega
  hμδ := caseA_mu.2.2.1
  hμδm := caseA_mu.2.2.2.1
  hcμδ := by have := caseA_mu.2.2.2.2; omega

@[expose] def stepB : StepData 2 1 where
  β₀ := bB0
  β₁ := bB1
  u₀ := uB0
  u₁ := uB1
  δ₀ := dB0
  δ₁ := dB1
  v₀ := vB0
  v₁ := vB1
  μ₀ := mB0
  hβ₀ := caseB_beta.1
  hβ₁ := caseB_beta.2.1
  hcβ₀ := by have := caseB_beta.2.2.1; omega
  hcβ₁ := by have := caseB_beta.2.2.2.1; omega
  hwβ₀ := caseB_beta.2.2.2.2.1
  hwβ₁ := caseB_beta.2.2.2.2.2.1
  hβne := caseB_beta.2.2.2.2.2.2.1
  hβsum := caseB_beta.2.2.2.2.2.2.2
  hu₀ := caseB_u.1
  hu₁ := caseB_u.2.1
  hcu₀ := by have := caseB_u.2.2.1; omega
  hcu₁ := by have := caseB_u.2.2.2.1; omega
  hνu₀ := caseB_u.2.2.2.2.1
  hνu₁ := caseB_u.2.2.2.2.2.1
  hune := caseB_u.2.2.2.2.2.2
  hδ₀ := caseB_delta.1
  hδ₀7 := caseB_delta.2.1
  hδ₁ := caseB_delta.2.2.1
  hδ₁7 := caseB_delta.2.2.2.1
  hwδ₀ := caseB_delta.2.2.2.2.1
  hwδ₁ := caseB_delta.2.2.2.2.2.1
  hδne := caseB_delta.2.2.2.2.2.2.1
  hδneg := caseB_extra.1
  hδsum := caseB_delta.2.2.2.2.2.2.2
  hδ0 := caseB_extra.2.1
  hδ1 := caseB_extra.2.2
  hv₀ := caseB_v.1
  hv₁ := caseB_v.2.1
  hcv₀ := by have := caseB_v.2.2.1; omega
  hcv₁ := by have := caseB_v.2.2.2.1; omega
  hνv₀ := caseB_v.2.2.2.2.1
  hνv₁ := caseB_v.2.2.2.2.2.1
  hvne := caseB_v.2.2.2.2.2.2
  hμ₀ := caseB_mu.1
  hcμ₀ := by have := caseB_mu.2.1; omega
  hμδ := caseB_mu.2.2.1
  hμδm := caseB_mu.2.2.2.1
  hcμδ := by have := caseB_mu.2.2.2.2; omega

theorem sRoots1_S₁ : ∀ β ∈ sRoots1, β ∈ rootFinset Tag.E8 ∧ ∀ α ∈ rootFinset Tag.E8,
    (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → α i = 0) → iform β α = 0 := by
  decide +kernel

theorem mem_S₁_of_sRoots {β : Fin Tag.E8.rank → ℤ} (h : β ∈ sRoots1) : β ∈ TwClass.e8Ten.S₁ :=
  ⟨mem_rootFinset.1 (sRoots1_S₁ β h).1, fun α hα =>
    (sRoots1_S₁ β h).2 α (mem_rootFinset.2 hα.1) hα.2⟩

theorem deg1_cases {β : Fin Tag.E8.rank → ℤ} (h : β ∈ deg1Roots) : β ∈ mRoots ∨ β ∈ sRoots1 := by
  obtain ⟨hr, h7⟩ := mem_deg1Roots.1 h
  by_cases h5 : β 4 % 5 = 0
  · exact Or.inr (mem_sRoots1.2 ⟨hr, h7, h5⟩)
  · exact Or.inl (mem_mRoots.2 ⟨hr, h7, h5⟩)

section Main

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)
  (H : Subgroup (ModGL Tag.E8 K))

theorem exists_Mcoord
    (hm : ∃ m ∈ H, m ∈ Qθ Tag.E8 K ∧
      heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D)) :
    ∃ μ ∈ mRoots, ∃ u ∈ Uspace D.g H, u μ ≠ 0 := by
  obtain ⟨m, hmH, hmQ, hmS⟩ := hm
  by_contra hno
  push Not at hno
  apply hmS
  have hmQ' : m ∈ Qθ TwClass.e8Ten.tag K := hmQ
  have hmQrat : m ∈ Qrat (K := K) D.g := CoordsAux.Ψ_Qθ D hmQ'
  have hCU : Cc D.g m ∈ Uspace D.g H := Cc_mem_Uspace hmH hmQrat
  have hX₁ : m ∈ TwClass.e8Ten.X₁ D := by
    refine CoordsAux.mem_X₁_of_support TwClass.e8Ten D hmQ' (fun β hβ => ?_)
    have hβD : β ∈ Deg1 TwClass.e8Ten.tag := by
      by_contra hn
      exact hβ (CoordsAux.κ_support D hmQ' hn)
    refine ⟨hβD, ?_⟩
    have hβ' : β ∈ deg1Roots :=
      mem_deg1Roots.2 ⟨(CoordAux.mem_Deg1.1 hβD).1, (CoordAux.mem_Deg1.1 hβD).2⟩
    rcases deg1_cases hβ' with hM | hS
    · exact absurd (hno β hM _ hCU) hβ
    · exact mem_S₁_of_sRoots hS
  have hX : m ∈ TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D := Subgroup.mem_sup_left hX₁
  exact Submodule.subset_span ⟨m, ⟨hX, hmQ⟩, rfl⟩

variable [IsAlgClosed D.L]

theorem allM_mem_Uspace (hHG : H ≤ adjointGroup Tag.E8 K)
    (hXH : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ H)
    (hm : ∃ m ∈ H, m ∈ Qθ Tag.E8 K ∧
      heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D)) :
    ∀ ν ∈ mRoots, (Pi.single ν (1 : D.L) : Fn D.L) ∈ Uspace D.g H := by
  have h1 : D.frame TwClass.e8Ten.S₁ ≤ H := le_sup_left.trans hXH
  have h2 : D.frame TwClass.e8Ten.S₂ ≤ H := le_sup_right.trans hXH
  obtain ⟨μ, hμ, u, hu, h0⟩ := exists_Mcoord D H hm
  have hblock := block_e8Ten D H h1 h2 hu hμ h0
  intro ν hν
  rcases mRoots_cls μ hμ with hc | hc | hc | hc
  ·
    have hP : ∀ ν ∈ mRoots, (cls ν = 1 ∨ cls ν = 5 - 1) →
        (Pi.single ν (1 : D.L) : Fn D.L) ∈ Uspace D.g H := fun ν hν hc' =>
      hblock ν hν (by omega)
    have hQ := second_step D H hHG h1 h2 stepA hP
    rcases mRoots_cls ν hν with hcν | hcν | hcν | hcν
    · exact hP ν hν (by omega)
    · exact hQ ν hν (by omega)
    · exact hQ ν hν (by omega)
    · exact hP ν hν (by omega)
  ·
    have hP : ∀ ν ∈ mRoots, (cls ν = 2 ∨ cls ν = 5 - 2) →
        (Pi.single ν (1 : D.L) : Fn D.L) ∈ Uspace D.g H := fun ν hν hc' =>
      hblock ν hν (by omega)
    have hQ := second_step D H hHG h1 h2 stepB hP
    rcases mRoots_cls ν hν with hcν | hcν | hcν | hcν
    · exact hQ ν hν (by omega)
    · exact hP ν hν (by omega)
    · exact hP ν hν (by omega)
    · exact hQ ν hν (by omega)
  ·
    have hP : ∀ ν ∈ mRoots, (cls ν = 2 ∨ cls ν = 5 - 2) →
        (Pi.single ν (1 : D.L) : Fn D.L) ∈ Uspace D.g H := fun ν hν hc' =>
      hblock ν hν (by omega)
    have hQ := second_step D H hHG h1 h2 stepB hP
    rcases mRoots_cls ν hν with hcν | hcν | hcν | hcν
    · exact hQ ν hν (by omega)
    · exact hP ν hν (by omega)
    · exact hP ν hν (by omega)
    · exact hQ ν hν (by omega)
  ·
    have hP : ∀ ν ∈ mRoots, (cls ν = 1 ∨ cls ν = 5 - 1) →
        (Pi.single ν (1 : D.L) : Fn D.L) ∈ Uspace D.g H := fun ν hν hc' =>
      hblock ν hν (by omega)
    have hQ := second_step D H hHG h1 h2 stepA hP
    rcases mRoots_cls ν hν with hcν | hcν | hcν | hcν
    · exact hP ν hν (by omega)
    · exact hQ ν hν (by omega)
    · exact hQ ν hν (by omega)
    · exact hP ν hν (by omega)

theorem mem_of_supp_mRoots {L : Type} [Field L] {U : Submodule L (Fn L)} {c : Fn L}
    (hc : ∀ β, c β ≠ 0 → β ∈ mRoots)
    (hall : ∀ ν ∈ mRoots, (Pi.single ν (1 : L) : Fn L) ∈ U) : c ∈ U := by
  classical
  have : c = ∑ ν ∈ mRoots, c ν • (Pi.single ν (1 : L) : Fn L) := by
    funext β
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
    by_cases hβ : β ∈ mRoots
    · rw [Finset.sum_eq_single β]
      · simp
      · intro ν _ hν
        simp [Ne.symm hν]
      · intro h
        exact absurd hβ h
    · rw [Finset.sum_eq_zero]
      · by_contra hne
        exact hβ (hc β hne)
      · intro ν hν
        have : β ≠ ν := fun h => hβ (h ▸ hν)
        simp [this]
  rw [this]
  exact Submodule.sum_mem _ fun ν hν => U.smul_mem _ (hall ν hν)

open Classical in
theorem split_mem (c : TwClass) {K : Type} [Field K] [Finite K] (D : LangLevi c.tag K c.w)
    {q qS qM : ModGL c.tag K} (hq : q ∈ Qθ c.tag K) (hqS : qS ∈ Qθ c.tag K)
    (hqM : qM ∈ Qθ c.tag K)
    (hκS : CoordsAux.κ D qS =
      fun β => if β ∈ CoordsAux.Bset c then CoordsAux.κ D q β else 0)
    (hκM : CoordsAux.κ D qM =
      fun β => if β ∈ CoordsAux.Bset c then 0 else CoordsAux.κ D q β) :
    q * (qS * qM)⁻¹ ∈ Uθ c.tag K := by
  classical
  have hSM : qS * qM ∈ Qθ c.tag K := mul_mem hqS hqM
  have hsum : CoordsAux.κ D (q * (qS * qM)⁻¹) = 0 := by
    rw [CoordsAux.κ_mul D hq (inv_mem hSM), TwCoordsAux.κ_inv c D hSM,
      CoordsAux.κ_mul D hqS hqM, hκS, hκM]
    funext β
    by_cases hB : β ∈ CoordsAux.Bset c <;> simp [hB]
  exact (CoordsAux.κ_eq_zero_iff D (mul_mem hq (inv_mem hSM))).1 hsum

theorem Qθ_le_of_Melement (hHG : H ≤ adjointGroup Tag.E8 K)
    (hXH : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ H)
    (hm : ∃ m ∈ H, m ∈ Qθ Tag.E8 K ∧
      heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D)) :
    Qθ Tag.E8 K ≤ H := by
  classical
  have hall := allM_mem_Uspace D H hHG hXH hm
  have h1 : D.frame TwClass.e8Ten.S₁ ≤ H := le_sup_left.trans hXH
  have hscal1 := scalClosed₁ D H h1
  have hker1 := hker₁ D H h1
  have hw : TwClass.e8Ten.w • highRoot TwClass.e8Ten.tag = highRoot TwClass.e8Ten.tag :=
    CoordsAux.w_smul_highRoot TwClass.e8Ten
  obtain ⟨ε, -, hε⟩ := CoordsAux.exists_monomial (τ := TwClass.e8Ten.tag) (F := D.L) hw
  have hε' : CoordsAux.MonomialProp TwClass.e8Ten.w ε := hε
  intro q hq
  have hq' : q ∈ Qθ TwClass.e8Ten.tag K := hq
  have hsig := CoordsAux.κ_isSig D hw hε' hq'
  obtain ⟨qS, hqS, hκS⟩ : ∃ qS : ModGL Tag.E8 K, qS ∈ Qθ TwClass.e8Ten.tag K ∧
      CoordsAux.κ D qS =
        fun β => if β ∈ CoordsAux.Bset TwClass.e8Ten then CoordsAux.κ D q β else 0 :=
    CoordsAux.exists_lift D hw hε' (TwCoordsAux.isSig_pB TwClass.e8Ten D hsig)
  obtain ⟨qM, hqM, hκM⟩ : ∃ qM : ModGL Tag.E8 K, qM ∈ Qθ TwClass.e8Ten.tag K ∧
      CoordsAux.κ D qM =
        fun β => if β ∈ CoordsAux.Bset TwClass.e8Ten then 0 else CoordsAux.κ D q β :=
    CoordsAux.exists_lift D hw hε' (TwCoordsAux.isSig_pM TwClass.e8Ten D hsig)
  have hqSX : qS ∈ TwClass.e8Ten.X₁ D :=
    CoordsAux.mem_X₁_of_support TwClass.e8Ten D hqS fun β hβ => by
      by_contra hB
      apply hβ
      rw [hκS]
      simp [hB]
  have hqSH : qS ∈ H := h1 hqSX
  have hqMQ : qM ∈ Qrat (K := K) D.g := CoordsAux.Ψ_Qθ D hqM
  have hqMA : qM ∈ adjointGroup Tag.E8 K := Qθ_le_adjointGroup Tag.E8 K hqM
  have hκMU : Cc D.g qM ∈ Uspace D.g H := by
    refine mem_of_supp_mRoots (fun β hβ => ?_) hall
    have hβ' : CoordsAux.κ D qM β ≠ 0 := hβ
    rw [hκM] at hβ'
    dsimp only at hβ'
    split_ifs at hβ' with hB
    · exact absurd rfl hβ'
    · have hβD : β ∈ Deg1 TwClass.e8Ten.tag := by
        by_contra hn
        exact hβ' (CoordsAux.κ_support D hq' hn)
      have hβ'' : β ∈ deg1Roots :=
        mem_deg1Roots.2 ⟨(CoordAux.mem_Deg1.1 hβD).1, (CoordAux.mem_Deg1.1 hβD).2⟩
      rcases deg1_cases hβ'' with hM | hS
      · exact hM
      · exact absurd ⟨hβD, mem_S₁_of_sRoots hS⟩ hB
  have hqMH : qM ∈ H := (toSetup D H).mem_H_of_Uspace hscal1 hHG hker1 hqMQ hqMA hκMU
  have hSM : qS * qM ∈ Qθ TwClass.e8Ten.tag K := mul_mem hqS hqM
  have hU : q * (qS * qM)⁻¹ ∈ Uθ TwClass.e8Ten.tag K :=
    split_mem TwClass.e8Ten D hq' hqS hqM hκS hκM
  have hUH : q * (qS * qM)⁻¹ ∈ H := h1 (TwCoordsAux.Uθ_le_X₁ TwClass.e8Ten D hU)
  have e : q = (q * (qS * qM)⁻¹) * qS * qM := by group
  rw [e]
  exact mul_mem (mul_mem hUH hqSH) hqMH

end Main

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
