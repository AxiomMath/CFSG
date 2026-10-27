module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ScalarTorus
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcConn
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Data
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux3

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open CFSG.ClassicalInvolution.ModelFacts.Levi

set_option linter.unusedSectionVars false


section MonoGroup

variable {L : Type} [Field L]

theorem Mono.mul {n₁ n₂ : ModGL Tag.E8 L} {w₁ w₂ : WeylGroup Tag.E8}
    {s₁ s₂ : (Fin Tag.E8.rank → ℤ) → L} (h₁ : Mono n₁ w₁ s₁) (h₂ : Mono n₂ w₂ s₂) :
    Mono (n₁ * n₂) (w₁ * w₂) (fun β => s₁ (w₂ • β) * s₂ β) := by
  intro β hβ
  obtain ⟨hs₂, hc₂⟩ := h₂ β hβ
  obtain ⟨hs₁, hc₁⟩ := h₁ (w₂ • β) (IsRoot.smul hβ w₂)
  refine ⟨?_, fun c => ?_⟩
  · calc s₁ (w₂ • β) * s₂ β * (s₁ (w₂ • β) * s₂ β)
        = (s₁ (w₂ • β) * s₁ (w₂ • β)) * (s₂ β * s₂ β) := by ring
      _ = 1 := by rw [hs₁, hs₂, one_mul]
  · have e : n₁ * n₂ * pinnedX Tag.E8 L β c * (n₁ * n₂)⁻¹ =
        n₁ * (n₂ * pinnedX Tag.E8 L β c * n₂⁻¹) * n₁⁻¹ := by group
    rw [e, hc₂ c, hc₁ (s₂ β * c), mul_smul, mul_assoc]

theorem Mono.inv {n : ModGL Tag.E8 L} {w : WeylGroup Tag.E8} {s : (Fin Tag.E8.rank → ℤ) → L}
    (h : Mono n w s) : Mono n⁻¹ w⁻¹ (fun β => s (w⁻¹ • β)) := by
  intro β hβ
  have hβ' : IsRoot Tag.E8 (w⁻¹ • β) := IsRoot.smul hβ w⁻¹
  obtain ⟨hs, hc⟩ := h (w⁻¹ • β) hβ'
  refine ⟨hs, fun c => ?_⟩
  have h1 := hc (s (w⁻¹ • β) * c)
  rw [smul_inv_smul, ← mul_assoc, hs, one_mul] at h1
  have : n⁻¹ * pinnedX Tag.E8 L β c * n⁻¹⁻¹ =
      n⁻¹ * (n * pinnedX Tag.E8 L (w⁻¹ • β) (s (w⁻¹ • β) * c) * n⁻¹) * n⁻¹⁻¹ := by
    rw [h1]
  rw [this]
  group

end MonoGroup

section Torus

variable {L : Type} [Field L]

theorem rootTorusSL2_eq_thetaDiag {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β) (c : Lˣ) :
    rootTorusSL2 Tag.E8 L β c = rootDiagUnit Tag.E8 (thetaDiag β c) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport Tag.E8 L hβ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single Tag.E8 i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit Tag.E8 a : ModGL Tag.E8 L) : Module.End L (RootModule Tag.E8 L))
      (rootVec Tag.E8 L (Pi.single i 1))) = ((a i : Lˣ) : L) • rootVec Tag.E8 L (Pi.single i 1) := by
    change rootDiag a (rootVec Tag.E8 L (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin (Tag.rank Tag.E8) → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single Tag.E8 i), hs]
  rw [h2] at h1
  have hne : rootVec Tag.E8 L (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single Tag.E8 i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective L hne h1
  have h4 : 2 * iform β (Pi.single i 1) / iform β β = iform β (Pi.single i 1) := by
    rw [iform_self_isRoot_E8 hβ]
    omega
  rw [h4] at h3
  exact Units.ext h3

@[expose] def scalSub (g : ModGL Tag.E8 L) (c : L) : Subgroup (ModGL Tag.E8 L) where
  carrier := {q | q ∈ Qθ Tag.E8 L ∧ g * q * g⁻¹ ∈ Qθ Tag.E8 L ∧
    heisCoord Tag.E8 L (g * q * g⁻¹) = c • heisCoord Tag.E8 L q}
  mul_mem' := by
    rintro q q' ⟨hq, hcq, hqe⟩ ⟨hq', hcq', hq'e⟩
    have e : g * (q * q') * g⁻¹ = (g * q * g⁻¹) * (g * q' * g⁻¹) := by group
    refine ⟨mul_mem hq hq', ?_, ?_⟩
    · rw [e]
      exact mul_mem hcq hcq'
    · rw [e, (heisCoord_spec Tag.E8 L).mul _ hcq _ hcq', hqe, hq'e,
        (heisCoord_spec Tag.E8 L).mul _ hq _ hq', smul_add]
  one_mem' := by
    refine ⟨one_mem _, ?_, ?_⟩
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [mul_one, mul_inv_cancel, heisCoord_one, smul_zero]
  inv_mem' := by
    rintro q ⟨hq, hcq, hqe⟩
    have e : g * q⁻¹ * g⁻¹ = (g * q * g⁻¹)⁻¹ := by group
    refine ⟨inv_mem hq, ?_, ?_⟩
    · rw [e]
      exact inv_mem hcq
    · rw [e, heisCoord_inv hcq, hqe, heisCoord_inv hq, smul_neg]

theorem Qθ_le_scalSub {g : ModGL Tag.E8 L} {c : L}
    (h₁ : ∀ α ∈ Deg1 Tag.E8, ∀ z : L, g * pinnedX Tag.E8 L α z * g⁻¹ = pinnedX Tag.E8 L α (c * z))
    (h₂ : ∀ z : L, g * pinnedX Tag.E8 L (highRoot Tag.E8) z * g⁻¹ =
      pinnedX Tag.E8 L (highRoot Tag.E8) (c ^ 2 * z)) : Qθ Tag.E8 L ≤ scalSub g c := by
  have hQ : ∀ α ∈ Deg1 Tag.E8, ∀ w : L, pinnedX Tag.E8 L α w ∈ Qθ Tag.E8 L :=
    fun α hα w => pinnedX_mem_Qθ_of_mem_Deg1 hα w
  refine Qθ_le_of_gen (fun α hα z => ?_) (fun z => ?_)
  · refine ⟨hQ α hα z, ?_, ?_⟩
    · rw [h₁ α hα z]
      exact hQ α hα _
    · rw [h₁ α hα z, (heisCoord_spec _ L).pinnedX_deg1 α hα,
        (heisCoord_spec _ L).pinnedX_deg1 α hα]
      funext β
      by_cases hβ : β = α
      · subst hβ
        simp
      · simp [Pi.single_apply, hβ]
  · refine ⟨pinnedX_highRoot_mem_Qθ z, ?_, ?_⟩
    · rw [h₂ z]
      exact pinnedX_highRoot_mem_Qθ _
    · rw [h₂ z, (heisCoord_spec _ L).pinnedX_highRoot, (heisCoord_spec _ L).pinnedX_highRoot,
        smul_zero]

@[expose] def dθ (a : Lˣ) : ModGL Tag.E8 L := rootTorusSL2 Tag.E8 L (highRoot Tag.E8) a

theorem dθ_mem (a : Lˣ) : dθ a ∈ Heis.Uθ Tag.E8 L ⊔ Heis.Uneg Tag.E8 L := by
  obtain ⟨hL, -⟩ := exceptional_Lang_root_rank_one_torus_transport Tag.E8 L (isRoot_highRoot Tag.E8)
  have hmem : rootTorusSL2 Tag.E8 L (highRoot Tag.E8) a ∈ rootRankOneGroup Tag.E8 L (highRoot Tag.E8) :=
    ⟨HSL a, rfl⟩
  rw [hL] at hmem
  exact hmem

theorem dθ_mem_adj (a : Lˣ) : dθ a ∈ adjointGroup Tag.E8 L := by
  have := dθ_mem a
  exact sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _) this

theorem dθ_eq (a : Lˣ) :
    dθ a = rootDiagUnit Tag.E8 (thetaDiag (highRoot Tag.E8) a) :=
  rootTorusSL2_eq_thetaDiag (isRoot_highRoot Tag.E8) a

theorem iform_highRoot_deg1 {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ Deg1 Tag.E8) :
    iform (highRoot Tag.E8) α = 1 := by
  have h := ScalarTorusAux.exponent_of_Deg1 hα
  rwa [iform_self_isRoot_E8 (isRoot_highRoot Tag.E8), show 2 * iform (highRoot Tag.E8) α / 2 =
    iform (highRoot Tag.E8) α by omega] at h

theorem dθ_scal (a : Lˣ) {q : ModGL Tag.E8 L} (hq : q ∈ Qθ Tag.E8 L) :
    dθ a * q * (dθ a)⁻¹ ∈ Qθ Tag.E8 L ∧
      heisCoord Tag.E8 L (dθ a * q * (dθ a)⁻¹) = (a : L) • heisCoord Tag.E8 L q := by
  have hle : Qθ Tag.E8 L ≤ scalSub (dθ a) (a : L) := by
    refine Qθ_le_scalSub (fun α hα z => ?_) (fun z => ?_)
    · rw [dθ_eq, rootDiagUnit_conj_pinnedX _ (CoordAux.mem_Deg1.1 hα).1, rootChar_thetaDiag,
        iform_highRoot_deg1 hα, zpow_one]
    · rw [dθ_eq, rootDiagUnit_conj_pinnedX _ (isRoot_highRoot Tag.E8), rootChar_thetaDiag,
        iform_self_isRoot_E8 (isRoot_highRoot Tag.E8)]
      simp [zpow_two, sq]
  exact (hle hq).2

end Torus

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
