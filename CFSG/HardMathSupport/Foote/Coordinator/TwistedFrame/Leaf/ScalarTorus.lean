module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Coordinates
public import CFSG.LieType.Chevalley.LangRootRankOneTorus

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


namespace ScalarTorusAux

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {K : Type} [Field K]

theorem torus_conj_pinnedX {β α : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hα : IsRoot τ α)
    (c : Kˣ) (z : K) :
    rootTorusSL2 τ K β c * pinnedX τ K α z * (rootTorusSL2 τ K β c)⁻¹ =
      pinnedX τ K α (((c ^ (2 * iform β α / iform β β) : Kˣ) : K) * z) := by
  obtain ⟨-, hdH, -, -, hv, hH, -, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ K hβ
  obtain ⟨a, ha, -⟩ := hH _ (hdH c)
  have h1 := (hv c).2 α hα
  rw [ha] at h1
  change rootDiag a (rootVec τ K α) = _ at h1
  rw [rootDiag_rootVec a hα] at h1
  have hne : rootVec τ K α ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot hα]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h2 := smul_left_injective K hne h1
  rw [ha, rootDiagUnit_conj_pinnedX a hα]
  congr 2

theorem exponent_of_Deg1 {α : Fin τ.rank → ℤ} (hα : α ∈ Deg1 τ) :
    2 * iform (highRoot τ) α / iform (highRoot τ) (highRoot τ) = 1 := by
  rw [iform_highRoot_apply, iform_highRoot_apply, (CoordAux.mem_Deg1.1 hα).2,
    CoordAux.highRoot_degree]
  rw [show 2 * (cθ τ * 1) = cθ τ * 2 by ring]
  exact Int.ediv_self (mul_ne_zero (cθ_ne_zero τ) two_ne_zero)

variable (τ K) in
def scalGood (g : ModGL τ K) (c : K) : Subgroup (ModGL τ K) where
  carrier := {q | q ∈ Qθ τ K ∧ g * q * g⁻¹ ∈ Qθ τ K ∧
    heisCoord τ K (g * q * g⁻¹) = c • heisCoord τ K q}
  mul_mem' := by
    rintro q q' ⟨hq, hcq, hqe⟩ ⟨hq', hcq', hq'e⟩
    have e : g * (q * q') * g⁻¹ = (g * q * g⁻¹) * (g * q' * g⁻¹) := by group
    refine ⟨mul_mem hq hq', ?_, ?_⟩
    · rw [e]
      exact mul_mem hcq hcq'
    · rw [e, (heisCoord_spec τ K).mul _ hcq _ hcq', hqe, hq'e,
        (heisCoord_spec τ K).mul _ hq _ hq', smul_add]
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

theorem Qθ_le_scalGood (c : Kˣ) :
    Qθ τ K ≤ scalGood τ K (rootTorusSL2 τ K (highRoot τ) c) (c : K) := by
  have hθ : IsRoot τ (highRoot τ) := isRoot_highRoot τ
  show rootSpan τ K (parabolicRadicalRoots τ (Jθ τ)) ≤ _
  refine iSup₂_le fun α hα => ?_
  intro g hg
  obtain ⟨z, rfl⟩ := mem_rootSubgroup.1 hg
  have hQ : ∀ w : K, pinnedX τ K α w ∈ Qθ τ K := fun w => pinnedX_mem_rootSpan hα w
  rcases (CoordAux.mem_radRoots_iff α).1 hα with h | h
  · have hconj := torus_conj_pinnedX hθ (CoordAux.mem_Deg1.1 h).1 c z
    rw [exponent_of_Deg1 h, zpow_one] at hconj
    refine ⟨hQ z, ?_, ?_⟩
    · rw [hconj]
      exact hQ _
    · rw [hconj, (heisCoord_spec τ K).pinnedX_deg1 α h, (heisCoord_spec τ K).pinnedX_deg1 α h]
      ext β
      by_cases hβ : β = α
      · subst hβ
        simp
      · simp [Pi.single_apply, hβ]
  · subst h
    have hconj := torus_conj_pinnedX hθ hθ c z
    refine ⟨hQ z, ?_, ?_⟩
    · rw [hconj]
      exact hQ _
    · rw [hconj, (heisCoord_spec τ K).pinnedX_highRoot, (heisCoord_spec τ K).pinnedX_highRoot,
        smul_zero]

end ScalarTorusAux

theorem exists_scalarTorus (τ : Tag) (K : Type) [Field K] {c : K} (hc : c ≠ 0) :
    ∃ h : ModGL τ K, h ∈ Heis.Uθ τ K ⊔ Heis.Uneg τ K ∧ h ∈ Lθ τ K ∧
      ∀ q ∈ Qθ τ K, h * q * h⁻¹ ∈ Qθ τ K ∧
        heisCoord τ K (h * q * h⁻¹) = c • heisCoord τ K q := by
  obtain ⟨hL, hdH, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ K (isRoot_highRoot τ)
  refine ⟨rootTorusSL2 τ K (highRoot τ) (Units.mk0 c hc), ?_, ?_, fun q hq => ?_⟩
  · have hmem : rootTorusSL2 τ K (highRoot τ) (Units.mk0 c hc) ∈
        rootRankOneGroup τ K (highRoot τ) := ⟨HSL (Units.mk0 c hc), rfl⟩
    rw [hL] at hmem
    exact hmem
  · exact torusGroup_le_parabolicLevi _ (hdH _)
  · exact (ScalarTorusAux.Qθ_le_scalGood (Units.mk0 c hc) hq).2

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
