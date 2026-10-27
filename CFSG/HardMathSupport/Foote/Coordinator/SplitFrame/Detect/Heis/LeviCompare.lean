module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.LeviNormalForm
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K]

theorem parabolicPosRoots_pos {α : Fin τ.rank → ℤ} (hα : α ∈ parabolicPosRoots τ (Jθ τ)) :
    IsRoot τ α ∧ 0 < height α := ⟨hα.1.1, hα.2.2⟩

theorem image_parabolicPosRoots_pos {w₀ : WeylGroup τ}
    (hmin : ∀ β ∈ parabolicPosRoots τ (Jθ τ), 0 < height (w₀ • β)) :
    ∀ α ∈ (fun β => w₀ • β) '' parabolicPosRoots τ (Jθ τ), IsRoot τ α ∧ 0 < height α := by
  rintro _ ⟨β, hβ, rfl⟩
  exact ⟨IsRoot.smul (parabolicPosRoots_pos hβ).1 w₀, hmin β hβ⟩

theorem normalForm_compare {g : ModGL τ K} {wa : WeylGroup τ} {ha ua va : ModGL τ K}
    (hha : ha ∈ torusGroup τ K) (hua : ua ∈ rootSpan τ K (parabolicPosRoots τ (Jθ τ)))
    (hva : va ∈ rootSpan τ K (parabolicPosRoots τ (Jθ τ) ∩ inversionSet wa))
    (hga : g = ha * ua * canonicalRep (coxeterSystem τ) K wa * va) {w₀ : WeylGroup τ}
    (hmin : ∀ β ∈ parabolicPosRoots τ (Jθ τ), 0 < height (w₀ • β))
    (hg₀ : g ∈ conjSub (canonicalRep (coxeterSystem τ) K w₀) (Lθ τ K)) :
    wa • (w₀ • highRoot τ) = w₀ • highRoot τ ∧
      ua ∈ rootSpan τ K ((fun β => w₀ • β) '' parabolicPosRoots τ (Jθ τ)) ∧
      va ∈ rootSpan τ K ((fun β => w₀ • β) '' parabolicPosRoots τ (Jθ τ)) := by
  obtain ⟨wb, hb, ub, vb, hhb, hub, hvb, hwb, hgb⟩ := normalForm_conj_Lθ τ K hmin hg₀
  have hposA : ∀ α ∈ parabolicPosRoots τ (Jθ τ), IsRoot τ α ∧ 0 < height α :=
    fun α hα => parabolicPosRoots_pos hα
  have hposB := image_parabolicPosRoots_pos hmin
  have huaU : ua ∈ posUnipotent τ K := rootSpan_le_posUnipotent hposA hua
  have hubU : ub ∈ posUnipotent τ K := rootSpan_le_posUnipotent hposB hub
  have hvaI : va ∈ rootSpan τ K (inversionSet wa) :=
    rootSpan_mono_of_subset Set.inter_subset_right hva
  have hvbI : vb ∈ rootSpan τ K (inversionSet wb) :=
    rootSpan_mono_of_subset Set.inter_subset_right hvb
  obtain ⟨hw, -, hu, hv⟩ := CFSG.HardMathSupport.Timmesfeld.Torality.bruhat_factor_unique τ K wa wb
    ha hb ua ub va vb hha hhb huaU hubU hvaI hvbI (hga.symm.trans hgb)
  refine ⟨hw ▸ hwb, hu ▸ hub, ?_⟩
  rw [hv]
  exact rootSpan_mono_of_subset Set.inter_subset_left hvb

theorem mem_conjSub_Lθ_of_centralizes (w₀ : WeylGroup τ) {g : ModGL τ K}
    (hg : g ∈ adjointGroup τ K)
    (hcθ : ∀ x ∈ conjSub (canonicalRep (coxeterSystem τ) K w₀) (Uθ τ K), g * x = x * g)
    (hcn : ∀ x ∈ conjSub (canonicalRep (coxeterSystem τ) K w₀) (Uneg τ K), g * x = x * g) :
    g ∈ conjSub (canonicalRep (coxeterSystem τ) K w₀) (Lθ τ K) := by
  set n : ModGL τ K := canonicalRep (coxeterSystem τ) K w₀ with hn
  have hnG : n ∈ adjointGroup τ K := canonicalRep_mem_adjointGroup _ K w₀
  have hconj : ∀ A : Subgroup (ModGL τ K), (∀ x ∈ conjSub n A, g * x = x * g) →
      ∀ x ∈ A, (n⁻¹ * g * n) * x = x * (n⁻¹ * g * n) := by
    intro A hA x hx
    have hx' : n * x * n⁻¹ ∈ conjSub n A := mem_conjSub_iff.2 (by
      rw [show n⁻¹ * (n * x * n⁻¹) * n = x by group]; exact hx)
    have e := hA _ hx'
    calc n⁻¹ * g * n * x = n⁻¹ * (g * (n * x * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * x * n⁻¹) * g) * n := by rw [e]
      _ = x * (n⁻¹ * g * n) := by group
  exact mem_conjSub_iff.2 (centralizer_Uθ_inf_centralizer_Uneg_le_Lθ τ K
    (mul_mem (mul_mem (inv_mem hnG) hg) hnG) (hconj _ hcθ) (hconj _ hcn))

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
