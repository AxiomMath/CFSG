module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Normalizer
public import CFSG.HardMathSupport.Timmesfeld.Torality.Conjugacy
public import CFSG.RankThree.PartOne.KE.ConjRootSpan
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.RootCentExc
open CFSG.HardMathSupport.Timmesfeld.Torality

set_option linter.unusedSectionVars false


variable (τ : Tag) (K : Type) [Field K]

theorem conjSub_Uθ_of_mem_posUnipotent {v : ModGL τ K} (hv : v ∈ posUnipotent τ K) :
    conjSub v (Uθ τ K) = Uθ τ K := by
  have hc : ∀ x ∈ Uθ τ K, v * x * v⁻¹ = x := by
    intro x hx
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    rw [(commute_of_mem_posUnipotent (isMaxHeight_highRoot τ) hv c).eq, mul_inv_cancel_right]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hc y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hc x hx]⟩

theorem exists_normalForm {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) :
    ∃ p ∈ Pθ τ K, ∃ β, IsRoot τ β ∧ (∃ w : WeylGroup τ, β = w • highRoot τ) ∧
      conjSub g (Uθ τ K) = conjSub p (rootSubgroup τ K β) := by
  obtain ⟨w, h, hh, u, hu, v, hv, rfl⟩ := bruhat_factor_exists τ K g hg
  have hvU : v ∈ posUnipotent τ K :=
    rootSpan_le_posUnipotent (fun α hα => inversionSet_pos hα) hv
  refine ⟨h * u, ?_, w • highRoot τ, IsRoot.smul (isRoot_highRoot τ) w, ⟨w, rfl⟩, ?_⟩
  · exact borelGroup_le_parabolicSubgroup _ (mul_mem (Subgroup.mem_sup_left hh)
      (Subgroup.mem_sup_right hu))
  · rw [conjSub_mul, conjSub_Uθ_of_mem_posUnipotent τ K hvU, conjSub_mul]
    unfold conjSub
    rw [CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup w (isRoot_highRoot τ)]

theorem isLongRoot_smul_highRoot (w : WeylGroup τ) : IsLongRoot τ (w • highRoot τ) := by
  unfold IsLongRoot
  exact iform_smul w _ _

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
