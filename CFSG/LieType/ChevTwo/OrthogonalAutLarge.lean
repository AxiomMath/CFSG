module

public import CFSG.LieType.ChevTwo.Defs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

namespace AutLarge

theorem zmodTwo_ringEquiv_apply (σ : ZMod 2 ≃+* ZMod 2) (x : ZMod 2) : σ x = x := by
  have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases h x with rfl | rfl
  · exact map_zero σ
  · exact map_one σ

theorem statedScalars_zmodTwo {ι : Type} [Fintype ι] [DecidableEq ι] :
    StatedScalars ι (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨c, rfl⟩
  have hc : c = 1 := by revert c; decide
  rw [hc, map_one]
  exact Subgroup.one_mem _

theorem omegaTwoAutInduced_of_semilinear {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : (ι → ZMod 2) → ZMod 2)
    (H : ∀ β : MulAut (StatedProj (StatedOmega Q)),
      ∃ (σ : ZMod 2 ≃+* ZMod 2) (A : GL ι (ZMod 2)) (μ : ZMod 2), μ ≠ 0 ∧
        (∀ v, Q (Matrix.mulVec (A : Matrix ι ι (ZMod 2)) fun i => σ (v i)) = μ * σ (Q v)) ∧
        ∀ g : StatedOmega Q,
          ∃ hg : A * glAut σ (g : GL ι (ZMod 2)) * A⁻¹ ∈ StatedOmega Q,
            β (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩) :
    OmegaTwoAutInduced Q := by
  intro α
  have hinj : Function.Injective
      (QuotientGroup.mk' ((StatedScalars ι (ZMod 2)).subgroupOf (StatedOmega Q))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', statedScalars_zmodTwo,
      Subgroup.bot_subgroupOf]
  let e : StatedOmega Q ≃* StatedProj (StatedOmega Q) :=
    MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨hinj, QuotientGroup.mk'_surjective _⟩
  obtain ⟨σ, A, μ, hμ, hQ, hβ⟩ := H (MulAut.congr e α)
  have hσ : ∀ x, σ x = x := zmodTwo_ringEquiv_apply σ
  have hμ1 : μ = 1 := by
    have h : ∀ y : ZMod 2, y ≠ 0 → y = 1 := by decide
    exact h μ hμ
  have hgl : ∀ g : GL ι (ZMod 2), glAut σ g = g := fun g => by
    apply Units.ext
    ext i j
    rw [coe_glAut, Matrix.map_apply, hσ]
  refine ⟨A, fun x => ?_, fun x => ?_⟩
  · have := hQ x
    simp only [hσ, hμ1, one_mul] at this
    exact this
  · obtain ⟨hg, hx⟩ := hβ x
    have h0 : (MulAut.congr e α) (QuotientGroup.mk x) = e (α x) := by
      change (MulAut.congr e α) (e x) = _
      simp [MulAut.congr_apply]
    have h1 : e (α x) = e ⟨A * glAut σ (x : GL ι (ZMod 2)) * A⁻¹, hg⟩ := h0.symm.trans hx
    have h2 := congrArg (fun y : StatedOmega Q => (y : GL ι (ZMod 2))) (e.injective h1)
    simpa [hgl] using h2

end AutLarge

theorem omegaTwoAutInduced_minus_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    OmegaTwoAutInduced (StatedQuadMinus (n + 1) (ZMod 2) 1 1) :=
  AutLarge.omegaTwoAutInduced_of_semilinear _ fun β =>
    CFSG.ComponentClassification.RankTwoClassical.exists_semilinear_minus (by omega)
      (by decide) β

theorem omegaTwoAutInduced_plus_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    OmegaTwoAutInduced (StatedQuadPlus (n + 1) (ZMod 2)) :=
  AutLarge.omegaTwoAutInduced_of_semilinear _ fun β =>
    CFSG.ComponentClassification.RankTwoClassical.exists_semilinear_plus (by omega) β

end CFSG.LieType.ChevTwo
