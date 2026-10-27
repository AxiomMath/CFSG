module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_5

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv

open Module CFSG.ComponentClassification.OutcomeLocal CFSG.HardMathSupport.Solomon.Coordinator

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem isMin_P (S : i285_Setup M) (hXW : S.X ≤ S.W) : S.IsMin S.P := by
  refine ⟨S.W_le_stab_P, inf_lt_left.2 S.not_P_le_Q, le_rfl, fun T hT1 hT2 hT3 => ?_⟩
  rcases S.eq_of_stab (hXW.trans hT1) hT2.le hT3 with h | h
  · exact absurd h hT2.ne'
  · exact h

theorem D_subset_T_P (S : i285_Setup M) (hP : S.IsMin S.P) : S.D ⊆ S.T S.P := by
  intro d hd
  obtain ⟨x, hx, hdx⟩ := S.exists_mem_T hP hd
  rwa [i285_map_eq_of_stab (S.X_le_stab_P hx)] at hdx

theorem X_le_H_P (S : i285_Setup M) (hXW : S.X ≤ S.W) : S.X ≤ S.H S.P := by
  refine hXW.trans ?_
  show Subgroup.closure S.D ≤ Subgroup.closure (S.T S.P)
  exact (Subgroup.closure_le _).2 fun d hd =>
    Subgroup.subset_closure (D_subset_T_P S (isMin_P S hXW) hd)

theorem exists_irreducible_section (S : i285_Setup M) (hXW : S.X ≤ S.W) :
    ∃ (U : Type) (_ : AddCommGroup U) (_ : Module (ZMod 2) U) (_ : Finite U)
      (ψ : ↥S.X →* LinearMap.GeneralLinearGroup (ZMod 2) U),
      Function.Injective ψ ∧
      (∀ T : Submodule (ZMod 2) U,
        (∀ g ∈ ψ.range, ∀ w ∈ T, (g : U →ₗ[ZMod 2] U) w ∈ T) → T = ⊥ ∨ T = ⊤) ∧
      (∃ T : Set (LinearMap.GeneralLinearGroup (ZMod 2) U),
        (∀ t ∈ T, IsF2Transvection t) ∧ ψ.range = Subgroup.closure T) ∧
      IsF2Transvection (ψ ⟨S.τ, S.hτX⟩) := by
  have hP := isMin_P S hXW
  have hXH : S.X ≤ S.H S.P := X_le_H_P S hXW
  have hrange : ((S.ρ hP).comp (Subgroup.inclusion hXH)).range = (S.ρ hP).range := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.1, S.H_le_X S.P y.2⟩, rfl⟩
  refine ⟨↥S.P ⧸ S.Q.comap S.P.subtype, inferInstance, inferInstance, ?_,
    (S.ρ hP).comp (Subgroup.inclusion hXH), ?_, ?_, ?_, ?_⟩
  · exact Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  · exact (S.ρ_injective hP).comp (Subgroup.inclusion_injective hXH)
  · intro T hT
    rw [hrange] at hT
    exact S.ρ_irred hP T hT
  · refine ⟨(S.ρ hP) '' (Subtype.val ⁻¹' S.T S.P), ?_, ?_⟩
    · rintro _ ⟨⟨d, hdH⟩, hd, rfl⟩
      exact S.ρ_transvection hP hd
    · rw [hrange]
      exact S.ρ_range hP
  · exact S.ρ_transvection hP (D_subset_T_P S hP S.τ_mem_D)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGTv
