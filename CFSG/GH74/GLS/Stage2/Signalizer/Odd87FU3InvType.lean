module

public import CFSG.GH74.KGroups.L3EpsUniAut
public import CFSG.GH74.Generic.S45.LUniLift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.SubgroupLists
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.GH74.KGroups.L3Eps.Uni
open CFSG.GH74.Generic.S45.Uni (class2_transpose scalar_of_comp det_unitary_norm ne_zero_of_unitary
  two_ne_zero_of_ne mkSU coe_mkSU)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} {F : Type} [Field F]

theorem involution_type_of_three_le (h : UnitaryFieldData p f F) (hp : p ≠ 2) (h3 : 3 ≤ p ^ f)
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    {σ : MulAut K} (hσ : σ * σ = 1) :
    (∃ A : GL (Fin 3) F,
        ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1 ∧
        (∃ μ : F, (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = μ • 1) ∧
        ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
          (g' : GL (Fin 3) F) = A * g * A⁻¹ ∧ θ g' = σ (θ g)) ∨
    (∃ (φ : F ≃+* F) (A : GL (Fin 3) F), (∀ c, φ c = h.bar c) ∧
        ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1 ∧
        (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F).map h.bar = 1 ∧
        ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
          (g' : GL (Fin 3) F) = A * glAut φ (g : GL (Fin 3) F) * A⁻¹ ∧ θ g' = σ (θ g)) := by
  have _ := h3
  have hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3) := by
    rw [hθ.ker]; exact unitaryScalars_le_center h 3
  obtain ⟨A, φ, hA, hAu, hlift, hinv⟩ :=
    CFSG.GH74.Generic.S45.exists_lift_unitarySU' h hp (le_refl 3) θ hθ.surj hker (σ : K ≃* K)
  obtain ⟨hφ, hcomp⟩ := hinv (fun x => by
    have := congrArg (fun φ : MulAut K => φ x) hσ
    simpa using this)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_ne h hp
  have hφφ : φ * φ = 1 := by
    rcases hφ with rfl | hb
    · ext c
      rfl
    · ext c
      change φ (φ c) = c
      rw [hb, hb, h.bar_bar]
  obtain ⟨μ, hμ⟩ := scalar_of_comp h h2 (le_refl 3) hφφ hA hcomp
  have hlift' : ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
      (g' : GL (Fin 3) F) = A * glAut φ (g : GL (Fin 3) F) * A⁻¹ ∧ θ g' = σ (θ g) :=
    fun g => ⟨unitaryConjHom A φ hA g, rfl, hlift g⟩
  rcases hφ with rfl | hb
  · left
    refine ⟨A, hAu, ⟨μ, ?_⟩, fun g => ?_⟩
    · have hmap : (A : Matrix (Fin 3) (Fin 3) F).map (RingEquiv.refl F) = A := by
        ext i j
        rfl
      rw [hmap] at hμ
      exact hμ
    · have : glAut (RingEquiv.refl F) (g : GL (Fin 3) F) = g := by
        apply Units.ext
        ext i j
        rfl
      rw [← this]
      exact hlift' g
  · right
    refine ⟨φ, A, hb, hAu, ?_, hlift'⟩
    have hmapφ : (A : Matrix (Fin 3) (Fin 3) F).map φ = (A : Matrix (Fin 3) (Fin 3) F).map h.bar := by
      ext i j
      exact hb _
    rw [hmapφ] at hμ
    obtain ⟨hAt, hAt'⟩ := class2_transpose h hAu hμ
    have hA0 := ne_zero_of_unitary h (by omega) hAu
    have hμμ : μ * μ = 1 := by
      have h3 : (μ * μ - 1) • (A : Matrix (Fin 3) (Fin 3) F) = 0 := by
        rw [sub_smul, one_smul, ← smul_smul, ← hAt', ← hAt, sub_self]
      have := (smul_eq_zero.1 h3).resolve_right hA0
      linear_combination this
    rcases mul_self_eq_one_iff.1 hμμ with hμ1 | hμ1
    · rw [hμ1, one_smul] at hμ
      exact hμ
    · exfalso
      rw [hμ1] at hμ
      exact false_of_alt h h2 hAu hμ

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
