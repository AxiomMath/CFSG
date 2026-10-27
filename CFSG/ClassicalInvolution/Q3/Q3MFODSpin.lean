module

public import CFSG.ClassicalInvolution.Q3.Q3OTBase
public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.Q3.Q3MFODSim

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOD

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3.Q3TLK
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.RouteD.TWZ CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Data

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem ringEquiv_eq_refl_of_card_three (hF : Nat.card F = 3) (φ : F ≃+* F) :
    φ = RingEquiv.refl F := by
  refine RingEquiv.ext fun x => ?_
  rcases cases_of_card_three hF x with rfl | rfl | rfl <;> simp

theorem exists_sim_data3 (hF3 : Nat.card F = 3) [Group.IsPerfect (spinGroup Q)]
    (hZ3 : ∀ c ∈ Subgroup.center (spinGroup Q), ¬ 3 ∣ orderOf c)
    (hlift : LiftSim Q (QuotientGroup.mk' (Subgroup.center (spinGroup Q))))
    {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars F (ι → F)))
    (ρ : MulAut (spinGroup Q ⧸ Subgroup.center (spinGroup Q))) (hρ2 : ρ * ρ = 1)
    {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝓕)
    (hρR : ∀ r ∈ R, ρ (QuotientGroup.mk r) = QuotientGroup.mk r) :
    ∃ (α : MulAut (spinGroup Q)) (a : (ι → F) ≃ₗ[F] (ι → F)) (μ : F) (fr : OFrame Q),
      μ ≠ 0 ∧ (∀ v, Q (a v) = μ * Q v) ∧
      (∀ x, spinAction Q (α x) = a * spinAction Q x * a⁻¹) ∧
      (∀ x, (QuotientGroup.mk (α x) : spinGroup Q ⧸ Subgroup.center (spinGroup Q)) =
        ρ (QuotientGroup.mk x)) ∧ α * α = 1 ∧ (∀ A : SL(2, F), a * fr.La A = fr.La A * a) := by
  classical
  set ψ : spinGroup Q →* spinGroup Q ⧸ Subgroup.center (spinGroup Q) :=
    QuotientGroup.mk' (Subgroup.center (spinGroup Q)) with hψ
  have hψs : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  have hψk : ψ.ker ≤ Subgroup.center (spinGroup Q) := by rw [hψ, QuotientGroup.ker_mk']
  obtain ⟨α, hαψ, A, φ, μ, hsim, hmat⟩ := hlift (autRange ψ hψs ρ)
  have hαρ : ∀ x, ψ (α x) = ρ (ψ x) := fun x => congrArg Subtype.val (hαψ x)
  have hφ := ringEquiv_eq_refl_of_card_three hF3 φ
  subst hφ
  have hmat' : ∀ x, spinMatrix Q (α x) = A * spinMatrix Q x * A⁻¹ := by
    intro x
    rw [hmat x, glFieldEquiv_refl]
  set a : (ι → F) ≃ₗ[F] (ι → F) := glLin A with ha
  have hθα : ∀ x, spinAction Q (α x) = a * spinAction Q x * a⁻¹ := by
    intro x
    rw [← glLin_spinMatrix, hmat', map_mul, map_mul, map_inv, glLin_spinMatrix]
  have hsim' : ∀ v, Q (a v) = μ * Q v := by
    intro v
    have := hsim v
    simpa [ha, glLin_apply] using this
  have hα2 : α * α = 1 := by
    have hc : ∀ s ∈ (⊤ : Subgroup (spinGroup Q)),
        s⁻¹ * (α * α) s ∈ Subgroup.center (spinGroup Q) := by
      intro s _
      have h1 : ψ (α (α s)) = ψ s := by
        rw [hαρ, hαρ]
        have := congrArg (fun m : MulAut (spinGroup Q ⧸ Subgroup.center (spinGroup Q)) =>
          m (ψ s)) hρ2
        simpa using this
      exact QuotientGroup.eq.mp h1.symm
    have hfix := alpha_fixes_commutators (α * α) hc
    have hP : ⁅(⊤ : Subgroup (spinGroup Q)), (⊤ : Subgroup (spinGroup Q))⁆ =
        (⊤ : Subgroup (spinGroup Q)) := by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top
    refine MulEquiv.ext fun s => ?_
    exact hfix s (by rw [hP]; exact Subgroup.mem_top s)
  have hRfix : ∀ r ∈ R, α r = r :=
    Q3TY.eq_of_fixed_of_pow3 ψ hψk (fun z hz => hZ3 z (hψk hz)) α ρ hαρ (cq.pow3 R hR) hρR
  obtain ⟨i, fr, hfr, -⟩ := cq.map_mem R hR
  refine ⟨α, a, (μ : F), fr, μ.ne_zero, hsim', hθα, hαρ, hα2, ?_⟩
  intro B
  have hmem : fr.La B ∈ R.map (spinAction Q) := by rw [hfr]; exact ⟨B, rfl⟩
  obtain ⟨r, hr, hrB⟩ := hmem
  have h1 := hθα r
  rw [hRfix r hr, hrB] at h1
  calc a * fr.La B = (a * fr.La B * a⁻¹) * a := by group
    _ = fr.La B * a := by rw [← h1]

end Data

end CFSG.ClassicalInvolution.Q3.Q3MFOD
