module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndFieldBasic
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNormal
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem exists_hom_zmod_two_of_index_eq_two {X : Type*} [Group X] {H : Subgroup X}
    (hH : H.index = 2) : ∃ χ : X →* Multiplicative (ZMod 2), ∀ g, χ g = 1 ↔ g ∈ H := by
  classical
  have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  have hsq : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
  refine ⟨{ toFun := fun g => if g ∈ H then 1 else Multiplicative.ofAdd 1,
            map_one' := by simp only [H.one_mem, ↓reduceIte]
            map_mul' := fun a b => ?_ }, fun g => ?_⟩
  · simp only [Subgroup.mul_mem_iff_of_index_two hH]
    by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [ha, hb, hsq]
  · change (if g ∈ H then 1 else Multiplicative.ofAdd (1 : ZMod 2)) = 1 ↔ g ∈ H
    by_cases hg : g ∈ H <;> simp [hg, hne]

section GraphCoordinate

variable {m : ℕ} {F : Type} [Field F] [Finite F]

theorem index_semilinearAutGroup (hm : 3 ≤ m) : (LinearFlag.semilinearAutGroup m F).index = 2 := by
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨LinearFlag.dualAut m F, ProjectivePlane.dualAut_not_mem_semilinearAutGroup hm,
    fun b => ?_⟩
  have hb : b ∈ LinearFlag.standardAutGroup m F := by
    rw [(LinearFlag.automorphism_generation (K := F) hm).1]
    exact mem_top b
  exact (LinearFlag.mem_or_mul_dualAut_mem hb).symm

theorem exists_linearGraphCoordinate (hm : 3 ≤ m) :
    ∃ χ : MulAut (LinearFlag.projectiveSL m F) →* Multiplicative (ZMod 2),
      (∀ x, χ (MulAut.conj x) = 1) ∧
        ∀ α, α ∉ LinearFlag.semilinearAutGroup m F → χ α ≠ 1 := by
  obtain ⟨χ, hχ⟩ := exists_hom_zmod_two_of_index_eq_two (index_semilinearAutGroup (F := F) hm)
  exact ⟨χ, fun x => (hχ _).2 (LinearPilot.conj_mem_semilinearAutGroup x),
    fun α hα h => hα ((hχ α).1 h)⟩

theorem not_mem_semilinearAutGroup_of_lieModel_PSp (hm : 3 ≤ m) {e : ℕ} (he : 1 ≤ e)
    (hF : Nat.card F = 2 ^ e) {α : MulAut (LinearFlag.projectiveSL m F)} (hα2 : α ^ 2 = 1)
    (hαo : α ∉ (MulAut.conj : LinearFlag.projectiveSL m F →* MulAut _).range) {n f : ℕ}
    (hfix : LieModel (fixedSubgroup α) .PSp n 2 f) : α ∉ LinearFlag.semilinearAutGroup m F := by
  intro hαE
  obtain ⟨A, σ, rfl⟩ := LinearFlag.mem_semilinearAutGroup_iff.1 hαE
  have hβ := CatalogueBLinearHigherB.congr_semilinear (n := m) (K := F) A σ
  have hβ2 : CatalogueBLinearSemilinear.semilinearAction m F A σ ^ 2 = 1 := by
    rw [← hβ, ← map_pow, hα2, map_one]
  by_cases hσ : σ = 1
  · subst hσ
    have h1 := CatLeafProof.innerDiagonalAction_mem_inner_of_sq he hF A
      (by rwa [CatalogueBLinearSemilinear.semilinearAction_one_field] at hβ2)
    rw [← CatalogueBLinearSemilinear.semilinearAction_one_field, ← hβ] at h1
    exact hαo ((FixedFourGroup.congr_mem_inner_iff _ _).1 h1)
  · have hP := LinearPilot.psl_field_pComponents (by omega) he hF A σ hσ hβ2
    let Ψ : fixedSubgroup (LinearFlag.conjAut m F A * LinearFlag.fieldAut m F σ) ≃*
        fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction m F A σ) :=
      (fixedSubgroupCongrEquiv (CatalogueBLinearHigherB.nativeEquiv m F) _).trans
        (MulEquiv.subgroupCongr (congrArg fixedSubgroup hβ))
    have hfix' : LieModel (fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction m F A σ))
        .PSp n 2 f := LieType.CurtisTits.lieModel_of_mulEquiv Ψ hfix
    obtain ⟨hadm', hm', -⟩ := hP ⊤ (isPComponent_top_of_lieModel_PSp hfix')
    exact false_of_lieModel_ne_PSp (sp2mEvenTypeDetClassical n) hfix' (Or.inl (by decide))
      (by decide) hadm' (LieType.CurtisTits.lieModel_of_mulEquiv Subgroup.topEquiv hm')

end GraphCoordinate

end CFSG.SeitzReduction.SymplecticPilot
