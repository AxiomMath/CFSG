module

public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs
import CFSG.RankThree.PartTwo.KFacts.L34Aut
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open
open scoped commutatorElement

theorem pRank_mulAut_le_two_of_isLThreeFour {X : Type} [Group X] [Finite X]
    (h : IsLThreeFour X) : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) ≤ 2 := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  have e' : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)
  have := CFSG.RankThree.PartTwo.KFacts.L34.pRank_three_mulAut_of_mulEquiv hcard e'
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at this
  exact this.le

@[expose] def quotientCenterAut' (X : Type*) [Group X] :
    MulAut X →* MulAut (X ⧸ Subgroup.center X) where
  toFun a := QuotientGroup.congr (Subgroup.center X) (Subgroup.center X) a
    (Subgroup.map_center_eq a)
  map_one' := by
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]

theorem commutator_mul_central {X : Type*} [Group X] {x y z w : X}
    (hz : z ∈ Subgroup.center X) (hw : w ∈ Subgroup.center X) :
    x * z * (y * w) * (x * z)⁻¹ * (y * w)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hz' := Subgroup.mem_center_iff.1 hz
  have hw' := Subgroup.mem_center_iff.1 hw
  calc x * z * (y * w) * (x * z)⁻¹ * (y * w)⁻¹
      = x * (z * (y * w) * z⁻¹) * x⁻¹ * (w⁻¹ * y⁻¹) := by group
    _ = x * (y * w) * x⁻¹ * (w⁻¹ * y⁻¹) := by rw [← hz' (y * w), mul_inv_cancel_right]
    _ = x * y * (w * x⁻¹ * w⁻¹) * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [← hw' x⁻¹, mul_inv_cancel_right]

theorem quotientCenterAut'_injective {X : Type*} [Group X] (hperf : commutator X = ⊤) :
    Function.Injective (quotientCenterAut' X) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  have hz : ∀ x : X, x⁻¹ * a x ∈ Subgroup.center X := by
    intro x
    have h1 := congrArg (fun φ : MulAut (X ⧸ Subgroup.center X) =>
      φ (QuotientGroup.mk x)) ha
    simp only [quotientCenterAut', MonoidHom.coe_mk, OneHom.coe_mk, QuotientGroup.congr_mk,
      MulAut.one_apply] at h1
    exact QuotientGroup.eq.1 h1.symm
  have hcomm : ∀ x y : X, a (x * y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹ := by
    intro x y
    obtain ⟨z₁, hz₁c, hz₁⟩ : ∃ z ∈ Subgroup.center X, a x = x * z := ⟨x⁻¹ * a x, hz x, by group⟩
    obtain ⟨z₂, hz₂c, hz₂⟩ : ∃ z ∈ Subgroup.center X, a y = y * z := ⟨y⁻¹ * a y, hz y, by group⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hz₁, hz₂]
    exact commutator_mul_central hz₁c hz₂c
  have hall : ∀ x : X, a x = x := by
    intro x
    have hx0 : x ∈ commutator X := by
      rw [hperf]
      exact Subgroup.mem_top x
    have hx : x ∈ Subgroup.closure {g : X | ∃ g₁ ∈ (⊤ : Subgroup X), ∃ g₂ ∈ (⊤ : Subgroup X),
        ⁅g₁, g₂⁆ = g} := by
      rw [← Subgroup.commutator_def]
      exact hx0
    refine Subgroup.closure_induction (p := fun g _ => a g = g) (fun g hg => ?_) (map_one a)
      (fun u v _ _ hu hv => by rw [map_mul, hu, hv]) (fun u _ hu => by rw [map_inv, hu]) hx
    obtain ⟨g₁, -, g₂, -, rfl⟩ := hg
    exact hcomm g₁ g₂
  exact Subgroup.mem_bot.2 (MulEquiv.ext hall)

theorem pRank_mulAut_le_two_of_isSLThreeFour {X : Type} [Group X] [Finite X]
    (h : IsSLThreeFour X) (hperf : commutator X = ⊤) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) ≤ 2 := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  have e₁ : X ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  have hq : IsLThreeFour (X ⧸ Subgroup.center X) :=
    ⟨F, inferInstance, inferInstance, hcard,
      ⟨(QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F)⟩⟩
  exact (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) (quotientCenterAut' X)
    (quotientCenterAut'_injective hperf)).trans (pRank_mulAut_le_two_of_isLThreeFour hq)

theorem pRank_mulAut_le_two_of_L34 {X : Type} [Group X] [Finite X]
    (h : IsLThreeFour X ∨ IsSLThreeFour X) (hperf : commutator X = ⊤) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) ≤ 2 :=
  h.elim pRank_mulAut_le_two_of_isLThreeFour fun h => pRank_mulAut_le_two_of_isSLThreeFour h hperf

end CFSG.LocalAnalysis.GLTheoremB
