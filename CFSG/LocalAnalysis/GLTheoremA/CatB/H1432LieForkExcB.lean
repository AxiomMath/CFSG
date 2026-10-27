module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkDefs
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkBase
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkExcA
import CFSG.HardMathSupport.Lang.E6Descent.OuterDescentE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Descent


private theorem descent_e_three {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = 3 ^ f) (β : MulAut ↥(adjointGroup τ F))
    (hβ3 : β ^ 3 = 1) (hβ : β ∉ inner ↥(adjointGroup τ F)) :
    ∃ (d : ℕ) (T : F ≃+* F) (r j : ℕ) (δ : MulAut ↥(adjointGroup τ F)), f = 3 * d ∧
      Nat.card ↥(fixSubfield T) = 3 ^ d ∧ (β ^ r) ^ j = β ∧
        δ * β ^ r * δ⁻¹ = entrywiseAdjointAut τ T := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : ¬ 3 ∣ Nat.card F - 1 := by
    have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    have h1 : 1 ≤ 3 ^ f := Nat.one_le_pow _ _ (by norm_num)
    rw [hF]
    omega
  obtain ⟨d, T, r, j, δ, hfd, -, hTc, -, -, hrj, hδ⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_conj_entrywise_of_not_innerDiag τ hτ hf F hF
      Nat.prime_three (by norm_num) β hβ3 fun g a h => hq
        (CFSG.HardMathSupport.Lang.E6Descent.prime_dvd_of_diag_noninner τ hτ F Nat.prime_three g a
          β h hβ3 hβ).2
  exact ⟨d, T, r, j, δ, hfd, hTc, hrj, hδ⟩

end Descent

section E7


theorem lieOuterThreeAt_e7 : LieOuterThreeAt FamE7 := by
  intro P _ _ t n f hadm hF hm ψ hψ3 hψ
  obtain rfl := hF
  obtain rfl : n = 0 := hadm.2.2
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .E7 (3 ^ f) := (hm.chevalleyExceptionalModel (by decide)).2
  refine outerSubThree_of_untwisted hU hψ3 hψ fun F _ _ hFcard β hβ3 hβinn => ?_
  obtain ⟨d, T, r, j, δ, rfl, hTc, hrj, hδ⟩ :=
    descent_e_three (Or.inr (Or.inl rfl)) hf F hFcard β hβ3 hβinn
  refine outerSubThree_of_conj_pow hrj hδ ?_
  haveI : Finite ↥(fixSubfield T) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E7 ↥(fixSubfield T)) .E7 3 d :=
    ⟨⟨Nat.prime_three, by omega, rfl⟩, untwisted_adjointGroup hTc⟩
  exact outerSubThree_entrywise_of_model T (by decide) (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    (CFSG.LieType.Simplicity.fam_e7_simplicity _ 3 d hM).2

end E7

section E8


theorem lieOuterThreeAt_e8 : LieOuterThreeAt FamE8 := by
  intro P _ _ t n f hadm hF hm ψ hψ3 hψ
  obtain rfl := hF
  obtain rfl : n = 0 := hadm.2.2
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .E8 (3 ^ f) := (hm.chevalleyExceptionalModel (by decide)).2
  refine outerSubThree_of_untwisted hU hψ3 hψ fun F _ _ hFcard β hβ3 hβinn => ?_
  obtain ⟨d, T, r, j, δ, rfl, hTc, hrj, hδ⟩ :=
    descent_e_three (Or.inr (Or.inr rfl)) hf F hFcard β hβ3 hβinn
  refine outerSubThree_of_conj_pow hrj hδ ?_
  haveI : Finite ↥(fixSubfield T) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E8 ↥(fixSubfield T)) .E8 3 d :=
    ⟨⟨Nat.prime_three, by omega, rfl⟩, untwisted_adjointGroup hTc⟩
  exact outerSubThree_entrywise_of_model T (by decide) (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    (CFSG.LieType.Simplicity.fam_e8_simplicity _ 3 d hM).2

end E8

section E6


private theorem outerSubThree_entrywise_e6 {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hcard : Nat.card ↥(fixSubfield σ) = 3 ^ d) :
    OuterSubThree .E6 0 (3 * d) (fixSubgroup (entrywiseAdjointAut Tag.E6 σ)) := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) .E6 3 d :=
    ⟨⟨Nat.prime_three, hd, rfl⟩, untwisted_adjointGroup hcard⟩
  exact outerSubThree_entrywise_of_model σ (by decide) (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    (CFSG.LieType.Simplicity.fam_e6_simplicity _ 3 d hM).2

theorem lieOuterThreeAt_e6 : LieOuterThreeAt FamE6 := by
  intro P _ _ t n f hadm hF hm ψ hψ3 hψ
  obtain rfl := hF
  obtain rfl : n = 0 := hadm.2.2
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .E6 (3 ^ f) := (hm.chevalleyExceptionalModel (by decide)).2
  refine outerSubThree_of_untwisted hU hψ3 hψ fun F _ _ hFcard β hβ3 hβinn => ?_
  obtain ⟨d, T, r, j, δ, rfl, hTc, hrj, hδ⟩ := descent_e_three (Or.inl rfl) hf F hFcard β hβ3 hβinn
  exact outerSubThree_of_conj_pow hrj hδ (outerSubThree_entrywise_e6 (by omega) T hTc)

end E6

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
