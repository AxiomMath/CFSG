module

public import CFSG.HardMathSupport.Solomon.Coordinator.CycThree
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.Quasithin.Background.F918Z4bAut
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Quasithin
  CFSG.RankThree.PartTwo.KFacts
open CFSG.Open (StatedProj StatedSL)

@[deprecated (since := "2026-10-15")] alias l514vexp_cyc_three := cyc_three

theorem l514vexp_toPGL_of_pow_three {K : Type} [Field K] (g : PGL2 K) (hg : g ^ 3 = 1) :
    ∃ x : PSL2 K, Matrix.ProjectiveSpecialLinearGroup.toPGL x = g :=
  CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_three hg

theorem l514vexp_inner_of_fieldPart {K : Type} [Field K] [Finite K] {δ : MulAut (PSL2 K)}
    (h : autFieldPart K δ = 1) (h3 : δ ^ 3 = 1) : ∃ x : PSL2 K, MulAut.conj x = δ := by
  obtain ⟨g, hg⟩ := mem_range_pglAction_of_autFieldPart_eq_one h
  have hg3 : g ^ 3 = 1 :=
    pglAction_injective_of_finite K (by rw [map_pow, hg, h3, map_one])
  obtain ⟨x, hx⟩ := l514vexp_toPGL_of_pow_three g hg3
  exact ⟨x, by rw [← pglAction_toPGL K x, hx, hg]⟩

theorem l514vexp_out3_psl2 (K : Type) [Field K] [Finite K] (α β : MulAut (PSL2 K)) (hα : α ^ 3 = 1)
    (hβ : β ^ 3 = 1) (hab : α * β = β * α) :
    (∃ x : PSL2 K, MulAut.conj x = α) ∨ ∃ (j : ℕ) (x : PSL2 K), MulAut.conj x = β * α ^ j := by
  have hcyc : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have hf3 : ∀ δ : MulAut (PSL2 K), δ ^ 3 = 1 → (autFieldPart K δ) ^ 3 = 1 := fun δ h => by
    rw [← map_pow, h, map_one]
  have hcy : (autFieldPart K α = 1) ∨ ∃ j : ℕ, autFieldPart K β * (autFieldPart K α) ^ j = 1 := by
    have : Finite (K ≃+* K) :=
      Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) (fun _ _ h => RingEquiv.ext (congrFun h))
    exact cyc_three (hf3 α hα) (hf3 β hβ)
  rcases hcy with h | ⟨j, hj⟩
  · exact Or.inl (l514vexp_inner_of_fieldPart h hα)
  · right
    refine ⟨j, l514vexp_inner_of_fieldPart (δ := β * α ^ j) ?_ ?_⟩
    · rw [map_mul, map_pow]; exact hj
    · have hc : Commute β (α ^ j) := (show Commute β α from hab.symm).pow_right j
      rw [hc.mul_pow, hβ, ← pow_mul, mul_comm j 3, pow_mul, hα, one_pow, one_mul]

theorem l514vexp_out3 (F : Type) [Field F] [Finite F] (α β : MulAut (StatedProj (StatedSL 2 F)))
    (hα : α ^ 3 = 1) (hβ : β ^ 3 = 1) (hab : α * β = β * α) :
    (∃ c, MulAut.conj c = α) ∨ ∃ (j : ℕ) (c : StatedProj (StatedSL 2 F)), MulAut.conj c = β * α ^ j := by
  let φ : PSL2 F ≃* StatedProj (StatedSL 2 F) :=
    CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F
  let ψ : MulAut (StatedProj (StatedSL 2 F)) ≃* MulAut (PSL2 F) := MulAut.congr φ.symm
  have key := l514vexp_out3_psl2 F (ψ α) (ψ β) (by rw [← map_pow, hα, map_one])
    (by rw [← map_pow, hβ, map_one]) (by rw [← map_mul, ← map_mul, hab])
  have back : ∀ (x : PSL2 F) (δ : MulAut (StatedProj (StatedSL 2 F))),
      MulAut.conj x = ψ δ → MulAut.conj (φ x) = δ := fun x δ hx => by
    apply ψ.injective
    rw [← hx]
    exact congr_mulAutConj φ.symm (φ x) ▸ by rw [φ.symm_apply_apply]
  rcases key with ⟨x, hx⟩ | ⟨j, x, hx⟩
  · exact Or.inl ⟨φ x, back x α hx⟩
  · exact Or.inr ⟨j, φ x, back x _ (by rw [hx, map_mul, map_pow])⟩

end CFSG.HardMathSupport.Solomon.Coordinator
