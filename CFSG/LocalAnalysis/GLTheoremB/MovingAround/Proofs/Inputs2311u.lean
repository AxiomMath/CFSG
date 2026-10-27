module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311m

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311u

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartTwo.Sec19 CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c

set_option linter.unusedSectionVars false

section Statements

@[expose] def TriOddA2Escape :
    Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ β : MulAut (C0 σ), β ^ 3 = 1 → β ∉ innerAut (C0 σ) → ¬ TriOddIsGLine σ β →
    ∀ x : C0 σ, β x = x → x ^ 3 = 1 →
      ∃ w : C0 σ, β w = w ∧ w * x = x * w ∧ ∀ y : C0 σ, β y = y →
        y ∈ Subgroup.closure ({y : C0 σ | β y = y ∧ ∃ n : ℕ, y ^ (ℓ ^ n) = 1} ∪ {w})

@[expose] def TriOddA2FixPGL :
    Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ β : MulAut (C0 σ), β ^ 3 = 1 → β ∉ innerAut (C0 σ) → ¬ TriOddIsGLine σ β →
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.IsPGLPiThree ↥(fixedSubgroup β) (ℓ ^ f)

end Statements

section Reduction

theorem five_le_pow_inputs2311u {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) :
    5 ≤ ℓ ^ f := by
  have h4 : ℓ ≠ 4 := fun h => by
    rw [h] at hℓ
    norm_num at hℓ
  have h5 : 5 ≤ ℓ := by
    have := hℓ.two_le
    omega
  calc 5 ≤ ℓ := h5
    _ = ℓ ^ 1 := (pow_one ℓ).symm
    _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf

theorem triOddA2Escape_of_fixPGL (h : TriOddA2FixPGL) : TriOddA2Escape := by
  intro ℓ f hℓ hℓ2 hℓ3 hf K _ _ hK σ hσ β hβ3 hβout hβG x hβx hx3
  exact (Inputs2311m.exists_rGen_escape_of_isPGLPiThree (five_le_pow_inputs2311u hℓ hℓ2 hℓ3 hf)
    (h ℓ f hℓ hℓ2 hℓ3 hf K hK σ hσ β hβ3 hβout hβG) hℓ hℓ3
    (dvd_pow_self ℓ (by omega : f ≠ 0)) hβx hx3).1

end Reduction

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311u
