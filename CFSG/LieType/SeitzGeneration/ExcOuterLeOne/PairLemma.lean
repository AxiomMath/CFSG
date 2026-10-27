module

public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.SL2Odd
public import CFSG.RankThree.PartOne.SEITZ6.G2Big
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

open CFSG.RankThree.PartOne.CTP
open CFSG.LieType.Chevalley

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section Pair

variable {K : Type} [Field K]

def diagConj (μ : K) (hμ : μ ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun A := ⟨!![μ, 0; 0, 1] * (A : Matrix (Fin 2) (Fin 2) K) * !![μ⁻¹, 0; 0, 1], by
    rw [Matrix.det_mul, Matrix.det_mul, A.2]
    simp [Matrix.det_fin_two, hμ]⟩
  map_one' := by
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hμ]
  map_mul' A B := by
    refine Subtype.ext ?_
    have hD : (!![μ⁻¹, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![μ, 0; 0, 1] = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hμ]
    show !![μ, 0; 0, 1] * ((A * B : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      !![μ⁻¹, 0; 0, 1] = (!![μ, 0; 0, 1] * (A : Matrix (Fin 2) (Fin 2) K) * !![μ⁻¹, 0; 0, 1]) *
        (!![μ, 0; 0, 1] * (B : Matrix (Fin 2) (Fin 2) K) * !![μ⁻¹, 0; 0, 1])
    rw [Matrix.SpecialLinearGroup.coe_mul,
      show (!![μ, 0; 0, 1] * (A : Matrix (Fin 2) (Fin 2) K) * !![μ⁻¹, 0; 0, 1]) *
        (!![μ, 0; 0, 1] * (B : Matrix (Fin 2) (Fin 2) K) * !![μ⁻¹, 0; 0, 1]) =
        !![μ, 0; 0, 1] * (A : Matrix (Fin 2) (Fin 2) K) *
          (!![μ⁻¹, 0; 0, 1] * !![μ, 0; 0, 1]) * (B : Matrix (Fin 2) (Fin 2) K) *
            !![μ⁻¹, 0; 0, 1] by simp only [mul_assoc], hD, mul_one]
    simp only [mul_assoc]

theorem diagConj_u2 (μ : K) (hμ : μ ≠ 0) (c : K) : diagConj μ hμ (u2 c) = u2 (μ * c) := by
  refine Subtype.ext ?_
  show !![μ, 0; 0, 1] * ((u2 c : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
    !![μ⁻¹, 0; 0, 1] = _
  rw [u2_coe, u2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hμ]

theorem diagConj_l2 (μ : K) (hμ : μ ≠ 0) (b : K) : diagConj μ hμ (l2 b) = l2 (μ⁻¹ * b) := by
  refine Subtype.ext ?_
  show !![μ, 0; 0, 1] * ((l2 b : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
    !![μ⁻¹, 0; 0, 1] = _
  rw [l2_coe, l2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hμ]
  ring

theorem sl2_hom_mem_of_pair {G : Type*} [Group G] [Finite K] (σ : K ≃+* K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hσ : orderOf σ = p) (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ))
    {H : Subgroup G} (ψ : Matrix.SpecialLinearGroup (Fin 2) K →* G) (μ₁ μ₂ : K) (hμ₁ : μ₁ ≠ 0)
    (hlam : μ₁ * μ₂ ∉ fixSubfield σ) (hu : ∀ c ∈ fixSubfield σ, ψ (u2 (μ₁ * c)) ∈ H)
    (hl : ∀ c ∈ fixSubfield σ, ψ (l2 (μ₂ * c)) ∈ H) (c : K) : ψ (u2 (μ₁ * c)) ∈ H := by
  classical
  set k := fixSubfield σ with hk
  have hK : Nat.card K = Nat.card k ^ p :=
    (CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow σ).trans (by rw [hσ])
  set M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := H.comap (ψ.comp (diagConj μ₁ hμ₁)) with hM
  have hmem : ∀ A, A ∈ M ↔ ψ (diagConj μ₁ hμ₁ A) ∈ H := fun A => Iff.rfl
  have hMu : ∀ c ∈ k, u2 c ∈ M := fun c hc => by
    rw [hmem, diagConj_u2]
    exact hu c hc
  have hMl : ∀ c ∈ k, l2 (c * (μ₁ * μ₂)) ∈ M := fun c hc => by
    rw [hmem, diagConj_l2]
    have : μ₁⁻¹ * (c * (μ₁ * μ₂)) = μ₂ * c := by field_simp
    rw [this]
    exact hl c hc
  have htop : M = ⊤ := by
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hℓ, -⟩ := FiniteField.card K (ringChar K)
    by_cases h2 : ringChar K = 2
    · haveI : CharP K 2 := by rw [← h2]; exact ringChar.charP K
      have h4 : 4 ∣ Nat.card k := hD.resolve_left (not_not.2 h2)
      exact CFSG.RankThree.PartOne.SEITZ2.sl2_eq_top_of_root_lines hp hp2 hK h4 hlam hMu hMl
    · haveI : CharP K (ringChar K) := ringChar.charP K
      have hr3 : 3 ≤ ringChar K := by
        have := hℓ.two_le
        omega
      exact CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.sl2_eq_top_of_root_lines_odd hr3 hp
        (Or.inr hp2) hK hlam hMu hMl
  have hA : u2 c ∈ M := htop ▸ Subgroup.mem_top _
  rw [hmem, diagConj_u2] at hA
  exact hA

end Pair

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
