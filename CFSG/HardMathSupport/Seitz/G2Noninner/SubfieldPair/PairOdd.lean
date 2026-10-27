module

public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.SL2Odd
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.BigCellOdd
public import CFSG.RankThree.PartOne.SEITZ6.G2Pair

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair

open Matrix CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.SEITZ6 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]

def diagConj (μ : K) (hμ : μ ≠ 0) : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 2) K where
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
    show !![μ, 0; 0, 1] * ((A * B : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
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
  show !![μ, 0; 0, 1] * ((u2 c : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
    !![μ⁻¹, 0; 0, 1] = _
  rw [u2_coe, u2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hμ]

theorem diagConj_l2 (μ : K) (hμ : μ ≠ 0) (b : K) : diagConj μ hμ (l2 b) = l2 (μ⁻¹ * b) := by
  refine Subtype.ext ?_
  show !![μ, 0; 0, 1] * ((l2 b : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
    !![μ⁻¹, 0; 0, 1] = _
  rw [l2_coe, l2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hμ]
  ring

theorem full_seven_of_pair_odd [Finite K] {r : ℕ} [CharP K r] (hr3 : 3 ≤ r)
    (k : Subfield K) {d : ℕ} (hd : d.Prime) (hrd : 5 ≤ r ∨ d ≠ 2) (hK : Nat.card K = Nat.card k ^ d)
    {H : Subgroup (adjointGroup .G2 K)} (g : adjointGroup .G2 K)
    (hH1 : ∀ c ∈ k, xp 7 c ∈ H) (hH2 : ∀ c ∈ k, g * xp 7 c * g⁻¹ ∈ H)
    (hlam : coordAt (rt 10) (g • rootVec .G2 K (rt 7)) ∉ k) : Full H 7 := by
  have hne0 : coordAt (rt 10) (g • rootVec .G2 K (rt 7)) ≠ 0 := fun h => hlam (h ▸ k.zero_mem)
  obtain ⟨ψ, μ₁, μ₂, h1, h2, hmu, hu, hl⟩ := bigCell_gen g hne0
  set M : Subgroup (SpecialLinearGroup (Fin 2) K) := H.comap (ψ.comp (diagConj μ₁ h1)) with hM
  have hmem : ∀ A, A ∈ M ↔ ψ (diagConj μ₁ h1 A) ∈ H := fun A => Iff.rfl
  have hMu : ∀ c ∈ k, u2 c ∈ M := fun c hc => by
    rw [hmem, diagConj_u2, ← sl2Upper_eq_u2, hu]
    exact hH1 c hc
  have hnk : μ₁ * μ₂ ∉ k := fun h => hlam (mem_of_mul_sign k hmu h)
  have hMl : ∀ c ∈ k, l2 (c * (μ₁ * μ₂)) ∈ M := fun c hc => by
    rw [hmem, diagConj_l2, ← sl2Lower_eq_l2]
    have : μ₁⁻¹ * (c * (μ₁ * μ₂)) = μ₂ * c := by field_simp
    rw [this, hl]
    exact hH2 c hc
  have htop : M = ⊤ := sl2_eq_top_of_root_lines_odd hr3 hd hrd hK hnk hMu hMl
  intro c
  have hA : u2 c ∈ M := htop ▸ Subgroup.mem_top _
  rw [hmem, diagConj_u2, ← sl2Upper_eq_u2, hu] at hA
  exact hA

end CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair
