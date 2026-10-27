module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddBigCell
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.PairOdd

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ8
  CFSG.RankThree.PartOne.SEITZ2 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6
  CFSG.RankThree.PartOne.CTP

variable {K : Type} [Field K]

section Pair

variable [Finite K] {σ : K →+* K}

theorem full_h_of_pair_odd {r : ℕ} [CharP K r] (hr3 : 3 ≤ r) (hσ : ∀ c, σ (σ (σ c)) = c)
    (F0 : Subfield (fixedField σ)) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hF : Nat.card (fixedField σ) = Nat.card F0 ^ d)
    {H : Subgroup (twistedGroup σ)} (g : twistedGroup σ)
    (hH1 : ∀ c ∈ F0, psiB σ hσ (sl2Upper c) ∈ H)
    (hH2 : ∀ c ∈ F0, g * psiB σ hσ (sl2Upper c) * g⁻¹ ∈ H)
    (lam : fixedField σ)
    (hlam_eq : (lam : K) =
      coordAt (d4Root 23) ((g : adjointGroup d4 K) • (rv 22 : RootModule d4 K)))
    (hlam : lam ∉ F0) : ∀ c : fixedField σ, psiB σ hσ (sl2Upper c) ∈ H := by
  have hne0 : coordAt (d4Root 23) ((g : adjointGroup d4 K) • (rv 22 : RootModule d4 K)) ≠ 0 := by
    rw [← hlam_eq]
    intro h
    exact hlam (by
      have : lam = 0 := Subtype.ext h
      rw [this]
      exact F0.zero_mem)
  obtain ⟨ψ, μ₁, μ₂, h1, h2, ⟨ε, hε, hmu⟩, hu, hl⟩ := bigCell_tw_odd hσ g hne0
  have hmu' : μ₁ * μ₂ = lam ∨ μ₁ * μ₂ = -lam := by
    rcases hε with rfl | rfl
    · left
      refine Subtype.ext ?_
      show (μ₁ : K) * (μ₂ : K) = (lam : K)
      rw [hmu, hlam_eq, one_mul]
    · right
      refine Subtype.ext ?_
      show ((μ₁ * μ₂ : fixedField σ) : K) = -(lam : K)
      rw [show ((μ₁ * μ₂ : fixedField σ) : K) = (μ₁ : K) * (μ₂ : K) from rfl, hmu, hlam_eq]
      ring
  set M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) :=
    H.comap (ψ.comp (G2Noninner.SubfieldPair.diagConj μ₁ h1)) with hM
  have hmem : ∀ A, A ∈ M ↔ ψ (G2Noninner.SubfieldPair.diagConj μ₁ h1 A) ∈ H := fun A => Iff.rfl
  have hMu : ∀ c ∈ F0, u2 c ∈ M := fun c hc => by
    rw [hmem, G2Noninner.SubfieldPair.diagConj_u2, ← sl2Upper_eq_u2, hu]
    exact hH1 c hc
  have hnk : μ₁ * μ₂ ∉ F0 := fun h =>
    hlam (G2Noninner.SubfieldPair.mem_of_mul_sign F0 hmu' h)
  have hMl : ∀ c ∈ F0, l2 (c * (μ₁ * μ₂)) ∈ M := fun c hc => by
    rw [hmem, G2Noninner.SubfieldPair.diagConj_l2, ← sl2Lower_eq_l2]
    have : μ₁⁻¹ * (c * (μ₁ * μ₂)) = μ₂ * c := by field_simp
    rw [this, hl]
    exact hH2 c hc
  have : Finite (fixedField σ) := Subtype.finite
  have htop : M = ⊤ :=
    G2Noninner.SubfieldPair.sl2_eq_top_of_root_lines_odd (r := r) hr3 hd (Or.inr hd2) hF hnk
      hMu hMl
  intro c
  have hA : u2 c ∈ M := htop ▸ Subgroup.mem_top _
  rw [hmem, G2Noninner.SubfieldPair.diagConj_u2, ← sl2Upper_eq_u2, hu] at hA
  exact hA

end Pair

end CFSG.HardMathSupport.Seitz.TrialityOdd
