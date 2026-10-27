module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootIrrRaise
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootIrrGood

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot

namespace CoreIrr

variable {K : Type} [Field K]

theorem good_top {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c) {N : AddSubgroup (Rv K)}
    (hΦ : N ≤ RPhi K σ) (hk : ∀ t : K, σ t = t → ∀ v ∈ N, t • v ∈ N)
    {n : Rv K} (hnN : n ∈ N) (hn0 : n ≠ 0) (hns : ∀ γ, γ ≠ topD → n γ = 0) :
    Good σ N topD := by
  intro c hc
  have hcσ : σ c = c := hc rho_top
  have hb : n topD ≠ 0 := fun h => hn0 (funext fun γ => by
    by_cases hγ : γ = topD
    · subst hγ
      exact h
    · exact hns γ hγ)
  have hbσ : σ (n topD) = n topD := by
    have := hΦ hnN topD
    rw [rho_top] at this
    exact this.symm
  have hfix : σ (c * (n topD)⁻¹) = c * (n topD)⁻¹ := by
    rw [map_mul, map_inv₀, hbσ, hcσ]
  have h1 := hk _ hfix n hnN
  have h2 : (c * (n topD)⁻¹) • n = orbVec σ topD c := by
    funext x
    by_cases hx : x = topD
    · subst hx
      simp [orbVec, hb]
    · simp [orbVec, hx, rho_top, hns x hx]
  rw [← h2]
  exact h1

end CoreIrr

theorem core_irreducible {K : Type} [Field K] (σ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c)
    (hσ1 : ∃ c, σ c ≠ c) (N : AddSubgroup (Rv K)) (hΦ : N ≤ RPhi K σ)
    (hk : ∀ t : K, σ t = t → ∀ v ∈ N, t • v ∈ N)
    (hX : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∀ c : K, (a = 2 → σ c = c) →
      ∀ v ∈ N, xorb K σ a c v ∈ N)
    (hY : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∀ c : K, (a = 2 → σ c = c) →
      ∀ v ∈ N, yorb K σ a c v ∈ N)
    (hW : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∃ ε : Dr → K,
      (∀ γ, ε γ = 1 ∨ ε γ = -1) ∧ ∀ v ∈ N, (fun γ => ε γ * v (reflD a γ)) ∈ N) :
    N = ⊥ ∨ RPhi K σ ≤ N := by
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨n, hnN, hn0, hns⟩ := CoreIrr.exists_top hσ1 hX hN
  exact CoreIrr.rphi_le_of_good hσσ
    (CoreIrr.good_all hσσ hΦ hY hW (CoreIrr.good_top hσσ hΦ hk hnN hn0 hns))

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
