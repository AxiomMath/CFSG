module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherTypePreserving

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module Subgroup ProjectiveGeometry

variable {K : Type*} [Field K] {n : ℕ}

theorem automorphism_generation [Finite K] (hn : 3 ≤ n) :
    standardAutGroup n K = ⊤ ∧
      ∀ α : MulAut (projectiveSL n K), ∃ (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
        α = conjAut n K A * fieldAut n K σ * dualAut n K ^ ε := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨-, -, -, -, -, -, haut⟩ := incidence_graph (K := K) p hn
  obtain ⟨hE, -, -, -, -⟩ := intrinsic_extremal_parabolics (K := K) p hn
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have hδδ : dualAut n K * dualAut n K = 1 := htrans.2.2.2.1
  have hmemL : ∀ L : Submodule K (Fin n → K), finrank K L = 1 →
      projStabilizer L ∈ extremalParabolics (projectiveSL n K) p := fun L hL => by
    rw [hE]
    exact Or.inl ⟨L, hL, rfl⟩
  have hform : ∀ α : MulAut (projectiveSL n K), ∃ (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ),
      ε ≤ 1 ∧ α = conjAut n K A * fieldAut n K σ * dualAut n K ^ ε := by
    intro α
    obtain ⟨Φ, hΦ, hpres⟩ := haut α
    rcases hpres with ⟨hpp, -⟩ | ⟨hph, -⟩
    ·
      obtain ⟨A, σ, hα⟩ := type_preserving_automorphisms hn α fun L hL => by
        obtain ⟨L', hL', hL'eq⟩ := hpp ⟨_, hmemL L hL⟩ ⟨L, hL, rfl⟩
        rw [hΦ] at hL'eq
        exact ⟨L', hL', hL'eq⟩
      exact ⟨A, σ, 0, zero_le_one, by rw [pow_zero, mul_one, hα]⟩
    ·
      obtain ⟨B, σ, hδα⟩ := type_preserving_automorphisms hn (dualAut n K * α) fun L hL => by
        obtain ⟨H, hH, hHeq⟩ := hph ⟨_, hmemL L hL⟩ ⟨L, hL, rfl⟩
        rw [hΦ] at hHeq
        refine ⟨dotOrth H, ?_, ?_⟩
        · rw [finrank_dotOrth, hH]
          omega
        · change (projStabilizer L).map ((dualAut n K : projectiveSL n K →* projectiveSL n K).comp
            (α : projectiveSL n K →* projectiveSL n K)) = _
          rw [← Subgroup.map_map, hHeq, htrans.2.2.2.2.2.2.2.2.1]
      refine ⟨GeneralLinearGroup.inverseTranspose B, σ, 1, le_rfl, ?_⟩
      have hα : α = dualAut n K * (conjAut n K B * fieldAut n K σ) := by
        rw [← hδα, ← mul_assoc, hδδ, one_mul]
      rw [hα, pow_one]
      symm
      calc conjAut n K (GeneralLinearGroup.inverseTranspose B) * fieldAut n K σ * dualAut n K
          _ = dualAut n K * conjAut n K B * dualAut n K *
              (dualAut n K * fieldAut n K σ * dualAut n K) * dualAut n K := by
            rw [htrans.2.2.2.2.1 B, htrans.2.2.2.2.2.1 σ]
          _ = dualAut n K * conjAut n K B * (dualAut n K * dualAut n K) * fieldAut n K σ *
              (dualAut n K * dualAut n K) := by group
          _ = dualAut n K * (conjAut n K B * fieldAut n K σ) := by
            rw [hδδ]
            group
  refine ⟨eq_top_iff.mpr fun α _ => ?_, hform⟩
  obtain ⟨A, σ, ε, -, rfl⟩ := hform α
  refine mul_mem (mul_mem ?_ ?_) (pow_mem (dualAut_mem_standardAutGroup) ε)
  · exact semilinearAutGroup_le_standardAutGroup
      (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
  · exact semilinearAutGroup_le_standardAutGroup (fieldAut_mem_semilinearAutGroup σ)

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
