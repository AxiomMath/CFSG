module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsOuterDiag
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

theorem cfL2Cent : GSThmB.CFL2Cent := by
  intro Y _ _ p f hp hp2 hf _ hY D₀ ⟨R, hR⟩ σ hσ hσD τ ζ hτ2 hζ2 hτs hζs hτD hζD hζ1
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have hodd := isOddPrimePower_of hp hp2 hf hF
  obtain ⟨hs1, hsL⟩ := outerDiag_transport hodd e σ hσ
  have hcomm : ∀ α : MulAut Y, (∀ d ∈ D₀, α d = d) →
      ∀ d ∈ ((sylowMap e R : Sylow 2 (PSL2 F)) : Subgroup (PSL2 F)),
        autEquiv e α * incl F d = incl F d * autEquiv e α := by
    intro α hα d hd
    rw [coe_sylowMap, hR] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    exact (apply_eq_iff_commute e α d₀).mp (hα d₀ hd₀)
  have h2 : ∀ α : MulAut Y, (∃ k : ℕ, α ^ 2 ^ k = 1) → ∃ k : ℕ, autEquiv e α ^ 2 ^ k = 1 := by
    rintro α ⟨k, hk⟩
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hres := l2Cent_model hp hp2 hf hF (sylowMap e R) (autEquiv e σ) hs1 hsL
    (by
      intro d hd
      rw [coe_sylowMap, hR] at hd ⊢
      obtain ⟨d₀, hd₀, rfl⟩ := hd
      refine ⟨e (σ d₀), ⟨σ d₀, ?_, rfl⟩, ?_⟩
      · rw [← hσD]
        exact ⟨d₀, hd₀, rfl⟩
      · rw [conj_incl]
        exact congrArg (incl F) (semilinearAction_autEquiv_apply e σ d₀).symm)
    (autEquiv e τ) (autEquiv e ζ) (h2 τ hτ2) (h2 ζ hζ2)
    (by rw [← map_mul, ← map_mul, hτs]) (by rw [← map_mul, ← map_mul, hζs])
    (hcomm τ hτD) (hcomm ζ hζD)
    (fun h => hζ1 ((autEquiv e).injective (h.trans (map_one _).symm)))
  rcases hres with h | h
  · exact Or.inl ((autEquiv e).injective (h.trans (map_one _).symm))
  · exact Or.inr ((autEquiv e).injective h)

end CFSG.ComponentClassification.AutL2Facts
