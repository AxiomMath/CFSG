module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductDecomp
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductG0

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common

section Statements

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem exists_labelled (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    ∃ K K₁ : Subgroup G, Labelled d t K K₁ := by
  obtain ⟨K, hK, -⟩ := A1_components h d hp
  obtain ⟨K₁, hK₁⟩ := D6_product h d hp
  obtain ⟨K₁', hL⟩ := F1_labelled h d hp hK hK₁
  exact ⟨K, K₁', hL⟩

theorem exists_diagonalPair (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) :
    ∃ X : DiagonalPair d t, yamadaP d t = X.P₀ ⊔ X.P₀ᵍ[t] ∧ X.A₁ ⊓ X.A₁ᵍ[t] = ⊥ := by
  obtain ⟨K, K₁, hL⟩ := exists_labelled h d hp
  obtain ⟨X, -, -, -, -, ⟨-, hA₁, -⟩, ⟨hP, -, -⟩⟩ := H1_decomposition h d hp hL
  exact ⟨X, hP, hA₁⟩

theorem exists_productConfig (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) :
    ∃ (G₀ : Subgroup G) (hcomm : ⁅G₀, G₀.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥),
      Group.IsPerfect ↥G₀ ∧ (diagonalHom G₀ t hcomm).range = L ∧
        normalizer ((yamadaR d t : Subgroup G) : Set G) ≤
          normalizer ((G₀ ⊔ G₀.map (MulAut.conj t⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  obtain ⟨X, hP, -⟩ := exists_diagonalPair h d hp
  obtain ⟨hL, hperf⟩ := X.range_and_isPerfect h hp.two_le
  exact ⟨X.A₁ ⊔ X.A₂, X.commutator_sup_eq_bot h.htL h.t_mul_t, hperf, hL,
    J6_normalizer h d hp X hP⟩

end Statements

end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
