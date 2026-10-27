module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductG0
public import CFSG.LocalAnalysis.EvenBN.G2.ProductEnd
public import CFSG.LocalAnalysis.EvenBN.G2.ProductEndFour
public import CFSG.LocalAnalysis.EvenBN.G2.ProductPair

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (diagonalHom)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_productConfig (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) :
    ∃ (G₀ : Subgroup G) (hcomm : ⁅G₀, G₀.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥),
      Group.IsPerfect ↥G₀ ∧ (diagonalHom G₀ t hcomm).range = L ∧
        normalizer ((yamadaR d t : Subgroup G) : Set G) ≤
          normalizer ((G₀ ⊔ G₀.map (MulAut.conj t⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨Λ₁, Λ₂, hL⟩ := h.exists_labelled hW d hK hQ hp
  obtain ⟨X, -, -, -, hP, -, -, -, -⟩ := h.exists_diagonalPair hW d hK hQ hp hL
  obtain ⟨hLr, hperf⟩ := X.range_and_isPerfect h hK4
  exact ⟨X.A₁ ⊔ X.A₂, X.commutator_sup_eq_bot hK4 h.htL h.t_mul_t, hperf, hLr,
    X.normalizer_yamadaR_le hW h hK hQ hP⟩


theorem false_of_productHyp (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) :
    False := by
  obtain ⟨G₀, hcomm, hperf, hLr, hN⟩ := h.exists_productConfig hW d hK hQ hp
  haveI := hperf
  rcases hQ.branch with h8 | ⟨hK4, -⟩
  · exact h.false_of_productConfig d hK h8 hcomm hLr hN
  · exact h.false_of_productConfig_four d hK hK4 hcomm hLr hN

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
