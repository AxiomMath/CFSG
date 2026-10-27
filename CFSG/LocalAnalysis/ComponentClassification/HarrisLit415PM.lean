module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd414
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PBase
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem not_isMType [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (h39 : Harris82TheoremOneKProper)
    (hq : IsQuasisimple ↥(layer (MBar z₁))) (hz₁E : betaBar z₁ ∈ layer (MBar z₁)) :
    ¬ IsMType p ↥(layer (MBar z₁)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hME
  obtain ⟨J, hJ, hJE, g, hg, hgk⟩ := Setting46e.exists_pComponent_of_isQuasisimple z₁ hq
  have hz₁2 : z₁ ^ 2 = 1 := hD.fd.sq_z₁
  have hz₁J := Setting46e.beta_mem_of_mem_map hz₁2 (J := J) (by rw [hJE]; exact hz₁E)
  have hMJ := HarrisEnd.isMType_of_surjective g hg hgk
    (ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hJ) hME
  have hz₁ord : orderOf z₁ = 2 := orderOf_eq_prime hz₁2 hD.z₁_ne_one
  exact h39 X hnab hK hcat z₁ hz₁ord J hJ hz₁J p hD.hs.prime_p hD.hs.p_ne_two hMJ

end Data415B

end CFSG.ComponentClassification.HarrisLit
