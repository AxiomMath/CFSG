module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageModels
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactorExcInputs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotientMin
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedD4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedE6
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviBorelTop

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalInvolution.ModelFacts.ChevAut
  CFSG.LieType.Steinberg.Minuscule

section G2


theorem gomiChevLeviPackageModel_g2 (n : ℕ) : GomiChevLeviPackageModel .G2 n := by
  refine gomiChevLeviPackageModel_of_gomiLeviPackageTop ?_
  intro X _ _ f hm
  rcases hm with ⟨hcl, -⟩ | ⟨-, -, hm⟩ | ⟨-, hree, -⟩ | ⟨-, hb2, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, hf, -⟩ := hm.1
    obtain ⟨F, hF, hFfin, hcard, ⟨e⟩⟩ := hm.2
    have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
    have : Finite ↥(adjointGroup .G2 F) := generated_group_finite .G2 F
    exact gomiLeviPackageTop_of_borelQuotient (borelQuotient_g2 e)
      (gomiLeviFactors_of_rank_le_two
        (D := CFSG.LieType.Steinberg.Adjoint.g2Datum F) (Nat.le_refl 2))
  · exact absurd hree (by decide)
  · exact absurd hb2 (by decide)

end G2

section F4E8


theorem gomiChevLeviPackageModel_f4 (hF4 : GomiLeviFactorsF4)
    (n : ℕ) : GomiChevLeviPackageModel .F4 n := by
  refine gomiChevLeviPackageModel_of_gomiLeviPackageTop ?_
  intro X _ _ f hm
  rcases hm with ⟨hcl, -⟩ | ⟨-, -, hm⟩ | ⟨-, hree, -⟩ | ⟨-, hb2, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, hf, -⟩ := hm.1
    obtain ⟨F, hF, hFfin, hcard, ⟨e⟩⟩ := hm.2
    have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
    have : Finite ↥(adjointGroup .F4 F) := generated_group_finite .F4 F
    exact gomiLeviPackageTop_of_borelQuotient (borelQuotient_f4 e) (hF4 F)
  · exact absurd hree (by decide)
  · exact absurd hb2 (by decide)

theorem gomiChevLeviPackageModel_e8 (hE8 : GomiLeviFactorsE8)
    (n : ℕ) : GomiChevLeviPackageModel .E8 n := by
  refine gomiChevLeviPackageModel_of_gomiLeviPackageTop ?_
  intro X _ _ f hm
  rcases hm with ⟨hcl, -⟩ | ⟨-, -, hm⟩ | ⟨-, hree, -⟩ | ⟨-, hb2, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, hf, -⟩ := hm.1
    obtain ⟨F, hF, hFfin, hcard, ⟨e⟩⟩ := hm.2
    have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
    have : Finite ↥(adjointGroup .E8 F) := generated_group_finite .E8 F
    exact gomiLeviPackageTop_of_borelQuotient (borelQuotient_e8 e) (hE8 F)
  · exact absurd hree (by decide)
  · exact absurd hb2 (by decide)

end F4E8

section E6


theorem gomiChevLeviPackageModel_e6 (hE6 : GomiLeviFactorsE6)
    (n : ℕ) : GomiChevLeviPackageModel .E6 n := by
  refine gomiChevLeviPackageModel_of_gomiLeviPackageTop ?_
  intro X _ _ f hm
  rcases hm with ⟨hcl, -⟩ | ⟨-, -, hm⟩ | ⟨-, hree, -⟩ | ⟨-, hb2, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, hf, -⟩ := hm.1
    obtain ⟨F, hF, hFfin, hcard, ⟨e⟩⟩ := hm.2
    have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
    have : Finite ↥(e6Data_valid.minGroup F) := finite_minGroup e6Data_valid F
    exact gomiLeviPackageTop_of_borelQuotient (borelQuotient_e6 e) (hE6 F)
  · exact absurd hree (by decide)
  · exact absurd hb2 (by decide)

end E6

section E7


theorem gomiChevLeviPackageModel_e7 (hE7 : GomiLeviFactorsE7)
    (n : ℕ) : GomiChevLeviPackageModel .E7 n := by
  refine gomiChevLeviPackageModel_of_gomiLeviPackageTop ?_
  intro X _ _ f hm
  rcases hm with ⟨hcl, -⟩ | ⟨-, -, hm⟩ | ⟨-, hree, -⟩ | ⟨-, hb2, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, hf, -⟩ := hm.1
    obtain ⟨F, hF, hFfin, hcard, ⟨e⟩⟩ := hm.2
    have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
    have : Finite ↥(e7Data_valid.minGroup F) := finite_minGroup e7Data_valid F
    exact gomiLeviPackageTop_of_borelQuotient (borelQuotient_e7 e) (hE7 F)
  · exact absurd hree (by decide)
  · exact absurd hb2 (by decide)

end E7

section TrialityD4


theorem gomiChevLeviPackageModel_trialityD4 (n : ℕ) : GomiChevLeviPackageModel .trialityD4 n := by
  refine gomiChevLeviPackageModel_of_gomiLeviPackageTop ?_
  intro X _ _ f hm
  rcases hm with ⟨hcl, -⟩ | ⟨-, -, hm⟩ | ⟨-, hree, -⟩ | ⟨-, hb2, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, hf, -⟩ := hm.1
    obtain ⟨F, hF, hFfin, hcard, σ, hσ, ⟨e⟩⟩ := hm.2
    have hK' : Nat.card F = (2 ^ f) ^ 3 := hcard
    have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two
      (show 1 ≤ f * 3 by omega)
      (show Nat.card F = 2 ^ (f * 3) by rw [hK', pow_mul])
    have h2le : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have : Finite ↥(CFSG.LieType.Steinberg.TwistedD4.twistedGroup (K := F) σ) := Subtype.finite
    exact gomiLeviPackageTop_of_borelQuotient (borelQuotient_d4tw h2le hK' hσ e)
      (gomiLeviFactors_of_rank_le_two
        (D := CFSG.LieType.Steinberg.TwistedD4.twistedDatum σ) (Nat.le_refl 2))
  · exact absurd hree (by decide)
  · exact absurd hb2 (by decide)

end TrialityD4

section TwistedE6


theorem gomiChevLeviPackageModel_twistedE6 (hE6tw : GomiLeviFactorsTwistedE6)
    (n : ℕ) : GomiChevLeviPackageModel .twistedE6 n := by
  refine gomiChevLeviPackageModel_of_gomiLeviPackageTop ?_
  intro X _ _ f hm
  rcases hm with ⟨hcl, -⟩ | ⟨-, -, hm⟩ | ⟨-, hree, -⟩ | ⟨-, hb2, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, hf, -⟩ := hm.1
    obtain ⟨F, hF, hFfin, hcard, σ, hσ, ⟨e⟩⟩ := hm.2
    have hK' : Nat.card F = (2 ^ f) ^ 2 := hcard
    have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two
      (show 1 ≤ f * 2 by omega)
      (show Nat.card F = 2 ^ (f * 2) by rw [hK', pow_mul])
    have h2le : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hK4 : 4 ≤ Nat.card F := by
      rw [hK']
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left h2le 2
    have hθ := involutive_of_card (k := F) (θ := σ) (q := 2 ^ f) hK' hσ
    have : Finite ↥(e6Data_valid.minGroup F) := finite_minGroup e6Data_valid F
    have : Finite ↥(CFSG.LieType.Steinberg.TwistedE6.fixedGroup F σ) := Subtype.finite
    exact gomiLeviPackageTop_of_borelQuotient (borelQuotient_e6tw hθ hK4 hK' hσ e)
      (hE6tw F σ (2 ^ f) hK' hσ)
  · exact absurd hree (by decide)
  · exact absurd hb2 (by decide)

end TwistedE6

end CFSG.GroupTheory
