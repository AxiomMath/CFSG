module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.NoE27L3U3
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ThreeRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank
public import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.LieType.Chevalley (graphFixedRootGroup)

open CFSG.LieType.Ree (ReeTag)


section G2


theorem noE27_adjointG2 (K : Type) [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K) :
    NoE27 ↥(adjointGroup Tag.G2 K) := by
  rintro ⟨E, hE, hc⟩
  have h9 :=
    CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.card_le_nine_of_isElemAbelian_three
      K h3 E hE
  norm_num at h9
  omega

theorem noE27_g2Low : NoE27At FamG2Low := by
  intro P _ _ t n p f hadm ht hF hm
  obtain ⟨rfl, hp3⟩ := hF
  have hU : UntwistedChevalleyModel P .G2 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_adjointGroup_of_untwisted hU
  refine NoE27.of_mulEquiv θ.symm (noE27_adjointG2 F ?_)
  rw [hFcard]
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.not_three_dvd_prime_pow hadm.1 hp3 f

end G2

section TriD4


theorem noE27_graphFixedD4 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ TwistTag.D4.order) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ ℓ ^ f) : NoE27 ↥(graphFixedRootGroup TwistTag.D4 K σ) := by
  rintro ⟨E, hE, hc⟩
  have h9 := CFSG.HardMathSupport.Timmesfeld.CrossChar.card_le_nine_of_graphFixedRootGroup_ne_three
    hℓ hℓ3 hf hK hσ E hE
  omega

theorem noE27_triD4Low : NoE27At FamTriD4Low := by
  intro P _ _ t n p f hadm ht hF hm
  obtain ⟨rfl, hp3⟩ := hF
  have hexc : ChevalleyExceptionalModel P .trialityD4 p f := by
    rcases hm with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
    · exact absurd hcl (by decide)
    · exact hexc
    · exact absurd hree (by decide)
    · exact absurd h (by decide)
  obtain ⟨hadm', hmod⟩ := hexc
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hadm'.1
      hadm'.2.1 hmod
  exact NoE27.of_mulEquiv e.symm (noE27_graphFixedD4 hadm'.1 hp3 hadm'.2.1 hK hσ)

end TriD4

section ReeF4


theorem noE27_reeGamma (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : NoE27 ↥(ReeTag.F4.reeGamma K a) := by
  rintro ⟨E, hE, hc⟩
  have h9 :=
    CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma a K hK E hE
  omega

theorem noE27_reeF4 : NoE27At FamReeF4 := by
  intro P _ _ t n p f hadm ht hF hm
  obtain rfl := hF
  obtain ⟨hn0, hℓ, hfodd, hf3⟩ := hadm.2.2
  subst hn0
  subst hℓ
  have hR : ReeTitsModel P .twistedF4 2 f := by
    rcases hm with ⟨ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, -, h⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
    · exact h
    · exact absurd ht' (by decide)
  obtain ⟨-, -, -, -, -, hiso⟩ := ReeTag.large_Ree_model_Schreier P 2 f hR
  obtain ⟨-, a, hfa, K, _, _, hK, ⟨e⟩⟩ := hR
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  exact NoE27.of_mulEquiv E (noE27_reeGamma a K (by rw [← hfa]; exact hK))

end ReeF4

end CFSG.HardMathSupport.Dickson.Sec6.I1431
