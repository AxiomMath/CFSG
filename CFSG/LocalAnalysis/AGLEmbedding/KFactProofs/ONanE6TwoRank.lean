module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanE6TwoSylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoRank
public import Certificates.Certificate9616
import CFSG.Adapters.TauCetiExceptional.EvenB1
import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.AGLEmbedding.E6Two

theorem rank_adjointGroup_E6 {K : Type} [Field K] [CharP K 2]
    [Finite (adjointGroup Tag.E6 K)]
    (hv : (Nat.card (adjointGroup Tag.E6 K)).factorization 3 = 6) :
    ∀ E : Subgroup (adjointGroup Tag.E6 K), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS, hrank⟩ := sylow_facts (K := K) e6SylowData Certificates.certificate9616
  have hS729 : Nat.card S = 729 := hS
  refine fun E hE => rank_le_of_sylow S (by rw [hv, hS729]; norm_num) ?_ E hE
  intro E' hE'S hE'
  have hlt := hrank E' hE'S hE'
  have hdvd : Nat.card E' ∣ 3 ^ 6 := by
    have := Subgroup.card_dvd_of_le hE'S
    rwa [hS729, show (729 : ℕ) = 3 ^ 6 by norm_num] at this
  obtain ⟨j, hj, hjE⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  rw [hjE] at hlt ⊢
  have hj5 : j < 5 := by
    by_contra hge
    have : 3 ^ 5 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hge)
    omega
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem e6TwoRankFour :
    E6TwoRankFour := by
  intro L _ _ d q hq hq1 hdq ⟨e⟩ E hE
  have hcard : Nat.card L = ordE6 (2 ^ 1) := by
    rw [Nat.card_congr e.toEquiv, card_catGroup_E6_even hq hdq, hq1]
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.E6 q := hdq
  have hm : ChevalleyExceptionalModel (CatGroup ⟨TauCeti.LieTypeIndex.E6 q, hv⟩)
      .E6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e6 q hv hq (MulEquiv.refl _)⟩
  obtain ⟨K, _, _, hK, ⟨ψ⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .E6 hm.2
  rw [hq, hq1] at hK
  have hK' : Nat.card K = 2 ^ 1 := by simpa using hK
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) hK'
  let φ : L ≃* adjointGroup Tag.E6 K := e.trans ψ
  have : Finite (adjointGroup Tag.E6 K) := Finite.of_equiv L φ.toEquiv
  have hG : Nat.card (adjointGroup Tag.E6 K) = ordE6 (2 ^ 1) := by
    rw [← Nat.card_congr φ.toEquiv, hcard]
  have hv3 : (Nat.card (adjointGroup Tag.E6 K)).factorization 3 = 6 := by
    rw [hG]
    have h : ordE6 (2 ^ 1) = 3 ^ 6 * 294707236655700377600 := by norm_num [ordE6]
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have h := rank_adjointGroup_E6 hv3 (E.map φ.toMonoidHom)
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E hE)
  rwa [Subgroup.card_map_of_injective φ.injective] at h

theorem jStarResidualE6TwoSix :
    JStarResidualE6TwoSix :=
  jStarResidualE6TwoSix_of_rank e6TwoRankFour

end CFSG.AGLEmbedding
