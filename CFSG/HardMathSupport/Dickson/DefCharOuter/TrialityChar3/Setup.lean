module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.CoreStatement
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityThree
import CFSG.Adapters.TauCetiExceptional.TwistedD4Push
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem charP_three_of_card (K : Type) [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = (3 ^ f) ^ 3) : CharP K 3 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, hs, m, hsp, hm⟩ := FiniteField.card' K
  rw [← Nat.card_eq_fintype_card, hK] at hm
  have h1 : s ∣ (3 ^ f) ^ 3 := by
    rw [hm]
    exact dvd_pow_self s m.ne_zero
  have h2 : s = 3 :=
    (Nat.prime_dvd_prime_iff_eq hsp Nat.prime_three).1
      (hsp.dvd_of_dvd_pow (hsp.dvd_of_dvd_pow h1))
  rw [h2] at hs
  exact hs


private theorem exists_graphFixed_of_tauCeti (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) {S : Type} [Group S]
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) (hq3 : q.p = 3) :
    ∃ (f : ℕ) (_ : 1 ≤ f) (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (3 ^ f) ^ 3 ∧ (∀ c, σ c = c ^ (3 ^ f)) ∧
        Nonempty (S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨f, hfq⟩ : ∃ f, q.exponent = f := ⟨_, rfl⟩
  have hf : 1 ≤ f := by
    rw [← hfq]
    exact q.exponent_pos
  have hqcard : q.card = 3 ^ f := by
    rw [TauCeti.PrimePower.card_def, hq3, hfq]
  have hp2 : q.p ≠ 2 := by
    rw [hq3]
    norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK₀ : Nat.card (GaloisField 3 (3 * f)) = (3 ^ f) ^ 3 := by
    rw [GaloisField.card 3 (3 * f) (by omega), ← pow_mul, mul_comm]
  have hσ₀ : ∀ c : GaloisField 3 (3 * f),
      iterateFrobenius (GaloisField 3 (3 * f)) 3 f c = c ^ 3 ^ f := fun c => by
    rw [iterateFrobenius_def]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hp2
    (GaloisField 3 (3 * f)) (by rw [hK₀, hqcard]; rfl)
    (iterateFrobenius (GaloisField 3 (3 * f)) 3 f)
    (fun c => by rw [hqcard]; exact hσ₀ c)
  have hmodel : TwistedChevalleyModel S TwistTag.D4 (3 ^ f) := by
    unfold TwistedChevalleyModel
    exact ⟨GaloisField 3 (3 * f), inferInstance, inferInstance, hK₀,
      iterateFrobenius (GaloisField 3 (3 * f)) 3 f, hσ₀, ⟨e.trans b.symm⟩⟩
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e₁⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_three hf hmodel
  exact ⟨f, hf, K, inferInstance, inferInstance, σ, hK, hσ, ⟨e₁⟩⟩

theorem trialityThreeOuter_of_core (hcore : TrialityThreeCore) :
    CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityThreeOuter := by
  intro q hv S _ _ _ _ e hq3 β hβ hout
  obtain ⟨f, hf, K, _, _, σ, hK, hσ, ⟨e₁⟩⟩ := exists_graphFixed_of_tauCeti q hv e hq3
  haveI : CharP K 3 := charP_three_of_card K hK
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Finite.of_equiv S e₁.toEquiv
  have hαp : MulAut.congr e₁ β ^ 3 = 1 := by
    rw [← map_pow, hβ, map_one]
  have hαin : MulAut.congr e₁ β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rintro ⟨g, hg⟩
    apply hout (e₁.symm g)
    apply (MulAut.congr e₁).injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e₁.apply_symm_apply]
    exact hg
  rcases DefCharGoodPlus.good (hcore f hf K hK σ hσ (MulAut.congr e₁ β) hαp hαin) with h | h
  · exact .inl (LieSemisimple.perfectInLayer_of_congr e₁ β h)
  · refine .inr ?_
    have hle := map_glaPPrimeCoreOf_fixSubgroup_le (e₁ : S →* _)
      (by rw [(MonoidHom.ker_eq_bot_iff _).2 e₁.injective]; exact bot_le) β (MulAut.congr e₁ β)
      (fun k => by
        change e₁ (β k) = e₁ (β (e₁.symm (e₁ k)))
        rw [MulEquiv.symm_apply_apply]) e₁.surjective Nat.prime_three
    rw [h, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ e₁.injective).1 hle

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
