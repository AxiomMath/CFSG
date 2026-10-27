module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeExcBase
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcE
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.RankFourTheoremC
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.I294CrossLargeExc

@[expose] def I294CrossLargeIsTwistedE6 : TauCeti.LieTypeIndex → Prop
  | .twistedE6 _ => True
  | _ => False

section TwistedE6


private theorem abelOrRankFour_twistedE6_five {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    [Finite ↥(twistedE6RootGroup K σ)] (hpℓ : 5 ≠ ℓ) :
    AbelOrRankFour 5 ↥(twistedE6RootGroup K σ) := by
  have hp : Nat.Prime 5 := by norm_num
  have hpq : ¬ 5 ∣ ℓ ^ f := fun h =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨e, he⟩ : ∃ e, orderOf (((ℓ ^ f : ℕ)) : ZMod 5) = e := ⟨_, rfl⟩
  have hd : e ∣ 4 := he ▸ orderOf_natCast_dvd_pred hp hpq
  rcases cases_dvd_four hd with rfl | rfl | rfl
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_twistedE6_one hℓ hf K hK σ hσ hp (by norm_num) he
    exact AbelOrRankFour.of_elemAbelian hp hE hc (by norm_num)
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_twistedE6_two hℓ hf K hK σ hσ hp (by norm_num) he
    exact AbelOrRankFour.of_elemAbelian hp hE hc (by norm_num)
  · exact AbelOrRankFour.of_sylowTorus (sylowTorus_twistedE6_four hℓ hf K hK σ hσ hp he)

end TwistedE6

section Catalogue


theorem abelOrRankFour_twistedE6_of_seven_le {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : q.p ≠ p) {L : Type} [Group L] [Finite L]
    (e : L ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) : AbelOrRankFour p L := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hm : 0 < TwistTag.E6.order := by decide
  have hK : Nat.card (GaloisField q.p (q.exponent * TwistTag.E6.order)) =
      q.card ^ TwistTag.E6.order := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' hm.ne'),
      TauCeti.PrimePower.card_def, pow_mul]
  let σ := iterateFrobenius (GaloisField q.p (q.exponent * TwistTag.E6.order)) q.p q.exponent
  have hσ : ∀ x, σ x = x ^ q.card := fun x => by
    rw [iterateFrobenius_def, TauCeti.PrimePower.card_def]
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv _ hK σ hσ
  have hpK : ¬ p ∣ Nat.card (GaloisField q.p (q.exponent * TwistTag.E6.order)) := by
    rw [hK, TauCeti.PrimePower.card_def, ← pow_mul]
    exact crossExc_not_dvd_pow_of_ne hp q.prime_p hpq
  exact AbelOrRankFour.of_sylow_comm
    (isMulCommutative_sylow_of_mulEquiv (e.trans φ.symm)
      (fun R => isMulCommutative_sylow_derivedCentralQuotient inf_le_left hp
        (crossExc_not_dvd_card_weylGroup_E6 hp hp7) hpK R))

theorem i294CrossLargePrimeOn_twistedE6 : I294CrossLargePrimeOn I294CrossLargeIsTwistedE6 := by
  refine i294CrossLargePrimeOn_of_abelOrRankFour ?_
  intro p hp h5 ⟨i, hv⟩ hφ hd L _ _ ⟨e⟩
  cases i with
  | twistedE6 q =>
    have hpq : q.p ≠ p := by simpa [TauCeti.LieTypeIndex.characteristic_twistedE6] using hd
    by_cases h7 : 7 ≤ p
    · exact abelOrRankFour_twistedE6_of_seven_le hv hp h7 hpq e
    · obtain rfl : p = 5 := eq_five_of_lt_seven hp h5 (by omega)
      obtain ⟨K, _, σ, hK, hσ, ⟨φ⟩⟩ := exists_catEquiv_twistedE6 q hv
      haveI : Finite ↥(twistedE6RootGroup K σ) := Finite.of_equiv L (e.trans φ).toEquiv
      exact AbelOrRankFour.of_mulEquiv hp (e.trans φ)
        (abelOrRankFour_twistedE6_five q.prime_p q.exponent_pos K hK σ hσ hpq.symm)
  | _ => exact (hφ : False).elim

end Catalogue

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
