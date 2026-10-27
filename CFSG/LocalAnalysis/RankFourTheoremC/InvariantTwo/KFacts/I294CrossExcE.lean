module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamilies
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcToral
import CFSG.RankThree.E6.LargePrimeStabilizers
import CFSG.RankThree.PartOne.KE.EDualStabilizer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC Subgroup CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def CrossAtPrime (d : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  p.Prime → 5 ≤ p → d.1.characteristic ≠ p →
    (∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ¬ IsLinearOrUnitaryAt p L →
      CFSG.Open.pRank p (⊤ : Subgroup L) = 2 → ∀ P : Sylow p L, IsMulCommutative (P : Subgroup L)) ∧
    (∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ¬ IsLinearOrUnitaryAt p L →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) →
      ∀ y : L, orderOf y = p → 3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set L)))

theorem crossAt_of_crossAtPrime {d : TauCeti.ValidLieTypeIndex} (h : ∀ p, CrossAtPrime d p) :
    CrossAt d :=
  ⟨fun p hp hp5 hdp L _ _ hs he hl h2 => ((h p hp hp5 hdp).1 L hs he hl h2),
    fun p hp hp5 hdp L _ _ hs he hl h3 y hy => ((h p hp hp5 hdp).2 L hs he hl h3 y hy)⟩

theorem crossAtPrime_of_sylowAbelian {d : TauCeti.ValidLieTypeIndex} {p : ℕ}
    (hab : p.Prime → 5 ≤ p → d.1.characteristic ≠ p →
      ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
        Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ P : Sylow p L, IsMulCommutative (P : Subgroup L)) :
    CrossAtPrime d p := by
  intro hp hp5 hdp
  refine ⟨fun L _ _ hs he _ _ => hab hp hp5 hdp L hs he, ?_⟩
  intro L _ _ hs he _ h3 y hy
  haveI : Fact p.Prime := ⟨hp⟩
  exact three_le_pRank_centralizer_of_sylow_abelian (hab hp hp5 hdp L hs he) h3
    (hy ▸ pow_orderOf_eq_one y)

theorem crossExc_seven_le_of_ne_five {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ≠ 5) :
    7 ≤ p := by
  by_contra hlt
  have h6 : p = 6 := by omega
  exact absurd (h6 ▸ hp) (by decide)

theorem crossExc_eleven_le_of_ne_five_seven {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : p ≠ 5)
    (h' : p ≠ 7) : 11 ≤ p := by
  have h7 := crossExc_seven_le_of_ne_five hp h5 h
  by_contra hlt
  have : p = 8 ∨ p = 9 ∨ p = 10 := by omega
  rcases this with rfl | rfl | rfl <;> exact absurd hp (by decide)

theorem crossExc_not_dvd_card_weylGroup_E6
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬ p ∣ Nat.card (WeylGroup Tag.E6) := by
  rw [CFSG.RankThree.E6.card_weylGroup_E6, show (51840 : ℕ) = 2 ^ 7 * 3 ^ 4 * 5 from rfl]
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact crossExc_not_dvd_two_pow_mul_three_pow hp (by omega) 7 4 h
  · have := Nat.le_of_dvd (by norm_num) h
    omega

section Untwisted


theorem crossAtPrime_of_untwisted {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hch : ∀ q, (c q).characteristic = q.p) {q : TauCeti.PrimePower} (hv : (c q).Valid) {p : ℕ}
    (hW : p.Prime → ¬ p ∣ Nat.card (WeylGroup τ)) :
    CrossAtPrime ⟨c q, hv⟩ p := by
  refine crossAtPrime_of_sylowAbelian fun hp hp5 hdp L _ _ hs ⟨e⟩ P => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hdp' : q.p ≠ p := by rw [← hch q]; exact hdp
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨φ⟩ := hB q hv (GaloisField q.p q.exponent) hK
  have hpK : ¬ p ∣ Nat.card (GaloisField q.p q.exponent) := by
    rw [hK, TauCeti.PrimePower.card_def]
    exact crossExc_not_dvd_pow_of_ne hp q.prime_p hdp'
  exact isMulCommutative_sylow_of_mulEquiv (e.trans φ.symm)
    (isMulCommutative_sylow_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      (fun S => isMulCommutative_sylow_adjointGroup hp (hW hp) hpK S)) P

theorem crossAtPrime_twistedE6 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp7 : 7 ≤ p) :
    CrossAtPrime ⟨.twistedE6 q, hv⟩ p := by
  refine crossAtPrime_of_sylowAbelian fun hp hp5 hdp L _ _ hs ⟨e⟩ P => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hdp' : q.p ≠ p := by simpa using hdp
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
    exact crossExc_not_dvd_pow_of_ne hp q.prime_p hdp'
  exact isMulCommutative_sylow_of_mulEquiv (e.trans φ.symm)
    (fun R => isMulCommutative_sylow_derivedCentralQuotient inf_le_left hp
      (crossExc_not_dvd_card_weylGroup_E6 hp hp7) hpK R) P

end Untwisted

@[expose] def CrossFamE6Five : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid),
    CrossAtPrime ⟨.E6 q, hv⟩ 5

@[expose] def CrossFamTwistedE6Five : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid),
    CrossAtPrime ⟨.twistedE6 q, hv⟩ 5

@[expose] def CrossFamE7Small : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid),
    CrossAtPrime ⟨.E7 q, hv⟩ 5 ∧ CrossAtPrime ⟨.E7 q, hv⟩ 7

@[expose] def CrossFamE8Small : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid),
    CrossAtPrime ⟨.E8 q, hv⟩ 5 ∧ CrossAtPrime ⟨.E8 q, hv⟩ 7

section Families


theorem crossFamE6_of_five (h : CrossFamE6Five) : CrossFamE6 := fun q hv =>
  crossAt_of_crossAtPrime fun p => by
    by_cases hp5 : p = 5
    · subst hp5
      exact h q hv
    · intro hp hp5' hdp
      exact crossAtPrime_of_untwisted CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6
        TauCeti.LieTypeIndex.characteristic_E6 hv (fun hp => crossExc_not_dvd_card_weylGroup_E6 hp
          (crossExc_seven_le_of_ne_five hp hp5' hp5)) hp hp5' hdp

theorem crossFamTwistedE6_of_five (h : CrossFamTwistedE6Five) : CrossFamTwistedE6 := fun q hv =>
  crossAt_of_crossAtPrime fun p => by
    by_cases hp5 : p = 5
    · subst hp5
      exact h q hv
    · intro hp hp5' hdp
      exact crossAtPrime_twistedE6 hv (crossExc_seven_le_of_ne_five hp hp5' hp5) hp hp5' hdp

theorem crossFamE7_of_small (h : CrossFamE7Small) : CrossFamE7 := fun q hv =>
  crossAt_of_crossAtPrime fun p => by
    by_cases hp5 : p = 5
    · subst hp5
      exact (h q hv).1
    by_cases hp7 : p = 7
    · subst hp7
      exact (h q hv).2
    · intro hp hp5' hdp
      exact crossAtPrime_of_untwisted CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7
        TauCeti.LieTypeIndex.characteristic_E7 hv
        (fun hp => CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp
          (by have := crossExc_eleven_le_of_ne_five_seven hp hp5' hp5 hp7; omega)
          (Or.inr (Or.inl rfl))) hp hp5' hdp

theorem crossFamE8_of_small (h : CrossFamE8Small) : CrossFamE8 := fun q hv =>
  crossAt_of_crossAtPrime fun p => by
    by_cases hp5 : p = 5
    · subst hp5
      exact (h q hv).1
    by_cases hp7 : p = 7
    · subst hp7
      exact (h q hv).2
    · intro hp hp5' hdp
      exact crossAtPrime_of_untwisted CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
        TauCeti.LieTypeIndex.characteristic_E8 hv
        (fun hp => CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp
          (by have := crossExc_eleven_le_of_ne_five_seven hp hp5' hp5 hp7; omega)
          (Or.inr (Or.inr rfl))) hp hp5' hdp

end Families

end CFSG.LocalAnalysis.RankFourTheoremC
