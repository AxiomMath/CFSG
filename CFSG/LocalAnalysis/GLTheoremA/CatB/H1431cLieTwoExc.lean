module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoE
public import CFSG.RankThree.PartTwo.Census.Exceptional.LocalRankThreeTwo
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadTwMain
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartTwo.Census.Exceptional

section E


theorem lieSTwoAt_E_of_rank
    (h6 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid), q.card = 2 →
      [Finite (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group] →
        4 ≤ CFSG.Open.twoLocalPrimeRank 3 (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group)
    (h7 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid), q.card = 2 →
      [Finite (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group] →
        4 ≤ CFSG.Open.twoLocalPrimeRank 3 (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group)
    (h8 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid), q.card = 2 →
      [Finite (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group] →
        4 ≤ CFSG.Open.twoLocalPrimeRank 3 (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group) :
    LieSTwoAt fun d => ∃ q, d = .E6 q ∨ d = .E7 q ∨ d = .E8 q := by
  intro Y _ _ hY _ hRk ⟨d, hv⟩ ⟨q, hdq⟩ _ hf ⟨e⟩ _ _ _ _
  have hq2 : q.card = 2 := by rcases hdq with rfl | rfl | rfl <;> exact hf
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hKq : Nat.card (GaloisField 2 1) = q.card := by rw [hK, hq2]
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  have h21 : Nat.card (GaloisField 2 1) - 1 = 1 := by rw [hK]
  rcases hdq with rfl | rfl | rfl
  · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group := Finite.of_equiv _ e.toEquiv
    obtain ⟨eB⟩ := hB.e6 q hv (GaloisField 2 1) hKq
    have hM := I1431C2.subsingleton_of_equiv_zmod_gcd (by rw [h21]; rfl)
      (CFSG.LieType.Steinberg.CentralExt.FieldTwo.e6_two_hopfMultiplier hK).2
    exact (I1431C2.false_of_rkY_of_four_le hRk
      (I1431C2.center_eq_bot_of_adjointQuotient hY (e.trans eB.symm) hM) e (h6 q hv hq2)).elim
  · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group := Finite.of_equiv _ e.toEquiv
    obtain ⟨eB⟩ := hB.e7 q hv (GaloisField 2 1) hKq
    have hM := I1431C2.subsingleton_of_equiv_zmod_gcd (by rw [h21]; rfl)
      (CFSG.LieType.Steinberg.CentralExt.FieldTwo.e7_two_hopfMultiplier hK).2
    exact (I1431C2.false_of_rkY_of_four_le hRk
      (I1431C2.center_eq_bot_of_adjointQuotient hY (e.trans eB.symm) hM) e (h7 q hv hq2)).elim
  · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group := Finite.of_equiv _ e.toEquiv
    obtain ⟨eB⟩ := hB.e8 q hv (GaloisField 2 1) hKq
    have hM := (CFSG.LieType.Steinberg.CentralExt.FieldTwo.e8_two_hopfMultiplier hK).2
    exact (I1431C2.false_of_rkY_of_four_le hRk
      (I1431C2.center_eq_bot_of_adjointQuotient hY (e.trans eB.symm) hM) e (h8 q hv hq2)).elim

end E

section EAt


theorem lieSTwoAt_E : LieSTwoAt fun d => ∃ q, d = .E6 q ∨ d = .E7 q ∨ d = .E8 q :=
  lieSTwoAt_E_of_rank (fun q hv hq => four_le_localRank_three_E6_two q hv hq)
    (fun q hv hq => four_le_localRank_three_E7_two q hv hq)
    (fun q hv hq => four_le_localRank_three_E8_two q hv hq)

end EAt

section TwE6


theorem lieSTwoAt_twistedE6 : LieSTwoAt fun d => ∃ q, d = .twistedE6 q := by
  intro Y _ _ _ _ hRk ⟨d, hv⟩ ⟨q, hdq⟩ hc hf ⟨e⟩ _ _ _ _
  subst hdq
  have hq2 : q.card = 2 := hf
  have hp : q.p = 2 := by simpa using hc
  have hexp : q.exponent = 1 := by
    have h := q.card_def
    rw [hq2, hp] at h
    exact (Nat.pow_right_injective (le_refl 2) (h.symm.trans (pow_one 2).symm))
  have hm := CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv hp e
  have hCE : ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .twistedE6 2 q.exponent :=
    ⟨⟨Nat.prime_two, q.exponent_pos, rfl⟩, hm⟩
  have hLM : LieModel (Y ⧸ Subgroup.center Y) .twistedE6 0 2 q.exponent :=
    .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags], hCE⟩)
  exact (CFSG.HardMathSupport.Dickson.Sec6.I1431.rkY_false_twE6 hRk Nat.prime_two
    q.exponent_pos hCE hLM (by rw [hexp]; norm_num)).elim

end TwE6

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
