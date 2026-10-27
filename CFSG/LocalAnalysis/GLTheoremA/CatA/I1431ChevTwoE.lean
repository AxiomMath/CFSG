module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzEvenCentreD4F4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)

theorem false_of_rkY_of_four_le {Y R : Type} [Group Y] [Finite Y] [Group R] [Finite R]
    (hRk : RkY Y) (hZ : Subgroup.center Y = ⊥) (θ : Y ⧸ Subgroup.center Y ≃* R)
    (hk : 4 ≤ CFSG.Open.twoLocalPrimeRank 3 R) : False := by
  have hqZ : ¬ 3 ∣ Nat.card (Subgroup.center Y) := by
    rw [hZ, Subgroup.card_bot]
    norm_num
  obtain ⟨E, hE, hEcard, T, hT2, hTc, hET⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.noncentralWitness_of_le_twoLocalPrimeRank θ
      Nat.prime_three hqZ (by norm_num) hk
  have hT : T ≠ ⊥ := fun h => hTc (h ▸ bot_le)
  have h3 := (hRk T hT hT2 E hET hE).2 (by rw [hZ, inf_bot_eq])
  rw [hEcard] at h3
  norm_num at h3

theorem center_eq_bot_of_adjointQuotient {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) {τ : Tag} {K : Type} [Field K]
    (e : Y ⧸ Subgroup.center Y ≃* AdjointQuotient τ K)
    (hM : Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient τ K))) :
    Subgroup.center Y = ⊥ :=
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87.center_eq_bot_of_hopf_subsingleton
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native Y).1 hY) e hM

theorem subsingleton_of_equiv_zmod_gcd {M : Type*} [Group M] {a b : ℕ} (hab : Nat.gcd a b = 1)
    (h : Nonempty (M ≃* Multiplicative (ZMod (Nat.gcd a b)))) : Subsingleton M := by
  obtain ⟨em⟩ := h
  rw [hab] at em
  exact em.injective.subsingleton

section E


theorem u42FieldTwoAt_E_of_rank
    (h6 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid), q.card = 2 →
      [Finite (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group] →
        4 ≤ CFSG.Open.twoLocalPrimeRank 3 (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group)
    (h7 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid), q.card = 2 →
      [Finite (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group] →
        4 ≤ CFSG.Open.twoLocalPrimeRank 3 (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group)
    (h8 : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid), q.card = 2 →
      [Finite (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group] →
        4 ≤ CFSG.Open.twoLocalPrimeRank 3 (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group) :
    U42FieldTwoAt fun d => ∃ q, d = .E6 q ∨ d = .E7 q ∨ d = .E8 q := by
  intro Y _ _ hY _ hRk ⟨d, hv⟩ ⟨q, hdq⟩ _ hf ⟨e⟩ _ _ _
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
    have hM := subsingleton_of_equiv_zmod_gcd (by rw [h21]; rfl)
      (CFSG.LieType.Steinberg.CentralExt.FieldTwo.e6_two_hopfMultiplier hK).2
    exact (false_of_rkY_of_four_le hRk (center_eq_bot_of_adjointQuotient hY (e.trans eB.symm) hM)
      e (h6 q hv hq2)).elim
  · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group := Finite.of_equiv _ e.toEquiv
    obtain ⟨eB⟩ := hB.e7 q hv (GaloisField 2 1) hKq
    have hM := subsingleton_of_equiv_zmod_gcd (by rw [h21]; rfl)
      (CFSG.LieType.Steinberg.CentralExt.FieldTwo.e7_two_hopfMultiplier hK).2
    exact (false_of_rkY_of_four_le hRk (center_eq_bot_of_adjointQuotient hY (e.trans eB.symm) hM)
      e (h7 q hv hq2)).elim
  · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group := Finite.of_equiv _ e.toEquiv
    obtain ⟨eB⟩ := hB.e8 q hv (GaloisField 2 1) hKq
    have hM := (CFSG.LieType.Steinberg.CentralExt.FieldTwo.e8_two_hopfMultiplier hK).2
    exact (false_of_rkY_of_four_le hRk (center_eq_bot_of_adjointQuotient hY (e.trans eB.symm) hM)
      e (h8 q hv hq2)).elim

end E

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
