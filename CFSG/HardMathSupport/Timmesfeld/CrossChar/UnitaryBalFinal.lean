module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalOuter

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag Matrix
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Lang.Coordinator

theorem diagUnitaryBalanceNeTwo_holds :
    ∀ (ℓ f n : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), 3 ≤ n →
      ¬(n = 3 ∧ ℓ ^ f = 2) → ℓ ^ f ≠ 2 → ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ ℓ → p ∣ ℓ ^ f + 1 →
      p ∣ n → ∀ D : Subgroup (MulAut (primeFormP h (idGram K n))), IsElemAbelian p D →
        Nat.card D = p ^ 3 → (D ≤ primeFormD h (idGram K n) ∨ (n = 3 ∧ ℓ ^ (f / p) = 2)) →
        ∀ H : Subgroup (MulAut (primeFormP h (idGram K n))),
          innerAut (primeFormP h (idGram K n)) ≤ H →
          D ≤ Subgroup.normalizer (H : Set (MulAut (primeFormP h (idGram K n)))) →
          localDeltaIn p H D = ⊥ := by
  intro ℓ f n K _ h hn hq hq2 p hp hp2 hpℓ hpq hpn D hD hcard hDo H hH hDH
  have hq3 : 3 < ℓ ^ f := by
    have h1 : 2 ≤ ℓ ^ f := two_le_pow_of h
    by_contra hle
    have h3 : ℓ ^ f = 3 := by omega
    rw [h3] at hpq
    have h4 : p ∣ 2 ^ 2 := hpq
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))
  by_cases hDl : D ≤ primeFormD h (idGram K n)
  · exact localDeltaIn_eq_bot_of_le_primeFormD hn hq hq3 hp hp2 hpq hD hcard hDl hH
  · rcases hDo with hDl' | ⟨hn3, hq0⟩
    · exact absurd hDl' hDl
    · subst hn3
      exact diagUnitaryBalanceOuter_holds ℓ f K h hq p hp hp2 hpℓ hpq hpn hq0 D hD hcard hDl H hH
        hDH

theorem crossCharFamAt_twistedADiag_of_ne_two
    (h32 : CrossCharFamAt .twistedA regimeTwistedAThreeTwo) :
    CrossCharFamAt .twistedA regimeTwistedADiag := by
  intro idx hk p hp hp2 hc hr
  obtain ⟨d, hv⟩ := idx
  obtain ⟨r, q, hd, h1, h2⟩ := hr
  change d = _ at hd
  subst hd
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  by_cases hq2 : q.card = 2
  · have hp3 : p = 3 := by
      have : p ∣ 3 := by rwa [hq2] at h1
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this
    exact h32 ⟨.twistedA r q, hv⟩ hk p hp hp2 hc ⟨r, q, rfl, hp3, hq2⟩
  · have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv
      (MulEquiv.refl (Cat ⟨.twistedA r q, hv⟩))
    obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
    have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
    obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
    let e : Cat ⟨.twistedA r q, hv⟩ ≃* primeFormP h (idGram K (r + 1)) :=
      (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
    have hpq : p ≠ q.p := fun h => hc (by simp [h])
    refine IsLocallyBalancedAbs.of_mulEquiv e ?_
    intro D hD hDcard H hH hDH
    by_cases hDl : D ≤ primeFormD h (idGram K (r + 1))
    · exact diagUnitaryBalanceNeTwo_holds q.p q.exponent (r + 1) K h (by omega) hq'
        (by rwa [← hcard]) p hp hp2 hpq (by rwa [← hcard]) h2 D hD hDcard (Or.inl hDl) H hH hDH
    · by_cases hq0 : r + 1 = 3 ∧ q.p ^ (q.exponent / p) = 2
      · exact diagUnitaryBalanceNeTwo_holds q.p q.exponent (r + 1) K h (by omega) hq'
          (by rwa [← hcard]) p hp hp2 hpq (by rwa [← hcard]) h2 D hD hDcard (Or.inr hq0) H hH hDH
      · exact localDeltaIn_eq_bot_of_not_le_primeFormD h (by omega) hq' hp hp2
          (by rwa [← hcard] ) hq0 hD hDl hH

theorem crossCharFamCat_twistedA_of_threeTwo
    (h32 : CrossCharFamAt .twistedA regimeTwistedAThreeTwo) : CrossCharFamCat .twistedA :=
  crossCharFamCat_twistedA_of_diag (crossCharFamAt_twistedADiag_of_ne_two h32) h32

end CFSG.HardMathSupport.Timmesfeld.CrossChar
