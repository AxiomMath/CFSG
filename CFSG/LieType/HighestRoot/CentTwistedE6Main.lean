module

public import CFSG.LieType.HighestRoot.CentTwistedE6

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.ModelFacts

abbrev f4zero : Fin (Tag.rank .F4) := ⟨0, by decide⟩

@[expose] def TwistedE6ThreeCZ2
    : Prop :=
  ∀ z ∈ rankOneGroup (twistedE6Datum 3 1) (Pi.single f4zero 1), orderOf z = 2 →
    ∀ L : Subgroup (twistedE6Group 3 1),
      L ≤ Subgroup.centralizer ({z} : Set (twistedE6Group 3 1)) →
      Subgroup.centralizer ({z} : Set (twistedE6Group 3 1)) ≤
        Subgroup.normalizer (L : Set (twistedE6Group 3 1)) →
      Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 1)) → z ∈ L →
      L = rankOneGroup (twistedE6Datum 3 1) (Pi.single f4zero 1)

variable (p f : ℕ) [Fact p.Prime]

theorem highestRootCZ_twistedE6
    (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h3 : p ^ f = 3 → TwistedE6ThreeCZ2) :
    HighestRootCZ (twistedE6Datum p f) (GaloisField p f) := by
  set k := GaloisField p (2 * f)
  have hcard : Nat.card k = p ^ (2 * f) := GaloisField.card p (2 * f) (by omega)
  have : Finite k := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact (pow_pos (Fact.out : p.Prime).pos _).ne')
  have hK : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  refine ⟨Pi.single f4zero 1, (isLongest_single_F4 rfl _ (k := f4zero) (by decide)).1,
    (isLongest_single_F4 rfl _ (k := f4zero) (by decide)).2,
    fun z hz h2 => ⟨centralizer_le_normalizer_twistedE6 (frobQ p f) hK hz h2,
      fun hF3 L hLC hCL hL hzL => ?_⟩⟩
  have hq : p ^ f = 3 := by
    rw [← hF3, GaloisField.card p f (by omega)]
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 := by
      rw [← hq]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1 hdvd
  subst hp3
  have hf1 : f = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) (hq.trans (pow_one 3).symm)
  subst hf1
  exact h3 hq z hz h2 L hLC hCL hL hzL

theorem highestRootCZ_modelUniv_twistedE6
    (n : ℕ) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h3 : p ^ f = 3 → TwistedE6ThreeCZ2) :
    HighestRootCZ (CFSG.ClassicalInvolution.Generic.modelUniv .twistedE6 n p f Fact.out).D
      (GaloisField p f) :=
  highestRootCZ_twistedE6 p f hp2 hf h3

end CFSG.LieType.HighestRoot
