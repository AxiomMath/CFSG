module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreS
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116c
public import CFSG.SignalizerFunctorTheorem.McBride.Models.OddFrame.Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open

private theorem prime_eq_of_dvd_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {k : ℕ}
    (h : p ∣ q ^ k) : p = q :=
  (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h)

private theorem prime_eq_of_dvd_120 {p : ℕ} (hp : p.Prime) (h : p ∣ 120) :
    p = 2 ∨ p = 3 ∨ p = 5 := by
  have h' : p ∣ 2 ^ 3 * 3 * 5 := by norm_num; exact h
  rcases hp.dvd_mul.mp h' with h1 | h5
  · rcases hp.dvd_mul.mp h1 with h2 | h3
    · exact Or.inl (prime_eq_of_dvd_pow hp Nat.prime_two h2)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5))

private theorem not_sq_dvd_120 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 120 := by
  intro h
  have hdvd : p ∣ 120 := (dvd_pow_self p two_ne_zero).trans h
  rcases prime_eq_of_dvd_120 hp hdvd with rfl | rfl | rfl
  · exact hp2 rfl
  · norm_num at h
  · norm_num at h

private theorem prime_eq_of_dvd_1440 {p : ℕ} (hp : p.Prime) (h : p ∣ 1440) :
    p = 2 ∨ p = 3 ∨ p = 5 := by
  have h' : p ∣ 2 ^ 5 * 3 ^ 2 * 5 := by norm_num; exact h
  rcases hp.dvd_mul.mp h' with h1 | h5
  · rcases hp.dvd_mul.mp h1 with h2 | h3
    · exact Or.inl (prime_eq_of_dvd_pow hp Nat.prime_two h2)
    · exact Or.inr (Or.inl (prime_eq_of_dvd_pow hp Nat.prime_three h3))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5))

private theorem not_sq_dvd_1440 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ^ 2 ∣ 1440 := by
  intro h
  have hdvd : p ∣ 1440 := (dvd_pow_self p two_ne_zero).trans h
  rcases prime_eq_of_dvd_1440 hp hdvd with rfl | rfl | rfl
  · exact hp2 rfl
  · exact hp3 rfl
  · norm_num at h

private theorem prime_eq_of_dvd_40320 {p : ℕ} (hp : p.Prime) (h : p ∣ 40320) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have h' : p ∣ 2 ^ 7 * 3 ^ 2 * 5 * 7 := by norm_num; exact h
  rcases hp.dvd_mul.mp h' with h1 | h7
  · rcases hp.dvd_mul.mp h1 with h2 | h5
    · rcases hp.dvd_mul.mp h2 with h3 | h4
      · exact Or.inl (prime_eq_of_dvd_pow hp Nat.prime_two h3)
      · exact Or.inr (Or.inl (prime_eq_of_dvd_pow hp Nat.prime_three h4))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7)))

private theorem not_sq_dvd_40320 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ^ 2 ∣ 40320 := by
  intro h
  have hdvd : p ∣ 40320 := (dvd_pow_self p two_ne_zero).trans h
  rcases prime_eq_of_dvd_40320 hp hdvd with rfl | rfl | rfl | rfl
  · exact hp2 rfl
  · exact hp3 rfl
  · norm_num at h
  · norm_num at h

private theorem card_mulAut_alternating_five (hn : 5 ≤ 5) :
    Nat.card (MulAut (TauCeti.CFSGIndex.alternating 5 hn).Group) = 120 := by
  have h : Nat.card (MulAut (alternatingGroup (Fin 5))) = Nat.factorial 5 :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116c.card_mulAut_alt
      (by norm_num) (by norm_num)
  simpa [Nat.factorial] using h

private theorem card_mulAut_alternating_six (hn : 5 ≤ 6) :
    Nat.card (MulAut (TauCeti.CFSGIndex.alternating 6 hn).Group) = 1440 := by
  have h := CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6
  simpa using h

private theorem card_mulAut_alternating_eight (hn : 5 ≤ 8) :
    Nat.card (MulAut (TauCeti.CFSGIndex.alternating 8 hn).Group) = 40320 := by
  have h : Nat.card (MulAut (alternatingGroup (Fin 8))) = Nat.factorial 8 :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116c.card_mulAut_alt
      (by norm_num) (by norm_num)
  simpa [Nat.factorial] using h

theorem kd264Amb_holds (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : KD264Amb p := by
  constructor
  · intro n hn hn568 hexcl D hD
    haveI : Fact p.Prime := ⟨hp⟩
    rcases hn568 with rfl | rfl | rfl
    · have hcard := card_mulAut_alternating_five hn
      haveI : Finite (MulAut (TauCeti.CFSGIndex.alternating 5 hn).Group) :=
        Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
      have hdvd : Nat.card D ∣ 120 := by
        calc Nat.card D ∣ Nat.card (MulAut (TauCeti.CFSGIndex.alternating 5 hn).Group) :=
              Subgroup.card_subgroup_dvd_card D
          _ = 120 := hcard
      exact CFSG.SignalizerFunctorTheorem.McBride.OddFrame.card_le_of_pgroup
        (CFSG.Open.IsElemAbelian.isPGroup hD) hdvd (not_sq_dvd_120 hp hp2)
    · have hcard := card_mulAut_alternating_six hn
      have hp3 : p ≠ 3 := fun h => hexcl ⟨h, Or.inl rfl⟩
      haveI : Finite (MulAut (TauCeti.CFSGIndex.alternating 6 hn).Group) :=
        Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
      have hdvd : Nat.card D ∣ 1440 := by
        calc Nat.card D ∣ Nat.card (MulAut (TauCeti.CFSGIndex.alternating 6 hn).Group) :=
              Subgroup.card_subgroup_dvd_card D
          _ = 1440 := hcard
      exact CFSG.SignalizerFunctorTheorem.McBride.OddFrame.card_le_of_pgroup
        (CFSG.Open.IsElemAbelian.isPGroup hD) hdvd (not_sq_dvd_1440 hp hp2 hp3)
    · have hcard := card_mulAut_alternating_eight hn
      have hp3 : p ≠ 3 := fun h => hexcl ⟨h, Or.inr rfl⟩
      haveI : Finite (MulAut (TauCeti.CFSGIndex.alternating 8 hn).Group) :=
        Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
      have hdvd : Nat.card D ∣ 40320 := by
        calc Nat.card D ∣ Nat.card (MulAut (TauCeti.CFSGIndex.alternating 8 hn).Group) :=
              Subgroup.card_subgroup_dvd_card D
          _ = 40320 := hcard
      exact CFSG.SignalizerFunctorTheorem.McBride.OddFrame.card_le_of_pgroup
        (CFSG.Open.IsElemAbelian.isPGroup hD) hdvd (not_sq_dvd_40320 hp hp2 hp3)
  · intro hp7 e he D hD
    subst hp7
    obtain ⟨d, hv⟩ := e
    obtain ⟨q, hq, hq7⟩ := he
    subst hq
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hcard : Nat.card (MulAut (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) = 336 :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116c.card_mulAut_L27 hq7
        (MulEquiv.refl _)
    haveI : Finite (MulAut (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have hdvd : Nat.card D ∣ 336 := by
      calc Nat.card D ∣ Nat.card (MulAut (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) :=
            Subgroup.card_subgroup_dvd_card D
        _ = 336 := hcard
    exact CFSG.SignalizerFunctorTheorem.McBride.OddFrame.card_le_of_pgroup
      (CFSG.Open.IsElemAbelian.isPGroup hD) hdvd (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
