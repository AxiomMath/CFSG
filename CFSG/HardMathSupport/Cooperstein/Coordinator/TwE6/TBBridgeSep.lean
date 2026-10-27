module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBBridge
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBPeriod

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint.Chevalley

theorem dvd_pow_sub_pow_mod (f b : ℕ) : ((2 : ℤ) ^ f - 1) ∣ 2 ^ b - 2 ^ (b % f) := by
  have h1 : (2 : ℤ) ^ b = (2 ^ f) ^ (b / f) * 2 ^ (b % f) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h2 : (2 : ℤ) ^ f - 1 ∣ (2 ^ f) ^ (b / f) - 1 := by
    simpa using sub_dvd_pow_sub_pow ((2 : ℤ) ^ f) 1 (b / f)
  have h3 := Dvd.dvd.mul_right h2 (2 ^ (b % f))
  convert h3 using 1
  rw [h1]; ring

section Certs


theorem twSepM0_holds : TwSepM0 := by
  intro f g hf hg hgf ht s lam hlam b b' i i' j j' hdiv
  obtain ⟨⟨h3, hodd, hdvd, hord⟩, -, -⟩ := twPeriodArith_holds f g hf hg hgf ht
  have hm : ((twM0 f g : ℕ) : ℤ) ∣ 2 ^ f - 1 := by
    have := Int.natCast_dvd_natCast.2 hdvd
    rwa [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at this
  have hlam' : ∀ c : TwN, ((twM0 f g : ℕ) : ℤ) ∣ lam c - 0 * (if c = twNode s then 1 else 0) := by
    intro c; simpa using hlam c
  have hz : ∀ c : TwN, ((twM0 f g : ℕ) : ℤ) ∣ twU (
      ((0 : ℤ) • (F4Exc.wF s i • (F4Exc.uF s j • F4Exc.f4Omega s)) -
        (2 : ℤ) ^ b • (F4Exc.wF s i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ))) -
      ((0 : ℤ) • (F4Exc.wF s i' • (F4Exc.uF s j' • F4Exc.f4Omega s)) -
        (2 : ℤ) ^ b' • (F4Exc.wF s i' • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)))) c := by
    intro c
    rw [twU_sub]
    have e1 := twV_dvd hm s 0 lam hlam' b i j c
    have e2 := twV_dvd hm s 0 lam hlam' b' i' j' c
    have := dvd_sub (hdiv c) (dvd_sub e1 e2)
    convert this using 1
    ring
  have hk : ∀ k : Fin Tag.F4.rank, ((twM0 f g : ℕ) : ℤ) ∣ (2 : ℤ) ^ b *
      (F4Exc.wF s i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) k - (2 : ℤ) ^ b' *
      (F4Exc.wF s i' • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) k := by
    intro k
    have := dvd_of_dvd_twU _ hz k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zero_mul, zero_sub] at this
    have := (dvd_neg).2 this
    convert this using 1
    ring
  have hk' : ∀ k : Fin Tag.F4.rank, ((twM0 f g : ℕ) : ℤ) ∣ (2 : ℤ) ^ (b % f) *
      (F4Exc.wF s i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) k - (2 : ℤ) ^ (b' % f) *
      (F4Exc.wF s i' • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) k := by
    intro k
    have d1 := dvd_trans hm (dvd_pow_sub_pow_mod f b)
    have d2 := dvd_trans hm (dvd_pow_sub_pow_mod f b')
    have := dvd_sub (hk k) (dvd_sub (Dvd.dvd.mul_right d1 ((F4Exc.wF s i • (Pi.single s (1 : ℤ) :
      Fin Tag.F4.rank → ℤ)) k)) (Dvd.dvd.mul_right d2 ((F4Exc.wF s i' • (Pi.single s (1 : ℤ) :
      Fin Tag.F4.rank → ℤ)) k)))
    convert this using 1
    ring
  obtain ⟨-, -, hcont, hmin⟩ := F4Exc.family_props s
  have := F4Exc.sep_gamma h3 hodd hord (ι := Fin 12)
    (fun r : Fin 12 => F4Exc.wF s r • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ))
    (fun r d m h => hcont r d m h) (fun r r' hrr' d hd => hmin r r' hrr' d hd)
    (Nat.mod_lt b (by omega)) (Nat.mod_lt b' (by omega)) hk'
  exact this

end Certs

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
