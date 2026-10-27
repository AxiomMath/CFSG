module

public import CFSG.HardMathSupport.Malle.SeitzCube.Landing
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.LieType.SeitzGeneration

theorem orderOf_eq_E8 {e : ℕ} (h : 3 ≤ degCount .E8 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
  have h30 : e ≤ 30 := le_thirty_of_degCount_pos (Or.inr (Or.inr (Or.inr rfl))) (by omega)
  interval_cases e <;> first | decide | (exfalso; revert h; decide)

theorem primes_E8 {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (hpq : ¬ p ∣ q)
    (hpq2 : ¬ p ∣ q ^ 2 - 1) (hdeg : 3 ≤ degCount .E8 (orderOf ((q : ℕ) : ZMod p))) :
    (p ≠ 3 ∧ p ∣ q ^ 2 + q + 1) ∨ p ∣ q ^ 2 + 1 ∨ (p ≠ 3 ∧ p ∣ q ^ 2 - q + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  set x : ZMod p := ((q : ℕ) : ZMod p) with hx
  have hx0 : x ≠ 0 := fun h0 => hpq ((ZMod.natCast_eq_zero_iff q p).1 h0)
  have hxp : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
  have hdvd : orderOf x ∣ p - 1 := orderOf_dvd_of_pow_eq_one hxp
  have hsq : x ^ 2 ≠ 1 := fun h => hpq2 (by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow,
      Nat.cast_one, ← hx, h, sub_self])
  have hpow : ∀ k, orderOf x = k → x ^ k = 1 := fun k hk => hk ▸ pow_orderOf_eq_one x
  rcases orderOf_eq_E8 hdeg with h | h | h | h | h
  · exact absurd (by rw [orderOf_eq_one_iff.1 h, one_pow]) hsq
  · exact absurd (hpow 2 h) hsq
  · left
    have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at h; omega
    have hpoly : x ^ 2 + x + 1 = 0 := by
      have h0 : (x - 1) * (x ^ 2 + x + 1) = 0 := by
        rw [show (x - 1) * (x ^ 2 + x + 1) = x ^ 3 - 1 by ring, hpow 3 h, sub_self]
      exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hx1)
    refine ⟨fun h3 => ?_, (ZMod.natCast_eq_zero_iff _ p).1 ?_⟩
    · subst h3
      rw [h] at hdvd
      norm_num at hdvd
    · push_cast
      rw [← hx]
      exact hpoly
  · right; left
    have hpoly : x ^ 2 + 1 = 0 := by
      have h0 : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by
        rw [show (x ^ 2 - 1) * (x ^ 2 + 1) = x ^ 4 - 1 by ring, hpow 4 h, sub_self]
      exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hsq)
    refine (ZMod.natCast_eq_zero_iff _ p).1 ?_
    push_cast
    rw [← hx]
    exact hpoly
  · right; right
    have hx3 : x ^ 3 ≠ 1 := fun h3 => by
      have := orderOf_dvd_of_pow_eq_one h3
      rw [h] at this
      norm_num at this
    have hxm : x + 1 ≠ 0 := fun h1 => hsq (by
      have h2 : x ^ 2 - 1 = (x + 1) * (x - 1) := by ring
      rwa [h1, zero_mul, sub_eq_zero] at h2)
    have hpoly : x ^ 2 - x + 1 = 0 := by
      have h0 : (x ^ 3 - 1) * ((x + 1) * (x ^ 2 - x + 1)) = 0 := by
        rw [show (x ^ 3 - 1) * ((x + 1) * (x ^ 2 - x + 1)) = x ^ 6 - 1 by ring, hpow 6 h,
          sub_self]
      exact ((mul_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hx3))).resolve_left
        hxm)
    refine ⟨fun h3 => ?_, (ZMod.natCast_eq_zero_iff _ p).1 ?_⟩
    · subst h3
      rw [h] at hdvd
      norm_num at hdvd
    · rw [Nat.cast_add, Nat.cast_sub (Nat.le_self_pow two_ne_zero q), Nat.cast_pow,
        Nat.cast_one, ← hx]
      exact hpoly

section Assembly


theorem excCubeHigh_E8_of_twisted
    (h3 : TwistedCubeE8 fun q p => p ≠ 3 ∧ p ∣ q ^ 2 + q + 1)
    (h4 : TwistedCubeE8 fun q p => p ≠ 2 ∧ p ∣ q ^ 2 + 1)
    (h6 : TwistedCubeE8 fun q p => p ≠ 3 ∧ p ∣ q ^ 2 - q + 1) :
    ExcCubeHigh .E8 TauCeti.LieTypeIndex.E8 := by
  intro q hv p hp hp2 hpq _ hpq2 hdeg _
  have hP : ∀ P : ℕ → ℕ → Prop, TwistedCubeE8 P → P q.card p →
      ∃ E : Subgroup (Cat ⟨TauCeti.LieTypeIndex.E8 q, hv⟩), IsElemAbelian p E ∧
        Nat.card E = p ^ 3 ∧
          (NormalizesRSub ⟨TauCeti.LieTypeIndex.E8 q, hv⟩ E ∨ HyperGen p ⊤ E) := by
    intro P hT hPq
    obtain ⟨E, hE, hc, hR⟩ := exists_cube_cat_E8_of_twisted q hv
      fun K _ _ hK hKc L _ _ _ Fr hFr => by
        have hT' := hT K L Fr (fun c => by rw [hFr, hK]) p hp (by rwa [hK])
        rwa [ringChar.eq K q.p] at hT'
    exact ⟨E, hE, hc, Or.inl hR⟩
  have hq1 : 1 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  have hpq' : ¬ p ∣ q.card := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1
    (hp.dvd_of_dvd_pow (TauCeti.PrimePower.card_def q ▸ h)))
  rcases primes_E8 hp hq1 hpq' hpq2 hdeg with h | h | h
  · exact hP _ h3 h
  · exact hP _ h4 ⟨hp2, h⟩
  · exact hP _ h6 h

end Assembly

end CFSG.HardMathSupport.Malle.SeitzCube
