module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor

public section

namespace CFSG.LocalAnalysis.GLTheoremA.No5

open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator

private theorem prime_eq_of_dvd_pow {q p k : ℕ} (hq : q.Prime) (hp : p.Prime) (h : q ∣ p ^ k) :
    q = p :=
  (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)

theorem prime_dvd_co1 {q : ℕ} (hq : q.Prime) (h : q ∣ CFSG.Open.orderCo1) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 23 := by
  unfold CFSG.Open.orderCo1 at h
  rcases (Nat.Prime.dvd_mul hq).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
          · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
            · exact Or.inl (prime_eq_of_dvd_pow hq Nat.prime_two h)
            · exact Or.inr (Or.inl (prime_eq_of_dvd_pow hq Nat.prime_three h))
          · exact Or.inr (Or.inr (Or.inl (prime_eq_of_dvd_pow hq Nat.prime_five h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (prime_eq_of_dvd_pow hq (by norm_num) h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h))))))

theorem spor_of_co1_dvd (s : TauCeti.SporadicName) (h : CFSG.Open.orderCo1 ∣ sporOrd s) :
    s = .Co1 ∨ s = .B ∨ s = .M := by
  revert h
  cases s <;> norm_num [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu,
    CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime,
    CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster,
    CFSG.Open.orderMonster]

theorem factorial_half_ne_co1 {m : ℕ} (hm : 5 ≤ m) :
    m.factorial / 2 ≠ CFSG.Open.orderCo1 := by
  intro h
  have h2 : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hfac : m.factorial = 2 * CFSG.Open.orderCo1 := by
    rw [← h, Nat.mul_div_cancel' h2]
  have h23 : 23 ∣ m.factorial := by
    rw [hfac]
    exact Dvd.dvd.mul_left (by norm_num [CFSG.Open.orderCo1]) 2
  have hm23 : 23 ≤ m := (Nat.Prime.dvd_factorial (by norm_num)).1 h23
  have h17 : 17 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  rw [hfac] at h17
  rcases (Nat.Prime.dvd_mul (by norm_num)).1 h17 with h' | h'
  · norm_num at h'
  · norm_num [CFSG.Open.orderCo1] at h'

theorem card_pSimple_dvd {Y : Type} [Group Y] [Finite Y] (J : Subgroup Y) :
    Nat.card (PSimple 5 J) ∣ Nat.card J :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)

theorem fixSubgroup_conj_eq_cx {Y : Type} [Group Y] (y : Y) :
    fixSubgroup (MulAut.conj y) = CFSG.LocalAnalysis.GLTheoremA.S8.cx y := by
  ext a
  rw [mem_fixSubgroup, CFSG.LocalAnalysis.GLTheoremA.S8.cx, Subgroup.mem_centralizer_singleton_iff,
    MulAut.conj_apply, mul_inv_eq_iff_eq_mul, eq_comm]

theorem conj_ne_one_of_orderOf {Y : Type} [Group Y] (hY : IsSimpleGroup Y)
    (hnab : ∃ a b : Y, a * b ≠ b * a) {y : Y} (hy : orderOf y = 5) : MulAut.conj y ≠ 1 := by
  intro h
  have hc : y ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := congrArg (fun φ : MulAut Y => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hg
    rw [mul_inv_eq_iff_eq_mul] at hg
    exact hg.symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with hb | ht
  · rw [hb, Subgroup.mem_bot] at hc
    subst hc
    simp at hy
  · obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : a ∈ Subgroup.center Y := by rw [ht]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 ha b).symm

end CFSG.LocalAnalysis.GLTheoremA.No5
