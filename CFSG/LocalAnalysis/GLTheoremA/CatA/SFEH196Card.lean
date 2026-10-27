module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H196Facts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFEH196Card

open CFSG.Yardstones.Md0ec50421ce4 CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.I1420
open Finset

private theorem dvd_div_of_cop {p N g : ℕ} (hg : g ∣ N) (hcop : Nat.Coprime p g) (h : p ∣ N) :
    p ∣ N / g := by
  rcases Nat.eq_zero_or_pos g with rfl | hg0
  · rw [Nat.div_zero]
    exact dvd_zero p
  · obtain ⟨c, rfl⟩ := hg
    rw [Nat.mul_div_cancel_left c hg0]
    exact hcop.dvd_of_dvd_mul_left h

private theorem cop_pred_succ {p x : ℕ} (hp : p.Prime) (hx : p ∣ x) (hx1 : 1 ≤ x) :
    Nat.Coprime p (x - 1) ∧ Nat.Coprime p (x + 1) := by
  refine ⟨?_, ?_⟩
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have hx' : p ∣ (x - 1) + 1 := by rwa [Nat.sub_add_cancel hx1]
    exact hp.not_dvd_one ((Nat.dvd_add_right h).mp hx')
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    exact hp.not_dvd_one ((Nat.dvd_add_right hx).mp h)

private theorem tri_ne_zero {n : ℕ} (hn : 1 ≤ n) : n * (n + 1) / 2 ≠ 0 := by
  have h : 1 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
  omega

private theorem dvd_orderA {p n q : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hq : p ∣ q) (hq1 : 1 ≤ q) :
    p ∣ orderA n q := by
  unfold orderA
  have hP2 : q ^ 2 - 1 ∣ ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) :=
    Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (by simp only [Finset.mem_Icc]; omega)
  have hq1' : q - 1 ∣ q ^ 2 - 1 := by simpa using Nat.sub_dvd_pow_sub_pow q 1 2
  have hg : Nat.gcd (n + 1) (q - 1) ∣
      q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) :=
    (Nat.gcd_dvd_right _ _).trans (hq1'.trans (hP2.trans (dvd_mul_left _ _)))
  have hcop : Nat.Coprime p (Nat.gcd (n + 1) (q - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) (cop_pred_succ hp hq hq1).1
  exact dvd_div_of_cop hg hcop (dvd_mul_of_dvd_left (dvd_pow hq (tri_ne_zero hn)) _)

private theorem dvd_orderTwistedA {p n q : ℕ} (hp : p.Prime) (hn : 2 ≤ n) (hq : p ∣ q)
    (hq1 : 1 ≤ q) : p ∣ orderTwistedA n q := by
  unfold orderTwistedA
  have h3 : (3 : ℕ) ∈ Icc 2 (n + 1) := by simp only [Finset.mem_Icc]; omega
  have hP3 : q + 1 ∣ ∏ i ∈ Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) := by
    refine (?_ : q + 1 ∣ (if Even 3 then q ^ 3 - 1 else q ^ 3 + 1)).trans
      (Finset.dvd_prod_of_mem (fun i => if Even i then q ^ i - 1 else q ^ i + 1) h3)
    have he : ¬ Even 3 := by decide
    rw [if_neg he]
    simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
  have hg : Nat.gcd (n + 1) (q + 1) ∣
      q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) :=
    (Nat.gcd_dvd_right _ _).trans (hP3.trans (dvd_mul_left _ _))
  have hcop : Nat.Coprime p (Nat.gcd (n + 1) (q + 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) (cop_pred_succ hp hq hq1).2
  exact dvd_div_of_cop hg hcop (dvd_mul_of_dvd_left (dvd_pow hq (tri_ne_zero (by omega))) _)

private theorem dvd_orderBC {p n q : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hq : p ∣ q) (hq1 : 1 ≤ q) :
    p ∣ orderBC n q := by
  unfold orderBC
  have h1 : (1 : ℕ) ∈ Icc 1 n := by simp only [Finset.mem_Icc]; omega
  have hterm : q - 1 ∣ ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) := by
    refine (?_ : q - 1 ∣ q ^ (2 * 1) - 1).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) h1)
    simpa using Nat.sub_dvd_pow_sub_pow q 1 (2 * 1)
  have hg : Nat.gcd 2 (q - 1) ∣ q ^ (n * n) * ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right _ _).trans (hterm.trans (dvd_mul_left _ _))
  have hcop : Nat.Coprime p (Nat.gcd 2 (q - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) (cop_pred_succ hp hq hq1).1
  have hnn : n * n ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  exact dvd_div_of_cop hg hcop (dvd_mul_of_dvd_left (dvd_pow hq hnn) _)

private theorem dvd_orderD {p n q : ℕ} (hp : p.Prime) (hn : 4 ≤ n) (hq : p ∣ q) (hq1 : 1 ≤ q) :
    p ∣ orderD n q := by
  unfold orderD
  have hqn : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have hg : Nat.gcd 4 (q ^ n - 1) ∣
      q ^ (n * (n - 1)) * (q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right _ _).trans (Dvd.dvd.mul_right (dvd_mul_left _ _) _)
  have hcop : Nat.Coprime p (Nat.gcd 4 (q ^ n - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
      (cop_pred_succ hp (dvd_pow hq (by omega)) hqn).1
  exact dvd_div_of_cop hg hcop (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (dvd_pow hq (Nat.mul_ne_zero (by omega) (by omega))) _) _)

private theorem dvd_orderTwistedD {p n q : ℕ} (hp : p.Prime) (hn : 4 ≤ n) (hq : p ∣ q)
    (hq1 : 1 ≤ q) : p ∣ orderTwistedD n q := by
  unfold orderTwistedD
  have hqn : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have hg : Nat.gcd 4 (q ^ n + 1) ∣
      q ^ (n * (n - 1)) * (q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right _ _).trans (Dvd.dvd.mul_right (dvd_mul_left _ _) _)
  have hcop : Nat.Coprime p (Nat.gcd 4 (q ^ n + 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
      (cop_pred_succ hp (dvd_pow hq (by omega)) hqn).2
  exact dvd_div_of_cop hg hcop (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (dvd_pow hq (Nat.mul_ne_zero (by omega) (by omega))) _) _)

private theorem dvd_orderE6 {p q : ℕ} (hp : p.Prime) (hq : p ∣ q) (hq1 : 1 ≤ q) :
    p ∣ orderE6 q := by
  unfold orderE6
  have hg : Nat.gcd 3 (q - 1) ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1) := by
    refine (Nat.gcd_dvd_right _ _).trans ?_
    exact Dvd.dvd.mul_left (by simpa using Nat.sub_dvd_pow_sub_pow q 1 2) _
  have hcop : Nat.Coprime p (Nat.gcd 3 (q - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) (cop_pred_succ hp hq hq1).1
  refine dvd_div_of_cop hg hcop ?_
  repeat' first | exact dvd_pow hq (by norm_num) | apply Dvd.dvd.mul_right

private theorem dvd_orderTwistedE6 {p q : ℕ} (hp : p.Prime) (hq : p ∣ q) (hq1 : 1 ≤ q) :
    p ∣ orderTwistedE6 q := by
  unfold orderTwistedE6
  have hg : Nat.gcd 3 (q + 1) ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) := by
    refine (Nat.gcd_dvd_right _ _).trans ?_
    have h5 : q + 1 ∣ q ^ 5 + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 5)
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h5 _) _
  have hcop : Nat.Coprime p (Nat.gcd 3 (q + 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) (cop_pred_succ hp hq hq1).2
  refine dvd_div_of_cop hg hcop ?_
  repeat' first | exact dvd_pow hq (by norm_num) | apply Dvd.dvd.mul_right

private theorem dvd_orderE7 {p q : ℕ} (hp : p.Prime) (hq : p ∣ q) (hq1 : 1 ≤ q) :
    p ∣ orderE7 q := by
  unfold orderE7
  have hg : Nat.gcd 2 (q - 1) ∣ q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
      (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := by
    refine (Nat.gcd_dvd_right _ _).trans ?_
    exact Dvd.dvd.mul_left (by simpa using Nat.sub_dvd_pow_sub_pow q 1 2) _
  have hcop : Nat.Coprime p (Nat.gcd 2 (q - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) (cop_pred_succ hp hq hq1).1
  refine dvd_div_of_cop hg hcop ?_
  repeat' first | exact dvd_pow hq (by norm_num) | apply Dvd.dvd.mul_right

private theorem dvd_orderE8 {p q : ℕ} (hq : p ∣ q) : p ∣ orderE8 q := by
  unfold orderE8
  repeat' first | exact dvd_pow hq (by norm_num) | apply Dvd.dvd.mul_right

private theorem dvd_orderF4 {p q : ℕ} (hq : p ∣ q) : p ∣ orderF4 q := by
  unfold orderF4
  repeat' first | exact dvd_pow hq (by norm_num) | apply Dvd.dvd.mul_right

private theorem dvd_orderG2 {p q : ℕ} (hq : p ∣ q) : p ∣ orderG2 q := by
  unfold orderG2
  repeat' first | exact dvd_pow hq (by norm_num) | apply Dvd.dvd.mul_right

private theorem dvd_orderTrialityD4 {p q : ℕ} (hq : p ∣ q) : p ∣ orderTrialityD4 q := by
  unfold orderTrialityD4
  repeat' first | exact dvd_pow hq (by norm_num) | apply Dvd.dvd.mul_right

private theorem dvd_orderSuzuki {q : ℕ} (hq : 2 ∣ q) : 2 ∣ orderSuzuki q := by
  unfold orderSuzuki
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow hq (by norm_num)) _) _

private theorem dvd_orderRee {q : ℕ} (hq : 3 ∣ q) : 3 ∣ orderRee q := by
  unfold orderRee
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow hq (by norm_num)) _) _

private theorem dvd_orderTwistedF4 {q : ℕ} (hq : 2 ∣ q) : 2 ∣ orderTwistedF4 q := by
  unfold orderTwistedF4
  repeat' first | exact dvd_pow hq (by norm_num) | apply Dvd.dvd.mul_right

private theorem two_dvd_orderTits : 2 ∣ orderTits := by
  unfold orderTits
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
    (dvd_pow_self 2 (by norm_num)) _) _) _

private theorem dvd_of_ambiguous_lie {p : ℕ} (d : TauCeti.LieTypeIndex) (hv : d.Valid)
    (hi : ambiguousChev p (TauCeti.CFSGIndex.lie ⟨d, hv⟩)) : p ∣ lieOrderFormula d := by
  cases d with
  | A r q =>
    rcases r with _ | _ | r
    · exact (show False from hi).elim
    · have hi' : (q.card = 7 ∧ p = 2) ∨ (q.card = 8 ∧ p = 3) := hi
      rcases hi' with ⟨h7, rfl⟩ | ⟨h8, rfl⟩
      · show 2 ∣ orderA 1 q.card
        rw [h7]
        decide
      · show 3 ∣ orderA 1 q.card
        rw [h8]
        decide
    · exact (show False from hi).elim
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | r
    · exact (show False from hi).elim
    · exact (show False from hi).elim
    · have hi' : q.card = 3 ∧ p = 2 := hi
      obtain ⟨h3, rfl⟩ := hi'
      show 2 ∣ orderTwistedA 2 q.card
      rw [h3]
      decide
    · have hi' : q.card = 2 ∧ p = 3 := hi
      obtain ⟨h2, rfl⟩ := hi'
      show 3 ∣ orderTwistedA 3 q.card
      rw [h2]
      decide
    · exact (show False from hi).elim
  | _ => exact (show False from hi).elim

private theorem dvd_card_of_char {p : ℕ} {q : TauCeti.PrimePower} (hc : q.p = p) :
    p ∣ q.card := by
  rw [TauCeti.PrimePower.card_def, ← hc]
  exact dvd_pow_self _ q.exponent_pos.ne'

private theorem one_le_card (q : TauCeti.PrimePower) : 1 ≤ q.card := by
  rw [TauCeti.PrimePower.card_def]
  exact Nat.one_le_pow _ _ q.prime_p.pos

private theorem dvd_lieOrderFormula {p : ℕ} (hp : p.Prime) {d : TauCeti.LieTypeIndex}
    (hv : d.Valid) (hc : d.characteristic = p) : p ∣ lieOrderFormula d := by
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hv).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases d with
  | A n q =>
    have hc' : q.p = p := by simpa using hc
    exact dvd_orderA hp hs.1 (dvd_card_of_char hc') (one_le_card q)
  | twistedA n q =>
    have hc' : q.p = p := by simpa using hc
    exact dvd_orderTwistedA hp hs.1 (dvd_card_of_char hc') (one_le_card q)
  | B n q =>
    have hc' : q.p = p := by simpa using hc
    exact dvd_orderBC hp (by have := hs.1; omega) (dvd_card_of_char hc') (one_le_card q)
  | C n q =>
    have hc' : q.p = p := by simpa using hc
    exact dvd_orderBC hp (by have := hs.1; omega) (dvd_card_of_char hc') (one_le_card q)
  | D n q =>
    have hc' : q.p = p := by simpa using hc
    exact dvd_orderD hp hs (dvd_card_of_char hc') (one_le_card q)
  | twistedD n q =>
    have hc' : q.p = p := by simpa using hc
    exact dvd_orderTwistedD hp hs (dvd_card_of_char hc') (one_le_card q)
  | E6 q =>
    have hc' : q.p = p := by simpa using hc
    exact dvd_orderE6 hp (dvd_card_of_char hc') (one_le_card q)
  | E7 q =>
    have hc' : q.p = p := by simpa using hc
    exact dvd_orderE7 hp (dvd_card_of_char hc') (one_le_card q)
  | E8 q =>
    have hc' : q.p = p := by simpa using hc
    exact dvd_orderE8 (dvd_card_of_char hc')
  | F4 q =>
    have hc' : q.p = p := by simpa using hc
    exact dvd_orderF4 (dvd_card_of_char hc')
  | G2 q =>
    have hc' : q.p = p := by simpa using hc
    exact dvd_orderG2 (dvd_card_of_char hc')
  | twistedE6 q =>
    have hc' : q.p = p := by simpa using hc
    exact dvd_orderTwistedE6 hp (dvd_card_of_char hc') (one_le_card q)
  | trialityD4 q =>
    have hc' : q.p = p := by simpa using hc
    exact dvd_orderTrialityD4 (dvd_card_of_char hc')
  | suzuki m =>
    have h2 : p = 2 := by simpa using hc.symm
    subst h2
    exact dvd_orderSuzuki (q := 2 ^ (2 * m + 1)) (dvd_pow_self 2 (by omega))
  | reeG2 m =>
    have h3 : p = 3 := by simpa using hc.symm
    subst h3
    exact dvd_orderRee (q := 3 ^ (2 * m + 1)) (dvd_pow_self 3 (by omega))
  | reeF4 m =>
    have h2 : p = 2 := by simpa using hc.symm
    subst h2
    exact dvd_orderTwistedF4 (q := 2 ^ (2 * m + 1)) (dvd_pow_self 2 (by omega))
  | tits =>
    have h2 : p = 2 := by simpa using hc.symm
    subst h2
    exact two_dvd_orderTits

end CFSG.LocalAnalysis.GLTheoremA.SFEH196Card

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4 CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.I1420
open SFEH196Card

theorem I196ChevCard_holds
    : ∀ p : ℕ, I196ChevCard p := by
  intro p
  unfold I196ChevCard
  intro hp S _ _ _ hchev
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic r hr => exact (show False from hi).elim
    | alternating n hn => exact (show False from hi).elim
    | lie d =>
      rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d S ⟨e⟩]
      exact dvd_lieOrderFormula hp d.2 hi
    | sporadic s => exact (show False from hi).elim
  · cases i with
    | cyclic r hr => exact (show False from hi).elim
    | alternating n hn =>
      have hs : (n = 5 ∧ (p = 2 ∨ p = 5)) ∨ (n = 6 ∧ (p = 2 ∨ p = 3)) ∨ (n = 8 ∧ p = 2) := hi
      have e' : S ≃ alternatingGroup (Fin n) := e.toEquiv
      rcases hs with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;>
        (rw [Nat.card_congr e', Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
         decide)
    | lie d =>
      rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d S ⟨e⟩]
      exact dvd_of_ambiguous_lie d.1 d.2 hi
    | sporadic s => exact (show False from hi).elim

end CFSG.LocalAnalysis.GLTheoremA

end
