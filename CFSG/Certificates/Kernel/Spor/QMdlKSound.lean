module

public import Certificates.Data.Kernel.Spor.QMdlK
public import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.QMdlK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PSearch CFSG.KS.HypK CFSG.KC.Misc.ArrEnum

theorem strictN_q (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem add5_lt (a b : Nat) : add5 a b < 243 := by
  have e : add5 a b = (dg3 a 0 + dg3 b 0) % 3 + 3 * ((dg3 a 1 + dg3 b 1) % 3 + 3 *
      ((dg3 a 2 + dg3 b 2) % 3 + 3 * ((dg3 a 3 + dg3 b 3) % 3 + 3 * ((dg3 a 4 + dg3 b 4) % 3)))) :=
    rfl
  omega

theorem cmod {v u : Nat} (hv : v < 243) : Nat.mod (v + 243 * u) 243 = v := by
  have h : (v + 243 * u) % 243 = v := by omega
  exact h

theorem cdiv {v u : Nat} (hv : v < 243) : Nat.div (v + 243 * u) 243 = u := by
  have h : (v + 243 * u) / 243 = u := by omega
  exact h

theorem cimod {i j : Nat} (hi : i < 3) : Nat.mod (i + 3 * j) 3 = i := by
  have h : (i + 3 * j) % 3 = i := by omega
  exact h

theorem cdiv729 {v i j : Nat} (hv : v < 243) (hi : i < 3) :
    Nat.div (v + 243 * (i + 3 * j)) 729 = j := by
  have h : (v + 243 * (i + 3 * j)) / 729 = j := by omega
  exact h

theorem dec {c : Nat} (hc : c < 2187) :
    ∃ v i j, v < 243 ∧ i < 3 ∧ j < 3 ∧ c = v + 243 * (i + 3 * j) :=
  ⟨c % 243, c / 243 % 3, c / 729, by omega, by omega, by omega, by omega⟩

theorem rdC_enc (M1 M2 : List Nat) {v i j : Nat} (k : Nat) (hv : v < 243) (hi : i < 3) :
    rdC M1 M2 (v + 243 * (i + 3 * j)) k = add5 v (nact M1 M2 i j k) + 243 * (i + 3 * j) := by
  unfold rdC
  rw [cmod hv, cdiv hv, cimod hi, cdiv729 hv hi]
  rfl

theorem rq1C_enc (M1 M2 : List Nat) (r1 r2 : Nat) {v i j : Nat} (hv : v < 243) (hi : i < 3) :
    rq1C M1 M2 r1 r2 (v + 243 * (i + 3 * j)) =
      if i = 2 then add5 (add5 v (pw3 M1 i (wq M2 r2 j))) r1 + 729 * j
      else add5 v (pw3 M1 i (wq M2 r2 j)) + 243 * (i + 3 * j + 1) := by
  unfold rq1C
  rw [cmod hv, cdiv hv, cimod hi, cdiv729 hv hi, strictN_q]
  interval_cases i <;> rfl

theorem rq2C_enc {v i j : Nat} (hv : v < 243) (hi : i < 3) (hj : j < 3) :
    rq2C (v + 243 * (i + 3 * j)) = if j = 2 then v + 243 * i else v + 243 * (i + 3 * (j + 1)) := by
  unfold rq2C
  rw [cdiv729 hv hi]
  interval_cases j
  · have h : Nat.add (v + 243 * (i + 3 * 0)) 729 = v + 243 * (i + 3 * (0 + 1)) := by
      change v + 243 * (i + 3 * 0) + 729 = _
      ring
    exact h
  · have h : Nat.add (v + 243 * (i + 3 * 1)) 729 = v + 243 * (i + 3 * (1 + 1)) := by
      change v + 243 * (i + 3 * 1) + 729 = _
      ring
    exact h
  · have h : Nat.sub (v + 243 * (i + 3 * 2)) 1458 = v + 243 * i := by
      change v + 243 * (i + 3 * 2) - 1458 = _
      omega
    exact h

variable {G : Type*} [Group G]

structure MHyp (E : Nat → G) (q1 q2 : G) (M1 M2 : List Nat) (r1 r2 : Nat) : Prop where
  e0 : E 0 = 1
  add : ∀ a b, E (add5 a b) = E a * E b
  c1 : ∀ k, q1 * E k = E (act5 M1 k) * q1
  c2 : ∀ k, q2 * E k = E (act5 M2 k) * q2
  p1 : q1 ^ 3 = E r1
  p2 : q2 ^ 3 = 1
  rr : q2 * q1 = E r2 * q1 * q2

@[expose] def mdl (E : Nat → G) (q1 q2 : G) (c : Nat) : G :=
  E (Nat.mod c 243) * q1 ^ Nat.mod (Nat.div c 243) 3 * q2 ^ Nat.div c 729

variable {E : Nat → G} {q1 q2 : G} {M1 M2 : List Nat} {r1 r2 : Nat}

theorem mdl_enc {v i j : Nat} (hv : v < 243) (hi : i < 3) :
    mdl E q1 q2 (v + 243 * (i + 3 * j)) = E v * q1 ^ i * q2 ^ j := by
  unfold mdl
  rw [cmod hv, cdiv hv, cimod hi, cdiv729 hv hi]

theorem pw3_conj {q : G} {M : List Nat} (hc : ∀ k, q * E k = E (act5 M k) * q) {i : Nat}
    (hi : i < 3) (k : Nat) : q ^ i * E k = E (pw3 M i k) * q ^ i := by
  interval_cases i
  · have e : pw3 M 0 k = k := rfl
    rw [e, pow_zero, one_mul, mul_one]
  · have e : pw3 M 1 k = act5 M k := rfl
    rw [e, pow_one, hc]
  · have e : pw3 M 2 k = act5 M (act5 M k) := rfl
    rw [e, pow_two, mul_assoc, hc, ← mul_assoc, hc, mul_assoc]

theorem s_conj (h : MHyp E q1 q2 M1 M2 r1 r2) {i j : Nat} (hi : i < 3) (hj : j < 3) (k : Nat) :
    q1 ^ i * q2 ^ j * E k = E (nact M1 M2 i j k) * (q1 ^ i * q2 ^ j) := by
  rw [mul_assoc, pw3_conj h.c2 hj, ← mul_assoc, pw3_conj h.c1 hi, mul_assoc]
  rfl

theorem wq_rel (h : MHyp E q1 q2 M1 M2 r1 r2) {j : Nat} (hj : j < 3) :
    q2 ^ j * q1 = E (wq M2 r2 j) * q1 * q2 ^ j := by
  interval_cases j
  · have e : wq M2 r2 0 = 0 := rfl
    simp [e, h.e0]
  · have e : wq M2 r2 1 = r2 := rfl
    simp only [e, pow_one]
    exact h.rr
  · have e : wq M2 r2 2 = add5 (act5 M2 r2) r2 := rfl
    calc q2 ^ 2 * q1 = q2 * (q2 * q1) := by rw [pow_two, mul_assoc]
      _ = q2 * E r2 * q1 * q2 := by rw [h.rr]; simp only [mul_assoc]
      _ = E (act5 M2 r2) * (q2 * q1) * q2 := by rw [h.c2]; simp only [mul_assoc]
      _ = E (act5 M2 r2) * (E r2 * q1 * q2) * q2 := by rw [h.rr]
      _ = E (wq M2 r2 2) * q1 * q2 ^ 2 := by rw [e, h.add, pow_two]; simp only [mul_assoc]

theorem mdl_rdC (h : MHyp E q1 q2 M1 M2 r1 r2) {c : Nat} (hc : c < 2187) (k : Nat) :
    mdl E q1 q2 c * E k = mdl E q1 q2 (rdC M1 M2 c k) ∧ rdC M1 M2 c k < 2187 := by
  obtain ⟨v, i, j, hv, hi, hj, rfl⟩ := dec hc
  rw [rdC_enc M1 M2 k hv hi, mdl_enc hv hi, mdl_enc (add5_lt _ _) hi, h.add]
  refine ⟨?_, by have := add5_lt v (nact M1 M2 i j k); omega⟩
  rw [mul_assoc, mul_assoc, ← mul_assoc (q1 ^ i), s_conj h hi hj]
  simp only [mul_assoc]

theorem mdl_rq1C (h : MHyp E q1 q2 M1 M2 r1 r2) {c : Nat} (hc : c < 2187) :
    mdl E q1 q2 c * q1 = mdl E q1 q2 (rq1C M1 M2 r1 r2 c) ∧ rq1C M1 M2 r1 r2 c < 2187 := by
  obtain ⟨v, i, j, hv, hi, hj, rfl⟩ := dec hc
  rw [rq1C_enc M1 M2 r1 r2 hv hi, mdl_enc hv hi]
  set w := add5 v (pw3 M1 i (wq M2 r2 j)) with hw
  have hwl : w < 243 := add5_lt _ _
  have key : E v * q1 ^ i * q2 ^ j * q1 = E w * q1 ^ (i + 1) * q2 ^ j := by
    rw [mul_assoc (E v * q1 ^ i), wq_rel h hj, hw, h.add, pow_succ]
    rw [← mul_assoc, ← mul_assoc, mul_assoc (E v), pw3_conj h.c1 hi]
    simp only [mul_assoc]
  rw [key]
  interval_cases i
  · have hb : w + 243 * (1 + 3 * j) < 2187 := by omega
    rw [if_neg (by norm_num)]
    have e : w + 243 * (0 + 3 * j + 1) = w + 243 * (1 + 3 * j) := by ring
    rw [e, mdl_enc hwl (by norm_num)]
    exact ⟨rfl, hb⟩
  · have hb : w + 243 * (2 + 3 * j) < 2187 := by omega
    rw [if_neg (by norm_num)]
    have e : w + 243 * (1 + 3 * j + 1) = w + 243 * (2 + 3 * j) := by ring
    rw [e, mdl_enc hwl (by norm_num)]
    exact ⟨rfl, hb⟩
  · rw [if_pos rfl]
    have e : add5 w r1 + 729 * j = add5 w r1 + 243 * (0 + 3 * j) := by ring
    have hb : add5 w r1 + 243 * (0 + 3 * j) < 2187 := by have := add5_lt w r1; omega
    rw [e, mdl_enc (add5_lt _ _) (by norm_num), h.add w r1, pow_zero, mul_one, ← h.p1]
    exact ⟨rfl, hb⟩

theorem mdl_rq2C (h : MHyp E q1 q2 M1 M2 r1 r2) {c : Nat} (hc : c < 2187) :
    mdl E q1 q2 c * q2 = mdl E q1 q2 (rq2C c) ∧ rq2C c < 2187 := by
  obtain ⟨v, i, j, hv, hi, hj, rfl⟩ := dec hc
  rw [rq2C_enc hv hi hj, mdl_enc hv hi, mul_assoc, ← pow_succ]
  have hb2 : ∀ j' < 3, v + 243 * (i + 3 * j') < 2187 := fun j' hj' => by omega
  interval_cases j
  · have hb := hb2 (0 + 1) (by norm_num)
    rw [if_neg (by norm_num), mdl_enc hv hi]
    exact ⟨rfl, hb⟩
  · have hb := hb2 (1 + 1) (by norm_num)
    rw [if_neg (by norm_num), mdl_enc hv hi]
    exact ⟨rfl, hb⟩
  · have hb := hb2 0 (by norm_num)
    rw [if_pos rfl]
    have e : v + 243 * i = v + 243 * (i + 3 * 0) := by ring
    rw [e, mdl_enc hv hi, h.p2, pow_zero, mul_one]
    exact ⟨rfl, hb⟩

theorem mdl_pq1 (h : MHyp E q1 q2 M1 M2 r1 r2) {c i : Nat} (hc : c < 2187) (hi : i < 3) :
    mdl E q1 q2 c * q1 ^ i = mdl E q1 q2 (pq1 M1 M2 r1 r2 i c) ∧ pq1 M1 M2 r1 r2 i c < 2187 := by
  interval_cases i
  · exact ⟨by rw [pow_zero, mul_one]; rfl, hc⟩
  · have e : pq1 M1 M2 r1 r2 1 c = rq1C M1 M2 r1 r2 c := rfl
    rw [e, pow_one]
    exact mdl_rq1C h hc
  · have e : pq1 M1 M2 r1 r2 2 c = rq1C M1 M2 r1 r2 (rq1C M1 M2 r1 r2 c) := strictN_q _ _
    obtain ⟨h1, l1⟩ := mdl_rq1C h hc
    obtain ⟨h2, l2⟩ := mdl_rq1C h l1
    rw [e, pow_two, ← mul_assoc, h1, h2]
    exact ⟨rfl, l2⟩

theorem mdl_pq2 (h : MHyp E q1 q2 M1 M2 r1 r2) {c j : Nat} (hc : c < 2187) (hj : j < 3) :
    mdl E q1 q2 c * q2 ^ j = mdl E q1 q2 (pq2 j c) ∧ pq2 j c < 2187 := by
  interval_cases j
  · exact ⟨by rw [pow_zero, mul_one]; rfl, hc⟩
  · have e : pq2 1 c = rq2C c := rfl
    rw [e, pow_one]
    exact mdl_rq2C h hc
  · have e : pq2 2 c = rq2C (rq2C c) := rfl
    obtain ⟨h1, l1⟩ := mdl_rq2C h hc
    obtain ⟨h2, l2⟩ := mdl_rq2C h l1
    rw [e, pow_two, ← mul_assoc, h1, h2]
    exact ⟨rfl, l2⟩

theorem mdl_mulC (h : MHyp E q1 q2 M1 M2 r1 r2) {a b : Nat} (ha : a < 2187) (hb : b < 2187) :
    mdl E q1 q2 a * mdl E q1 q2 b = mdl E q1 q2 (mulC M1 M2 r1 r2 a b) ∧
      mulC M1 M2 r1 r2 a b < 2187 := by
  have hm : mulC M1 M2 r1 r2 a b = pq2 (Nat.div b 729)
      (pq1 M1 M2 r1 r2 (Nat.mod (Nat.div b 243) 3) (rdC M1 M2 a (Nat.mod b 243))) := by
    unfold mulC
    simp only [strictN_q]
  obtain ⟨v, i, j, hv, hi, hj, rfl⟩ := dec hb
  rw [hm, cmod hv, cdiv hv, cimod hi, cdiv729 hv hi, mdl_enc hv hi]
  obtain ⟨h1, l1⟩ := mdl_rdC h ha v
  obtain ⟨h2, l2⟩ := mdl_pq1 h l1 hi
  obtain ⟨h3, l3⟩ := mdl_pq2 h l2 hj
  rw [← h3, ← h2, ← h1]
  exact ⟨by simp only [mul_assoc], l3⟩

theorem mdl_cubeC (h : MHyp E q1 q2 M1 M2 r1 r2) {c : Nat} (hc : c < 2187) :
    mdl E q1 q2 c ^ 3 = mdl E q1 q2 (cubeC M1 M2 r1 r2 c) ∧ cubeC M1 M2 r1 r2 c < 2187 := by
  have e : cubeC M1 M2 r1 r2 c = mulC M1 M2 r1 r2 (mulC M1 M2 r1 r2 c c) c := strictN_q _ _
  obtain ⟨h1, l1⟩ := mdl_mulC h hc hc
  obtain ⟨h2, l2⟩ := mdl_mulC h l1 hc
  rw [e, ← h2, ← h1, pow_three, mul_assoc]
  exact ⟨rfl, l2⟩

end CFSG.KS.QMdlK

end
