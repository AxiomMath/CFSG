module

public import Certificates.Data.Kernel.MonsterPcFive.Model
public import CFSG.Certificates.Kernel.BabyMonster.PcFive.Coll
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.MonPcFive

open CFSG.KC.BM.PcFive (pow_mod_five swap_assoc pow_pow_assoc conjInv conjInv_apply conj_pow_succ)

variable {G : Type*} [Group G]

@[expose] def cmAt (m : CM6) : Fin 6 → Fin 6 → ℕ :=
  ![![0, m.m01, m.m02, m.m03, m.m04, m.m05], ![0, 0, m.m12, m.m13, m.m14, m.m15],
    ![0, 0, 0, m.m23, m.m24, m.m25], ![0, 0, 0, 0, m.m34, m.m35], ![0, 0, 0, 0, 0, m.m45],
    ![0, 0, 0, 0, 0, 0]]

structure RRel (m : CM6) (b : Fin 6 → G) (x : G) : Prop where
  x5 : x ^ 5 = 1
  b5 : ∀ i, b i ^ 5 = 1
  xc : ∀ i, x * b i = b i * x
  sw : ∀ i j : Fin 6, i < j → b j * b i = b i * b j * x ^ cmAt m i j

@[expose] def nfR (b : Fin 6 → G) (x : G) (a : RV) : G :=
  b 0 ^ a.a0 * b 1 ^ a.a1 * b 2 ^ a.a2 * b 3 ^ a.a3 * b 4 ^ a.a4 * b 5 ^ a.a5 * x ^ a.c

section R

variable {m : CM6} {b : Fin 6 → G} {x : G}

theorem RRel.xq (h : RRel m b x) (i : Fin 6) (n l : ℕ) (X : G) :
    x ^ n * (b i ^ l * X) = b i ^ l * (x ^ n * X) := by
  rw [← mul_assoc, (Commute.pow_pow (h.xc i) n l).eq, mul_assoc]

theorem nfR_mul (h : RRel m b x) (a c : RV) : nfR b x a * nfR b x c = nfR b x (mulR m a c) := by
  have w : ∀ i j : Fin 6, i < j → ∀ (k l : ℕ) (X : G),
      b j ^ k * (b i ^ l * X) = b i ^ l * (b j ^ k * (x ^ (l * k * cmAt m i j) * X)) :=
    fun i j hij => swap_assoc (h.xc i) (h.xc j) (h.sw i j hij)
  have w01 : ∀ (k l : ℕ) (X : G), b 1 ^ k * (b 0 ^ l * X) =
      b 0 ^ l * (b 1 ^ k * (x ^ (l * k * m.m01) * X)) := w 0 1 (by decide)
  have w02 : ∀ (k l : ℕ) (X : G), b 2 ^ k * (b 0 ^ l * X) =
      b 0 ^ l * (b 2 ^ k * (x ^ (l * k * m.m02) * X)) := w 0 2 (by decide)
  have w03 : ∀ (k l : ℕ) (X : G), b 3 ^ k * (b 0 ^ l * X) =
      b 0 ^ l * (b 3 ^ k * (x ^ (l * k * m.m03) * X)) := w 0 3 (by decide)
  have w04 : ∀ (k l : ℕ) (X : G), b 4 ^ k * (b 0 ^ l * X) =
      b 0 ^ l * (b 4 ^ k * (x ^ (l * k * m.m04) * X)) := w 0 4 (by decide)
  have w05 : ∀ (k l : ℕ) (X : G), b 5 ^ k * (b 0 ^ l * X) =
      b 0 ^ l * (b 5 ^ k * (x ^ (l * k * m.m05) * X)) := w 0 5 (by decide)
  have w12 : ∀ (k l : ℕ) (X : G), b 2 ^ k * (b 1 ^ l * X) =
      b 1 ^ l * (b 2 ^ k * (x ^ (l * k * m.m12) * X)) := w 1 2 (by decide)
  have w13 : ∀ (k l : ℕ) (X : G), b 3 ^ k * (b 1 ^ l * X) =
      b 1 ^ l * (b 3 ^ k * (x ^ (l * k * m.m13) * X)) := w 1 3 (by decide)
  have w14 : ∀ (k l : ℕ) (X : G), b 4 ^ k * (b 1 ^ l * X) =
      b 1 ^ l * (b 4 ^ k * (x ^ (l * k * m.m14) * X)) := w 1 4 (by decide)
  have w15 : ∀ (k l : ℕ) (X : G), b 5 ^ k * (b 1 ^ l * X) =
      b 1 ^ l * (b 5 ^ k * (x ^ (l * k * m.m15) * X)) := w 1 5 (by decide)
  have w23 : ∀ (k l : ℕ) (X : G), b 3 ^ k * (b 2 ^ l * X) =
      b 2 ^ l * (b 3 ^ k * (x ^ (l * k * m.m23) * X)) := w 2 3 (by decide)
  have w24 : ∀ (k l : ℕ) (X : G), b 4 ^ k * (b 2 ^ l * X) =
      b 2 ^ l * (b 4 ^ k * (x ^ (l * k * m.m24) * X)) := w 2 4 (by decide)
  have w25 : ∀ (k l : ℕ) (X : G), b 5 ^ k * (b 2 ^ l * X) =
      b 2 ^ l * (b 5 ^ k * (x ^ (l * k * m.m25) * X)) := w 2 5 (by decide)
  have w34 : ∀ (k l : ℕ) (X : G), b 4 ^ k * (b 3 ^ l * X) =
      b 3 ^ l * (b 4 ^ k * (x ^ (l * k * m.m34) * X)) := w 3 4 (by decide)
  have w35 : ∀ (k l : ℕ) (X : G), b 5 ^ k * (b 3 ^ l * X) =
      b 3 ^ l * (b 5 ^ k * (x ^ (l * k * m.m35) * X)) := w 3 5 (by decide)
  have w45 : ∀ (k l : ℕ) (X : G), b 5 ^ k * (b 4 ^ l * X) =
      b 4 ^ l * (b 5 ^ k * (x ^ (l * k * m.m45) * X)) := w 4 5 (by decide)
  have xx : ∀ (a c : ℕ) (X : G), x ^ a * (x ^ c * X) = x ^ (a + c) * X := pow_pow_assoc x
  have qq : ∀ (i : Fin 6) (a c : ℕ) (X : G), b i ^ a * (b i ^ c * X) = b i ^ (a + c) * X :=
    fun i => pow_pow_assoc (b i)
  have xq := h.xq
  unfold nfR mulR
  simp only [mul_assoc, w01, w02, w03, w04, w05, w12, w13, w14, w15, w23, w24, w25, w34, w35, w45,
    xx, qq, xq, ← pow_add]
  rw [pow_mod_five (h.b5 0) (a.a0 + c.a0), pow_mod_five (h.b5 1) (a.a1 + c.a1),
    pow_mod_five (h.b5 2) (a.a2 + c.a2), pow_mod_five (h.b5 3) (a.a3 + c.a3),
    pow_mod_five (h.b5 4) (a.a4 + c.a4), pow_mod_five (h.b5 5) (a.a5 + c.a5), pow_mod_five h.x5]
  congr 8
  ring

theorem nfR_one : nfR b x RV.one = 1 := by simp [nfR, RV.one]

theorem nfR_pow (h : RRel m b x) (r : RV) : ∀ k : ℕ, nfR b x r ^ k = nfR b x (powR m r k)
  | 0 => by rw [pow_zero, powR, nfR_one]
  | k + 1 => by rw [pow_succ, nfR_pow h r k, powR, nfR_mul h]

theorem nfR_xg : nfR b x RV.xg = x := by simp [nfR, RV.xg]

theorem nfR_xc (c : ℕ) : nfR b x (RV.xc c) = x ^ c := by simp [nfR, RV.xc]

@[expose] def RAct.get (A : RAct) (i : ℕ) : RV :=
  bif i.beq 0 then A.r0 else bif i.beq 1 then A.r1 else bif i.beq 2 then A.r2
  else bif i.beq 3 then A.r3 else bif i.beq 4 then A.r4 else A.r5

theorem map_nfR (h : RRel m b x) {f : G →* G} {A : RAct}
    (hb : ∀ i : Fin 6, f (b i) = nfR b x (A.get i.val)) (hx : f x = x) (a : RV) :
    f (nfR b x a) = nfR b x (applyR m A a) := by
  unfold applyR
  simp only [← nfR_mul h, ← nfR_pow h, nfR_xg]
  have e0 : nfR b x A.r0 = f (b 0) := (hb 0).symm
  have e1 : nfR b x A.r1 = f (b 1) := (hb 1).symm
  have e2 : nfR b x A.r2 = f (b 2) := (hb 2).symm
  have e3 : nfR b x A.r3 = f (b 3) := (hb 3).symm
  have e4 : nfR b x A.r4 = f (b 4) := (hb 4).symm
  have e5 : nfR b x A.r5 = f (b 5) := (hb 5).symm
  rw [e0, e1, e2, e3, e4, e5]
  conv_rhs => rw [← hx]
  unfold nfR
  simp only [map_mul, map_pow]

theorem conj_nfR (h : RRel m b x) {u : G} {A : RAct}
    (hb : ∀ i : Fin 6, u * b i * u⁻¹ = nfR b x (A.get i.val)) (hx : u * x * u⁻¹ = x) (a : RV) :
    u * nfR b x a * u⁻¹ = nfR b x (applyR m A a) := by
  have e : ∀ y : G, u * y * u⁻¹ = (MulAut.conj u).toMonoidHom y := fun y => by
    simp [MulAut.conj_apply]
  rw [e]
  exact map_nfR h (fun i => by rw [← e, hb i]) (by rw [← e, hx]) a

end R

@[expose] def RV.red (a : RV) : Prop :=
  a.a0 < 5 ∧ a.a1 < 5 ∧ a.a2 < 5 ∧ a.a3 < 5 ∧ a.a4 < 5 ∧ a.a5 < 5 ∧ a.c < 5

theorem RV.beq_eq {a b : RV} (h : a.beq b = true) : a = b := by
  unfold RV.beq at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  cases a
  cases b
  simp only at h0 h1 h2 h3 h4 h5 h6
  subst h0 h1 h2 h3 h4 h5 h6
  rfl

theorem mulR_red (m : CM6) (a b : RV) : (mulR m a b).red := by
  unfold mulR RV.red
  refine ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num)⟩

theorem rvOne_red : RV.one.red := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [RV.one]

theorem decR_red (n : ℕ) : (decR n).red := by
  unfold decR RV.red
  refine ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num)⟩

theorem applyT_red (T : RT) (a : RV) : (applyT T a).red := mulR_red _ _ _

theorem phi1At_red (k : ℕ) {a : RV} (ha : a.red) : (phi1At k a).red := by
  unfold phi1At
  cases k.beq 0 <;> cases k.beq 1 <;> cases k.beq 2 <;> cases k.beq 3 <;>
    simp only [cond_true, cond_false] <;> first | exact ha | exact applyT_red _ _

theorem phi2At_red (k : ℕ) {a : RV} (ha : a.red) : (phi2At k a).red := by
  unfold phi2At
  cases k.beq 0 <;> cases k.beq 1 <;> cases k.beq 2 <;> cases k.beq 3 <;>
    simp only [cond_true, cond_false] <;> first | exact ha | exact applyT_red _ _

theorem allBelow_spec {f : ℕ → Bool} : ∀ {k : ℕ}, allBelow f k = true → ∀ n < k, f n = true
  | 0, _, n, hn => absurd hn (Nat.not_lt_zero n)
  | k + 1, h, n, hn => by
    unfold allBelow at h
    rw [Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
    · exact allBelow_spec h.2 n hn
    · exact h.1

section Tab

variable {b : Fin 6 → G} {x : G}

theorem nfR_unitR : ∀ k : Fin 6, nfR b x (unitR k.val) = b k := by
  intro k
  fin_cases k <;> simp [nfR, unitR]

theorem RP.powOK_spec (h : RRel cmM b x) {P : RP} (hp : P.powOK = true) :
    ∀ e < 5, nfR b x (P.at e) = nfR b x P.p1 ^ e := by
  unfold RP.powOK at hp
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨h2, h3⟩, h4⟩ := hp
  have a0 : P.at 0 = RV.one := rfl
  have a1 : P.at 1 = P.p1 := rfl
  have a2 : P.at 2 = P.p2 := rfl
  have a3 : P.at 3 = P.p3 := rfl
  have a4 : P.at 4 = P.p4 := rfl
  intro e he
  interval_cases e
  · rw [a0, nfR_one, pow_zero]
  · rw [a1, pow_one]
  · rw [a2, RV.beq_eq h2, ← nfR_mul h, pow_two]
  · rw [a3, RV.beq_eq h3, ← nfR_mul h, RV.beq_eq h2, ← nfR_mul h, pow_three, mul_assoc]
  · rw [a4, RV.beq_eq h4, ← nfR_mul h, RV.beq_eq h3, ← nfR_mul h, RV.beq_eq h2, ← nfR_mul h]
    simp only [pow_succ, pow_zero, one_mul]

theorem conj_tab (h : RRel cmM b x) {g : G} {T : RT}
    (hrow : ∀ i : Fin 6, g⁻¹ * b i * g = nfR b x (T.row i.val).p1) (hp : T.powOK = true)
    (hx : g⁻¹ * x * g = x) {a : RV} (ha : a.red) :
    g⁻¹ * nfR b x a * g = nfR b x (applyT T a) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := ha
  have hpi := allBelow_spec hp
  have r : ∀ (i : Fin 6) (e : ℕ), e < 5 → nfR b x ((T.row i.val).at e) = (g⁻¹ * b i * g) ^ e :=
    fun i e he => by rw [hrow i]; exact RP.powOK_spec h (hpi i.val i.2) e he
  have r0 : nfR b x (T.t0.at a.a0) = (g⁻¹ * b 0 * g) ^ a.a0 := r 0 _ h0
  have r1 : nfR b x (T.t1.at a.a1) = (g⁻¹ * b 1 * g) ^ a.a1 := r 1 _ h1
  have r2 : nfR b x (T.t2.at a.a2) = (g⁻¹ * b 2 * g) ^ a.a2 := r 2 _ h2
  have r3 : nfR b x (T.t3.at a.a3) = (g⁻¹ * b 3 * g) ^ a.a3 := r 3 _ h3
  have r4 : nfR b x (T.t4.at a.a4) = (g⁻¹ * b 4 * g) ^ a.a4 := r 4 _ h4
  have r5 : nfR b x (T.t5.at a.a5) = (g⁻¹ * b 5 * g) ^ a.a5 := r 5 _ h5
  have hxc : x ^ a.c = conjInv g (x ^ a.c) := by rw [map_pow, conjInv_apply, hx]
  unfold applyT
  rw [← nfR_mul h, ← nfR_mul h, ← nfR_mul h, ← nfR_mul h, ← nfR_mul h, ← nfR_mul h, r0, r1, r2, r3,
    r4, r5, nfR_xc, hxc]
  simp only [← conjInv_apply, ← map_pow, ← map_mul]
  rfl

theorem tab_red : ∀ T ∈ [tabU11, tabU12, tabU13, tabU14, tabU21, tabU22, tabU23, tabU24],
    ∀ i < 6, (T.row i).p1.red := by
  unfold RV.red
  decide

theorem conj_chain (h : RRel cmM b x) {u : G} {A : RAct} {T1 T2 T3 T4 : RT}
    (hc : ∀ i : Fin 6, u * b i * u⁻¹ = nfR b x (A.get i.val)) (hx : u * x * u⁻¹ = x)
    (hok : (T1.powOK && T2.powOK && T3.powOK && T4.powOK && invOK A T1 && stepOK T1 T1 T2 &&
      stepOK T1 T2 T3 && stepOK T1 T3 T4) = true)
    (hr1 : ∀ i < 6, (T1.row i).p1.red) :
    (∀ {a : RV}, a.red → u⁻¹ * nfR b x a * u = nfR b x (applyT T1 a)) ∧
    (∀ {a : RV}, a.red → (u ^ 2)⁻¹ * nfR b x a * u ^ 2 = nfR b x (applyT T2 a)) ∧
    (∀ {a : RV}, a.red → (u ^ 3)⁻¹ * nfR b x a * u ^ 3 = nfR b x (applyT T3 a)) ∧
    (∀ {a : RV}, a.red → (u ^ 4)⁻¹ * nfR b x a * u ^ 4 = nfR b x (applyT T4 a)) := by
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, hinv⟩, s2⟩, s3⟩, s4⟩ := hok
  have hxi : u⁻¹ * x * u = x := by
    calc u⁻¹ * x * u = u⁻¹ * (u * x * u⁻¹) * u := by rw [hx]
      _ = x := by group
  have hxk : ∀ k : ℕ, (u ^ k)⁻¹ * x * u ^ k = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [conj_pow_succ, hxi, ih]
  have row1 : ∀ i : Fin 6, u⁻¹ * b i * u = nfR b x (T1.row i.val).p1 := by
    intro i
    have e := conj_nfR h hc hx (T1.row i.val).p1
    rw [RV.beq_eq (allBelow_spec hinv i.val i.2), nfR_unitR] at e
    rw [← e]
    group
  have g1 : ∀ {a : RV}, a.red → u⁻¹ * nfR b x a * u = nfR b x (applyT T1 a) :=
    fun ha => conj_tab h row1 p1 hxi ha
  have step : ∀ {k : ℕ} {Tk Tk1 : RT},
      (∀ {a : RV}, a.red → (u ^ k)⁻¹ * nfR b x a * u ^ k = nfR b x (applyT Tk a)) →
      stepOK T1 Tk Tk1 = true → Tk1.powOK = true →
      ∀ {a : RV}, a.red → (u ^ (k + 1))⁻¹ * nfR b x a * u ^ (k + 1) = nfR b x (applyT Tk1 a) := by
    intro k Tk Tk1 hk hs hp a ha
    refine conj_tab h (fun i => ?_) hp (hxk (k + 1)) ha
    rw [conj_pow_succ, row1 i, hk (hr1 i.val i.2), RV.beq_eq (allBelow_spec hs i.val i.2)]
  have g1' : ∀ {a : RV}, a.red → (u ^ 1)⁻¹ * nfR b x a * u ^ 1 = nfR b x (applyT T1 a) :=
    fun ha => by rw [pow_one]; exact g1 ha
  have g2 : ∀ {a : RV}, a.red → (u ^ 2)⁻¹ * nfR b x a * u ^ 2 = nfR b x (applyT T2 a) :=
    fun ha => step g1' s2 p2 ha
  have g3 : ∀ {a : RV}, a.red → (u ^ 3)⁻¹ * nfR b x a * u ^ 3 = nfR b x (applyT T3 a) :=
    fun ha => step g2 s3 p3 ha
  have g4 : ∀ {a : RV}, a.red → (u ^ 4)⁻¹ * nfR b x a * u ^ 4 = nfR b x (applyT T4 a) :=
    fun ha => step g3 s4 p4 ha
  exact ⟨g1, g2, g3, g4⟩

end Tab

structure PcHyp (u2 u1 : G) (b : Fin 6 → G) (x : G) : Prop where
  rel : RRel cmM b x
  u25 : u2 ^ 5 = 1
  u15 : u1 ^ 5 = x ^ 2
  c1 : ∀ i : Fin 6, u1 * b i * u1⁻¹ = nfR b x (act1.get i.val)
  c2 : ∀ i : Fin 6, u2 * b i * u2⁻¹ = nfR b x (act2.get i.val)
  ux1 : u1 * x * u1⁻¹ = x
  ux2 : u2 * x * u2⁻¹ = x
  r0 : u2 * u1 * u2⁻¹ = u1 * nfR b x rU

structure TabChecks : Prop where
  tab : tabOK () = true
  tau : tauOK () = true

@[expose] def psi (u2 u1 : G) (b : Fin 6 → G) (x : G) (v : V9) : G :=
  u2 ^ v.e0 * u1 ^ v.e1 * nfR b x v.r

variable {u2 u1 : G} {b : Fin 6 → G} {x : G}

theorem TabChecks.split (C : TabChecks) :
    (tabU11.powOK && tabU12.powOK && tabU13.powOK && tabU14.powOK && invOK act1 tabU11 &&
      stepOK tabU11 tabU11 tabU12 && stepOK tabU11 tabU12 tabU13 &&
      stepOK tabU11 tabU13 tabU14) = true ∧
    (tabU21.powOK && tabU22.powOK && tabU23.powOK && tabU24.powOK && invOK act2 tabU21 &&
      stepOK tabU21 tabU21 tabU22 && stepOK tabU21 tabU22 tabU23 &&
      stepOK tabU21 tabU23 tabU24) = true := by
  have h := C.tab
  unfold tabOK at h
  simp only [Bool.and_eq_true] at h ⊢
  tauto

theorem PcHyp.conj1 (H : PcHyp u2 u1 b x) (C : TabChecks) {k : ℕ} (hk : k < 5) {a : RV}
    (ha : a.red) : (u1 ^ k)⁻¹ * nfR b x a * u1 ^ k = nfR b x (phi1At k a) := by
  obtain ⟨g1, g2, g3, g4⟩ := conj_chain H.rel H.c1 H.ux1 C.split.1
    (tab_red tabU11 (by simp))
  interval_cases k
  · simp [phi1At]
  · rw [pow_one]
    exact g1 ha
  · exact g2 ha
  · exact g3 ha
  · exact g4 ha

theorem PcHyp.conj2 (H : PcHyp u2 u1 b x) (C : TabChecks) {k : ℕ} (hk : k < 5) {a : RV}
    (ha : a.red) : (u2 ^ k)⁻¹ * nfR b x a * u2 ^ k = nfR b x (phi2At k a) := by
  obtain ⟨g1, g2, g3, g4⟩ := conj_chain H.rel H.c2 H.ux2 C.split.2
    (tab_red tabU21 (by simp))
  interval_cases k
  · simp [phi2At]
  · rw [pow_one]
    exact g1 ha
  · exact g2 ha
  · exact g3 ha
  · exact g4 ha

theorem tauAt_red : ∀ e < 5, ∀ f < 5, (tauAt e f).red := by
  unfold RV.red
  decide

theorem PcHyp.tau1 (H : PcHyp u2 u1 b x) (C : TabChecks) :
    ∀ f < 5, (u2 ^ f)⁻¹ * u1 * u2 ^ f = u1 * nfR b x (tauAt 1 f) := by
  have hT := C.tau
  unfold tauOK at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨⟨h0, h1⟩, -⟩ := hT
  have base : u2⁻¹ * u1 * u2 = u1 * nfR b x (tauAt 1 1) := by
    have e := conj_nfR H.rel H.c2 H.ux2 (tauAt 1 1)
    have e2 : u2 * (u1 * nfR b x (tauAt 1 1)) * u2⁻¹ = u1 := by
      calc u2 * (u1 * nfR b x (tauAt 1 1)) * u2⁻¹
          = (u2 * u1 * u2⁻¹) * (u2 * nfR b x (tauAt 1 1) * u2⁻¹) := by group
        _ = u1 := by
          rw [H.r0, e, mul_assoc, nfR_mul H.rel, RV.beq_eq h0, nfR_one, mul_one]
    calc u2⁻¹ * u1 * u2 = u2⁻¹ * (u2 * (u1 * nfR b x (tauAt 1 1)) * u2⁻¹) * u2 := by rw [e2]
      _ = u1 * nfR b x (tauAt 1 1) := by group
  have succ : ∀ f < 3, (u2 ^ (f + 1))⁻¹ * u1 * u2 ^ (f + 1) = u1 * nfR b x (tauAt 1 (f + 1)) →
      (u2 ^ (f + 2))⁻¹ * u1 * u2 ^ (f + 2) = u1 * nfR b x (tauAt 1 (f + 2)) := by
    intro f hf ih
    have hs := RV.beq_eq (allBelow_spec h1 f hf)
    have c := H.conj2 C (k := 1) (by norm_num) (tauAt_red 1 (by norm_num) (f + 1) (by omega))
    rw [pow_one] at c
    calc (u2 ^ (f + 2))⁻¹ * u1 * u2 ^ (f + 2)
        = u2⁻¹ * ((u2 ^ (f + 1))⁻¹ * u1 * u2 ^ (f + 1)) * u2 := by
          rw [show f + 2 = f + 1 + 1 from rfl, pow_succ]
          group
      _ = (u2⁻¹ * u1 * u2) * (u2⁻¹ * nfR b x (tauAt 1 (f + 1)) * u2) := by
          rw [ih]
          group
      _ = u1 * nfR b x (tauAt 1 (f + 2)) := by
          rw [base, c, mul_assoc, nfR_mul H.rel, hs]
  intro f hf
  have t0 : (u2 ^ 0)⁻¹ * u1 * u2 ^ 0 = u1 * nfR b x (tauAt 1 0) := by
    simp [tauAt, nfR_one]
  have t1 : (u2 ^ 1)⁻¹ * u1 * u2 ^ 1 = u1 * nfR b x (tauAt 1 1) := by
    rw [pow_one]
    exact base
  have t2 := succ 0 (by norm_num) t1
  have t3 := succ 1 (by norm_num) t2
  have t4 := succ 2 (by norm_num) t3
  interval_cases f
  · exact t0
  · exact t1
  · exact t2
  · exact t3
  · exact t4

theorem PcHyp.tau (H : PcHyp u2 u1 b x) (C : TabChecks) :
    ∀ e < 5, ∀ f < 5, (u2 ^ f)⁻¹ * u1 ^ e * u2 ^ f = u1 ^ e * nfR b x (tauAt e f) := by
  have hT := C.tau
  unfold tauOK at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨-, h2⟩ := hT
  have t1 := H.tau1 C
  have succ : ∀ e < 3, ∀ f < 5,
      (u2 ^ f)⁻¹ * u1 ^ (e + 1) * u2 ^ f = u1 ^ (e + 1) * nfR b x (tauAt (e + 1) f) →
      (u2 ^ f)⁻¹ * u1 ^ (e + 2) * u2 ^ f = u1 ^ (e + 2) * nfR b x (tauAt (e + 2) f) := by
    intro e he f hf ih
    rcases Nat.eq_zero_or_pos f with rfl | hf0
    · simp [tauAt, nfR_one]
    have hs := RV.beq_eq (allBelow_spec (allBelow_spec h2 e he) (f - 1) (by omega))
    rw [show f - 1 + 1 = f by omega] at hs
    have c := H.conj1 C (k := 1) (by norm_num) (tauAt_red (e + 1) (by omega) f hf)
    rw [pow_one] at c
    calc (u2 ^ f)⁻¹ * u1 ^ (e + 2) * u2 ^ f
        = ((u2 ^ f)⁻¹ * u1 ^ (e + 1) * u2 ^ f) * ((u2 ^ f)⁻¹ * u1 * u2 ^ f) := by
          rw [show e + 2 = e + 1 + 1 from rfl, pow_succ]
          group
      _ = u1 ^ (e + 1) * u1 * (u1⁻¹ * nfR b x (tauAt (e + 1) f) * u1) * nfR b x (tauAt 1 f) := by
          rw [ih, t1 f hf]
          group
      _ = u1 ^ (e + 2) * nfR b x (tauAt (e + 2) f) := by
          rw [c, mul_assoc, nfR_mul H.rel, ← hs, ← pow_succ]
  intro e he f hf
  have s0 : (u2 ^ f)⁻¹ * u1 ^ 0 * u2 ^ f = u1 ^ 0 * nfR b x (tauAt 0 f) := by
    simp [tauAt, nfR_one]
  have s1 : (u2 ^ f)⁻¹ * u1 ^ 1 * u2 ^ f = u1 ^ 1 * nfR b x (tauAt 1 f) := by
    simpa only [pow_one] using t1 f hf
  have s2 := succ 0 (by norm_num) f hf s1
  have s3 := succ 1 (by norm_num) f hf s2
  have s4 := succ 2 (by norm_num) f hf s3
  interval_cases e
  · exact s0
  · exact s1
  · exact s2
  · exact s3
  · exact s4

@[expose] def V9.red (v : V9) : Prop := v.e0 < 5 ∧ v.e1 < 5 ∧ v.r.red

theorem mulV_red (v w : V9) : (mulV v w).red :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), mulR_red _ _ _⟩

theorem v9One_red : V9.one.red := ⟨by norm_num [V9.one], by norm_num [V9.one], rvOne_red⟩

theorem powV_red (v : V9) : ∀ k, (powV v k).red
  | 0 => v9One_red
  | _ + 1 => mulV_red _ _

theorem dec_red (i : ℕ) : (dec i).red :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), decR_red _⟩

theorem psi_one : psi u2 u1 b x V9.one = 1 := by
  simp [psi, V9.one, nfR_one]

theorem PcHyp.u1_pow_add (H : PcHyp u2 u1 b x) (e f : ℕ) (he : e < 5) (hf : f < 5) :
    u1 ^ e * u1 ^ f = u1 ^ ((e + f) % 5) * nfR b x (carry e f) := by
  unfold carry
  rw [← pow_add]
  by_cases h : e + f < 5
  · have h' : Nat.blt (e + f) 5 = true := by
      rw [Nat.blt_eq]
      exact h
    rw [h', cond_true, nfR_one, mul_one, Nat.mod_eq_of_lt h]
  · have h' : Nat.blt (e + f) 5 = false := by
      rw [Bool.eq_false_iff]
      intro h2
      rw [Nat.blt_eq] at h2
      exact h h2
    have hx2 : nfR b x CFSG.KC.MonPcFive.x2 = x ^ 2 := by
      simp [nfR, CFSG.KC.MonPcFive.x2]
    rw [h', cond_false, hx2, ← H.u15, ← pow_add]
    congr 1
    omega

theorem PcHyp.psi_mul (H : PcHyp u2 u1 b x) (C : TabChecks) {v w : V9} (hv : v.red)
    (hw : w.red) : psi u2 u1 b x v * psi u2 u1 b x w = psi u2 u1 b x (mulV v w) := by
  obtain ⟨he0, he1, hr⟩ := hv
  obtain ⟨hf0, hf1, hs⟩ := hw
  have hA : nfR b x v.r * (u2 ^ w.e0 * u1 ^ w.e1) =
      u2 ^ w.e0 * u1 ^ w.e1 * nfR b x (phi1At w.e1 (phi2At w.e0 v.r)) := by
    rw [← H.conj1 C hf1 (phi2At_red _ hr), ← H.conj2 C hf0 hr]
    group
  have hB : u1 ^ v.e1 * u2 ^ w.e0 = u2 ^ w.e0 * u1 ^ v.e1 * nfR b x (tauAt v.e1 w.e0) := by
    rw [mul_assoc, ← H.tau C v.e1 he1 w.e0 hf0]
    group
  have hC : nfR b x (tauAt v.e1 w.e0) * u1 ^ w.e1 =
      u1 ^ w.e1 * nfR b x (phi1At w.e1 (tauAt v.e1 w.e0)) := by
    rw [← H.conj1 C hf1 (tauAt_red _ he1 _ hf0)]
    group
  have h2 : u2 ^ v.e0 * u2 ^ w.e0 = u2 ^ ((v.e0 + w.e0) % 5) := by
    rw [← pow_add, pow_mod_five H.u25]
  have h1 := H.u1_pow_add v.e1 w.e1 he1 hf1
  unfold psi mulV
  simp only
  rw [← nfR_mul H.rel, ← nfR_mul H.rel, ← nfR_mul H.rel]
  calc u2 ^ v.e0 * u1 ^ v.e1 * nfR b x v.r * (u2 ^ w.e0 * u1 ^ w.e1 * nfR b x w.r)
      = u2 ^ v.e0 * u1 ^ v.e1 * (nfR b x v.r * (u2 ^ w.e0 * u1 ^ w.e1)) * nfR b x w.r := by group
    _ = u2 ^ v.e0 * (u1 ^ v.e1 * u2 ^ w.e0) * u1 ^ w.e1 *
          nfR b x (phi1At w.e1 (phi2At w.e0 v.r)) * nfR b x w.r := by
        rw [hA]
        group
    _ = u2 ^ v.e0 * u2 ^ w.e0 * u1 ^ v.e1 * (nfR b x (tauAt v.e1 w.e0) * u1 ^ w.e1) *
          nfR b x (phi1At w.e1 (phi2At w.e0 v.r)) * nfR b x w.r := by
        rw [hB]
        group
    _ = (u2 ^ v.e0 * u2 ^ w.e0) * (u1 ^ v.e1 * u1 ^ w.e1) *
          nfR b x (phi1At w.e1 (tauAt v.e1 w.e0)) *
          nfR b x (phi1At w.e1 (phi2At w.e0 v.r)) * nfR b x w.r := by
        rw [hC]
        group
    _ = _ := by
        rw [h2, h1]
        group

theorem PcHyp.psi_pow (H : PcHyp u2 u1 b x) (C : TabChecks) {v : V9} (hv : v.red) :
    ∀ k, psi u2 u1 b x v ^ k = psi u2 u1 b x (powV v k)
  | 0 => by rw [pow_zero, powV, psi_one]
  | k + 1 => by rw [pow_succ, H.psi_pow C hv k, powV, H.psi_mul C (powV_red _ _) hv]

end CFSG.KC.MonPcFive

end
