module

public import Certificates.Data.Kernel.StdOdd.RootOrbit
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.StdOdd.Orbit

open CFSG.KC.StdOdd.Orbit Matrix

@[expose] noncomputable def ptB (PL : List ℕ) (i : ℕ) : Fin 156 → ZMod 2 :=
  fun c => if (nthN PL c).testBit i then 1 else 0

@[expose] noncomputable def matB (M : ℕ) : Matrix (Fin 156) (Fin 156) (ZMod 2) :=
  Matrix.of fun c d => if M.testBit (156 * c + d) then 1 else 0

structure OrbitBits (PL : List ℕ) (A B n r : ℕ) : Prop where
  inj : ∀ i < n, ∀ j < n, ptB PL i = ptB PL j → i = j
  root_lt : r < n
  root : ∀ c : Fin 156, ptB PL r c = if (c : ℕ) = 14 then 1 else 0
  closA : ∀ i < n, ∃ j < n, ptB PL j = matB A *ᵥ ptB PL i
  closB : ∀ i < n, ∃ j < n, ptB PL j = matB B *ᵥ ptB PL i
  conn : ∃ dep : ℕ → ℕ, (∀ i < n, dep i = 0 → i = r) ∧
    ∀ i < n, 0 < dep i → ∃ j < n, dep j < dep i ∧
      (ptB PL i = matB A *ᵥ ptB PL j ∨ ptB PL i = matB B *ᵥ ptB PL j ∨
        ptB PL j = matB B *ᵥ ptB PL i)

theorem forceN_eq (y : ℕ) (k : ℕ → ℕ) : forceN y k = k y := by
  cases y <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

theorem nthN_cons_zero (x : ℕ) (l : List ℕ) : nthN (x :: l) 0 = x := rfl

theorem nthN_cons_succ (x : ℕ) (l : List ℕ) (i : ℕ) : nthN (x :: l) (i + 1) = nthN l i := rfl

theorem lenN_cons (x : ℕ) (l : List ℕ) : lenN (x :: l) = lenN l + 1 := rfl

theorem testBit_full (n i : ℕ) : (full n).testBit i = decide (i < n) := by
  change (1 <<< n - 1).testBit i = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

theorem exists_nthN {l : List ℕ} {x : ℕ} (h : x ∈ l) : ∃ c < lenN l, nthN l c = x := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by rw [lenN_cons]; omega, rfl⟩
    · obtain ⟨c, hc, e⟩ := ih h
      exact ⟨c + 1, by rw [lenN_cons]; omega, e⟩

theorem add_eq_xor_of_disj : ∀ (n a b : ℕ), a < 2 ^ n → b < 2 ^ n →
    (∀ q, a.testBit q = true → b.testBit q = false) → a + b = a ^^^ b
  | 0, a, b, ha, hb, _ => by
    have : a = 0 := by omega
    have : b = 0 := by omega
    subst_vars
    rfl
  | n + 1, a, b, ha, hb, hd => by
    have ea : a = 2 ^ 1 * (a / 2) + a % 2 := by omega
    have eb : b = 2 ^ 1 * (b / 2) + b % 2 := by omega
    have hd2 : ∀ q, (a / 2).testBit q = true → (b / 2).testBit q = false := by
      intro q hq
      rw [← Nat.testBit_succ] at hq ⊢
      exact hd _ hq
    have ih := add_eq_xor_of_disj n (a / 2) (b / 2) (by rw [Nat.pow_succ] at ha; omega)
      (by rw [Nat.pow_succ] at hb; omega) hd2
    have h0 : a % 2 + b % 2 = a % 2 ^^^ b % 2 := by
      rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> rw [h1, h2]
      · rfl
      · rfl
      · rfl
      · exfalso
        have := hd 0 (by rw [Nat.testBit_zero, h1]; rfl)
        rw [Nat.testBit_zero, h2] at this
        exact absurd this (by decide)
    have hlt : a % 2 ^^^ b % 2 < 2 ^ 1 :=
      Nat.xor_lt_two_pow (by omega) (by omega)
    have e : a + b = 2 ^ 1 * (a / 2 ^^^ b / 2) + (a % 2 ^^^ b % 2) := by
      rw [← ih, ← h0]
      omega
    rw [e]
    apply Nat.eq_of_testBit_eq
    intro q
    have ha' : a.testBit q = if q < 1 then (a % 2).testBit q else (a / 2).testBit (q - 1) := by
      conv_lhs => rw [ea]
      exact Nat.testBit_two_pow_mul_add _ (by omega) q
    have hb' : b.testBit q = if q < 1 then (b % 2).testBit q else (b / 2).testBit (q - 1) := by
      conv_lhs => rw [eb]
      exact Nat.testBit_two_pow_mul_add _ (by omega) q
    rw [Nat.testBit_two_pow_mul_add _ hlt, Nat.testBit_xor a b, ha', hb']
    split <;> simp only [Nat.testBit_xor]

theorem sub_land_eq (P m : ℕ) : P - (P &&& m) = P ^^^ (P &&& m) := by
  obtain ⟨n, hn⟩ : ∃ n, P < 2 ^ n := ⟨P, Nat.lt_two_pow_self⟩
  have hlt : P ^^^ (P &&& m) < 2 ^ n :=
    Nat.xor_lt_two_pow hn (Nat.lt_of_le_of_lt Nat.and_le_left hn)
  have e := add_eq_xor_of_disj n (P ^^^ (P &&& m)) (P &&& m) hlt
    (Nat.lt_of_le_of_lt Nat.and_le_left hn) (by
      intro q hq
      simp only [Nat.testBit_xor, Nat.testBit_and] at hq ⊢
      cases hP : P.testBit q <;> cases hm : m.testBit q <;> simp_all)
  have e2 : P ^^^ (P &&& m) ^^^ (P &&& m) = P := by
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [e2] at e
  omega

@[expose] def bz (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bz_xor (a b : Bool) : bz (a ^^ b) = bz a + bz b := by
  cases a <;> cases b <;> decide

theorem bz_inj {a b : Bool} (h : bz a = bz b) : a = b := by
  revert h
  cases a <;> cases b <;> decide

theorem ptB_eq (PL : List ℕ) (i : ℕ) (c : Fin 156) : ptB PL i c = bz ((nthN PL c).testBit i) :=
  rfl

@[expose] noncomputable def rowA (PL : List ℕ) : ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun P _ ih r acc => Bool.rec (motive := fun _ => Nat)
      (ih (Nat.shiftRight r (nat_lit 1)) (Nat.xor acc P))
      (ih (Nat.shiftRight r (nat_lit 1)) acc)
      (Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 0))) PL

theorem rowX_eq (r : ℕ) (PL : List ℕ) : rowX r PL = rowA PL r 0 := rfl

theorem rowA_nil (r acc : ℕ) : rowA [] r acc = acc := rfl

theorem rowA_cons (P : ℕ) (PL : List ℕ) (r acc : ℕ) :
    rowA (P :: PL) r acc = Bool.rec (motive := fun _ => ℕ) (rowA PL (r >>> 1) (acc ^^^ P))
      (rowA PL (r >>> 1) acc) (Nat.beq (r &&& 1) 0) := rfl

theorem rowA_bit : ∀ (PL : List ℕ) (r acc i : ℕ), bz ((rowA PL r acc).testBit i) =
    bz (acc.testBit i) +
      ∑ d ∈ Finset.range (lenN PL), bz (r.testBit d) * bz ((nthN PL d).testBit i)
  | [], r, acc, i => by
    rw [rowA_nil]
    simp [lenN]
  | P :: PL, r, acc, i => by
    rw [rowA_cons, lenN_cons, Finset.sum_range_succ']
    simp only [nthN_cons_succ, nthN_cons_zero]
    have hs : ∀ d, r.testBit (d + 1) = (r >>> 1).testBit d := by
      intro d
      rw [Nat.testBit_shiftRight, Nat.add_comm]
    simp only [hs]
    cases h : Nat.beq (r &&& 1) 0
    · have h1 : r % 2 ≠ 0 := by
        rw [← Nat.and_one_is_mod]
        exact Nat.ne_of_beq_eq_false h
      have h0 : r.testBit 0 = true := by
        rw [Nat.testBit_zero]
        simp only [decide_eq_true_eq]
        omega
      change bz ((rowA PL (r >>> 1) (acc ^^^ P)).testBit i) = _
      rw [rowA_bit PL, Nat.testBit_xor, bz_xor, h0]
      simp only [bz, ite_true]
      ring
    · have h1 : r % 2 = 0 := by
        rw [← Nat.and_one_is_mod]
        exact Nat.eq_of_beq_eq_true h
      have h0 : r.testBit 0 = false := by
        rw [Nat.testBit_zero]
        simp only [decide_eq_false_iff_not]
        omega
      change bz ((rowA PL (r >>> 1) acc).testBit i) = _
      rw [rowA_bit PL, h0]
      simp only [bz, Bool.false_eq_true, ite_false, zero_mul, add_zero]

theorem rowX_bit {PL : List ℕ} (hl : lenN PL = 156) (M : ℕ) (c : Fin 156) (i : ℕ) :
    bz ((rowX (M >>> (156 * (c : ℕ))) PL).testBit i) = (matB M *ᵥ ptB PL i) c := by
  rw [rowX_eq, rowA_bit, hl, Nat.zero_testBit, Finset.sum_range]
  simp only [bz, Bool.false_eq_true, ite_false, zero_add, Matrix.mulVec, dotProduct, matB,
    Matrix.of_apply, ptB, Nat.testBit_shiftRight]

@[expose] def swp (d m q : ℕ) : ℕ :=
  if m.testBit q = true then q + d else if d ≤ q ∧ m.testBit (q - d) = true then q - d else q

@[expose] def Disj (d m : ℕ) : Prop := ∀ q, m.testBit q = true → m.testBit (q + d) = false

theorem disj_of {d m : ℕ} (h : Nat.land m (Nat.shiftLeft m d) = 0) : Disj d m := by
  intro q hq
  have := congrArg (fun x => x.testBit (q + d)) h
  change (m &&& (m <<< d)).testBit (q + d) = (0 : ℕ).testBit (q + d) at this
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit, Nat.add_sub_cancel, hq] at this
  simpa using this

theorem swp_swp {d m : ℕ} (h : Disj d m) (q : ℕ) : swp d m (swp d m q) = q := by
  by_cases h1 : m.testBit q = true
  · have h2 := h q h1
    have e : swp d m q = q + d := by simp [swp, h1]
    rw [e]
    simp [swp, h2, h1]
  · by_cases h3 : d ≤ q ∧ m.testBit (q - d) = true
    · have e : swp d m q = q - d := by simp [swp, h1, h3]
      rw [e]
      have e2 : q - d + d = q := by omega
      simp [swp, h3.2, e2]
    · have e : swp d m q = q := by simp [swp, h1, h3]
      rw [e, e]

theorem dsw_eq (d m x : ℕ) :
    dsw d m x = x ^^^ ((((x >>> d) ^^^ x) &&& m) ^^^ ((((x >>> d) ^^^ x) &&& m) <<< d)) := by
  unfold dsw
  rw [forceN_eq]
  rfl

theorem testBit_dsw {d m : ℕ} (h : Disj d m) (x q : ℕ) :
    (dsw d m x).testBit q = x.testBit (swp d m q) := by
  rw [dsw_eq]
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  unfold swp
  by_cases h1 : m.testBit q = true
  · have h0 : ∀ hd : d ≤ q, m.testBit (q - d) = false := by
      intro hd
      cases h2 : m.testBit (q - d)
      · rfl
      · have := h (q - d) h2
        rw [Nat.sub_add_cancel hd, h1] at this
        exact absurd this (by decide)
    rw [ite_eq_left h1, Nat.add_comm q d]
    by_cases hd : d ≤ q
    · simp only [h1, h0 hd, Bool.and_false, Bool.and_true, Bool.xor_false]
      cases x.testBit q <;> cases x.testBit (d + q) <;> rfl
    · have : decide (q ≥ d) = false := by simp; omega
      simp only [h1, this, Bool.false_and, Bool.and_true]
      cases x.testBit q <;> cases x.testBit (d + q) <;> rfl
  · simp only [Bool.not_eq_true] at h1
    rw [ite_eq_right (by simp [h1])]
    by_cases h3 : d ≤ q ∧ m.testBit (q - d) = true
    · rw [ite_eq_left h3]
      have e : d + (q - d) = q := by omega
      have hd : decide (q ≥ d) = true := by simp; omega
      simp only [h1, h3.2, hd, e, Bool.and_false, Bool.true_and, Bool.and_true]
      cases x.testBit q <;> cases x.testBit (q - d) <;> rfl
    · rw [ite_eq_right h3]
      have : (decide (q ≥ d) && m.testBit (q - d)) = false := by
        cases hd : decide (q ≥ d)
        · rfl
        · simp only [Bool.true_and]
          cases h4 : m.testBit (q - d)
          · rfl
          · exact absurd ⟨by simpa using hd, h4⟩ h3
      simp only [h1, Bool.and_false]
      cases hd : decide (q ≥ d)
      · simp
      · have h4 : m.testBit (q - d) = false := by simpa [hd] using this
        simp [h4]

@[expose] def tau : List ℕ → List ℕ → ℕ → ℕ
  | d :: Ds, m :: Ms, q => swp d m (tau Ds Ms q)
  | _, _, q => q

@[expose] def tauR : List ℕ → List ℕ → ℕ → ℕ
  | d :: Ds, m :: Ms, q => tauR Ds Ms (swp d m q)
  | _, _, q => q

theorem net_cons (d m : ℕ) (Ds Ms : List ℕ) (x : ℕ) :
    net (d :: Ds) (m :: Ms) x = net Ds Ms (dsw d m x) :=
  forceN_eq _ _

theorem netRev_cons (d m : ℕ) (Ds Ms : List ℕ) (x : ℕ) :
    netRev (d :: Ds) (m :: Ms) x = dsw d m (netRev Ds Ms x) :=
  forceN_eq _ _

theorem stagesOK_cons (d m : ℕ) (Ds Ms : List ℕ) :
    stagesOK (d :: Ds) (m :: Ms) =
      andB (Nat.beq (Nat.land m (Nat.shiftLeft m d)) 0) (stagesOK Ds Ms) := rfl

theorem disj_of_stagesOK {d m : ℕ} {Ds Ms : List ℕ} (h : stagesOK (d :: Ds) (m :: Ms) = true) :
    Disj d m ∧ stagesOK Ds Ms = true := by
  rw [stagesOK_cons, andB_eq, Bool.and_eq_true] at h
  exact ⟨disj_of (Nat.eq_of_beq_eq_true h.1), h.2⟩

theorem testBit_net : ∀ (Ms Ds : List ℕ), stagesOK Ds Ms = true →
    ∀ x q, (net Ds Ms x).testBit q = x.testBit (tau Ds Ms q)
  | [], Ds, _, x, q => by cases Ds <;> rfl
  | _ :: _, [], _, x, q => rfl
  | m :: Ms, d :: Ds, h, x, q => by
    obtain ⟨h1, h2⟩ := disj_of_stagesOK h
    rw [net_cons, testBit_net Ms Ds h2, testBit_dsw h1]
    rfl

theorem testBit_netRev : ∀ (Ms Ds : List ℕ), stagesOK Ds Ms = true →
    ∀ x q, (netRev Ds Ms x).testBit q = x.testBit (tauR Ds Ms q)
  | [], Ds, _, x, q => by cases Ds <;> rfl
  | _ :: _, [], _, x, q => rfl
  | m :: Ms, d :: Ds, h, x, q => by
    obtain ⟨h1, h2⟩ := disj_of_stagesOK h
    rw [netRev_cons, testBit_dsw h1, testBit_netRev Ms Ds h2]
    rfl

theorem tau_tauR : ∀ (Ms Ds : List ℕ), stagesOK Ds Ms = true →
    ∀ q, tau Ds Ms (tauR Ds Ms q) = q
  | [], Ds, _, q => by cases Ds <;> rfl
  | _ :: _, [], _, q => rfl
  | m :: Ms, d :: Ds, h, q => by
    obtain ⟨h1, h2⟩ := disj_of_stagesOK h
    change swp d m (tau Ds Ms (tauR Ds Ms (swp d m q))) = q
    rw [tau_tauR Ms Ds h2, swp_swp h1]

theorem tau_lt_iff {Ds Ms : List ℕ} {n : ℕ} (hv : stagesOK Ds Ms = true)
    (hf : Nat.beq (net Ds Ms (full n)) (full n) = true) (q : ℕ) : tau Ds Ms q < n ↔ q < n := by
  have := congrArg (fun x => x.testBit q) (Nat.eq_of_beq_eq_true hf)
  simp only [testBit_net Ms Ds hv, testBit_full, decide_eq_decide] at this
  exact this

theorem tauR_lt_iff {Ds Ms : List ℕ} {n : ℕ} (hv : stagesOK Ds Ms = true)
    (hf : Nat.beq (net Ds Ms (full n)) (full n) = true) (q : ℕ) : tauR Ds Ms q < n ↔ q < n := by
  rw [← tau_lt_iff hv hf, tau_tauR Ms Ds hv]

theorem pt_rel {PL Ds Ms : List ℕ} {M : ℕ} (hl : lenN PL = 156) (hv : stagesOK Ds Ms = true)
    (hc : ∀ c < 156, closeOK Ds Ms M PL c = true) (i : ℕ) :
    ptB PL i = matB M *ᵥ ptB PL (tau Ds Ms i) := by
  funext c
  have e := Nat.eq_of_beq_eq_true (hc c c.2)
  change net Ds Ms (rowX (M >>> (156 * (c : ℕ))) PL) = nthN PL c at e
  have := congrArg (fun x => x.testBit i) e
  simp only [testBit_net Ms Ds hv] at this
  rw [← rowX_bit hl M c (tau Ds Ms i), this, ptB_eq]

@[expose] noncomputable def sigA (PL : List ℕ) : List ℕ → List ℕ → Bool → List ℕ :=
  List.rec (motive := fun _ => List Nat → List Nat → Bool → List Nat)
    (fun ev od _ => List.rec (motive := fun _ => List Nat) ev (fun x _ ih => List.cons x ih) od)
    (fun x _ ih ev od par => Bool.rec (motive := fun _ => List Nat)
      (ih (List.cons x ev) od true) (ih ev (List.cons x od) false) par)
    PL

theorem mem_rec_cons {ev od : List ℕ} {y : ℕ}
    (h : y ∈ List.rec (motive := fun _ => List ℕ) ev (fun x _ ih => List.cons x ih) od) :
    y ∈ ev ∨ y ∈ od := by
  induction od with
  | nil => exact Or.inl h
  | cons x od ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inr List.mem_cons_self
    · rcases ih h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_sigA : ∀ (PL ev od : List ℕ) (par : Bool) (y : ℕ), y ∈ sigA PL ev od par →
    y ∈ PL ∨ y ∈ ev ∨ y ∈ od
  | [], ev, od, _, y, h => Or.inr (mem_rec_cons h)
  | x :: PL, ev, od, par, y, h => by
    cases par
    · rcases mem_sigA PL (x :: ev) od true y h with h | h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inl List.mem_cons_self
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases mem_sigA PL ev (x :: od) false y h with h | h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr (Or.inl h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inl List.mem_cons_self
        · exact Or.inr (Or.inr h)

theorem mem_sigPlanes {PL : List ℕ} {y : ℕ} (h : y ∈ sigPlanes PL) : y ∈ PL := by
  rcases mem_sigA PL [] [] false y h with h | h | h
  · exact h
  · cases h
  · cases h

@[expose] noncomputable def ltA (L : List ℕ) : ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun lt _ => lt)
    (fun x _ ih lt eq => sortStep x lt eq ih) L

theorem ltA_cons (x : ℕ) (L : List ℕ) (lt eq : ℕ) :
    ltA (x :: L) lt eq = sortStep x lt eq (ltA L) := rfl

theorem sortStep_eq (x lt eq : ℕ) (k : ℕ → ℕ → ℕ) :
    sortStep x lt eq k = k (lt ||| ((eq &&& (x >>> 1)) - ((eq &&& (x >>> 1)) &&& x)))
      (eq - (eq &&& (x ^^^ (x >>> 1)))) := by
  unfold sortStep
  simp only [forceN_eq]
  rfl

@[expose] def hv (i a : ℕ) (L : List ℕ) : ℕ := L.foldl (fun a x => 2 * a + (x.testBit i).toNat) a

theorem hv_congr {i j : ℕ} : ∀ (L : List ℕ), (∀ y ∈ L, y.testBit i = y.testBit j) →
    ∀ a, hv i a L = hv j a L
  | [], _, a => rfl
  | x :: L, h, a => by
    change hv i (2 * a + (x.testBit i).toNat) L = hv j (2 * a + (x.testBit j).toNat) L
    rw [h x List.mem_cons_self]
    exact hv_congr L (fun y hy => h y (List.mem_cons_of_mem _ hy)) _

theorem ltA_spec : ∀ (L : List ℕ) (a : ℕ → ℕ) (lt eq : ℕ),
    (∀ i, lt.testBit i = true → a i < a (i + 1)) →
    (∀ i, eq.testBit i = true → a i = a (i + 1)) →
    ∀ i, (ltA L lt eq).testBit i = true → hv i (a i) L < hv (i + 1) (a (i + 1)) L
  | [], _, _, _, hlt, _, i, h => hlt i h
  | x :: L, a, lt, eq, hlt, heq, i, h => by
    rw [ltA_cons, sortStep_eq] at h
    refine ltA_spec L (fun i => 2 * a i + (x.testBit i).toNat) _ _ (fun i hi => ?_)
      (fun i hi => ?_) i h
    · simp only [Nat.testBit_or, sub_land_eq, Nat.testBit_xor, Nat.testBit_and,
        Nat.testBit_shiftRight, Nat.add_comm 1 i] at hi
      have h1 := hlt i
      have h2 := heq i
      revert hi h1 h2
      cases lt.testBit i <;> cases eq.testBit i <;> cases x.testBit i <;>
        cases x.testBit (i + 1) <;> intro hi h1 h2 <;> simp at hi h1 h2 ⊢ <;> omega
    · simp only [sub_land_eq, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight,
        Nat.add_comm 1 i] at hi
      have h2 := heq i
      revert hi h2
      cases eq.testBit i <;> cases x.testBit i <;> cases x.testBit (i + 1) <;>
        intro hi h2 <;> simp at hi h2 ⊢ <;> omega

theorem sort_inj {PL : List ℕ} {n : ℕ} (hl : lenN PL = 156) (h : sortOK PL n = true) :
    ∀ i < n, ∀ j < n, ptB PL i = ptB PL j → i = j := by
  have e : ltA (sigPlanes PL) 0 (full (n - 1)) = full (n - 1) := Nat.eq_of_beq_eq_true h
  have key : ∀ i, i + 1 < n → hv i 0 (sigPlanes PL) < hv (i + 1) 0 (sigPlanes PL) := by
    intro i hi
    refine ltA_spec (sigPlanes PL) (fun _ => 0) 0 (full (n - 1)) ?_ (fun _ _ => rfl) i ?_
    · intro i h
      rw [Nat.zero_testBit] at h
      cases h
    · rw [e, testBit_full]
      simp only [decide_eq_true_eq]
      omega
  have mono : ∀ i j, i < j → j < n → hv i 0 (sigPlanes PL) < hv j 0 (sigPlanes PL) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
      · exact Nat.lt_trans (ih h (by omega)) (key j hj)
      · exact key i hj
  have cong : ∀ i j, ptB PL i = ptB PL j → hv i 0 (sigPlanes PL) = hv j 0 (sigPlanes PL) := by
    intro i j hp
    refine hv_congr _ (fun y hy => ?_) 0
    obtain ⟨c, hc, rfl⟩ := exists_nthN (mem_sigPlanes hy)
    rw [hl] at hc
    have := congrFun hp ⟨c, hc⟩
    rw [ptB_eq, ptB_eq] at this
    exact bz_inj this
  intro i hi j hj hp
  have := cong i j hp
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd this (Nat.ne_of_lt (mono i j h hj))
  · exact h
  · exact absurd this.symm (Nat.ne_of_lt (mono j i h hi))

theorem colEq_spec : ∀ (PL : List ℕ) (r pat : ℕ), colEq PL r pat = true →
    ∀ c < lenN PL, (nthN PL c).testBit r = pat.testBit c
  | [], _, _, _, c, hc => absurd hc (Nat.not_lt_zero c)
  | P :: PL, r, pat, h, c, hc => by
    change andB (Nat.beq ((P >>> r) &&& 1) (pat &&& 1)) (colEq PL r (pat >>> 1)) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    cases c with
    | zero =>
      have := congrArg (fun y => y.testBit 0) (Nat.eq_of_beq_eq_true h.1)
      simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_one_zero, Bool.and_true,
        Nat.add_zero] at this
      exact this
    | succ c =>
      rw [nthN_cons_succ, colEq_spec PL r (pat >>> 1) h.2 c (by rw [lenN_cons] at hc; omega),
        Nat.testBit_shiftRight, Nat.add_comm]

theorem rootOrbit_sound {PL DA MA DB MB RS : List ℕ} {A B n r D : ℕ}
    (hl : Nat.beq (lenN PL) 156 = true) (hr : Nat.blt r n = true) (hroot : rootOK PL r = true)
    (hsort : sortOK PL n = true) (hvA : stagesOK DA MA = true) (hvB : stagesOK DB MB = true)
    (hfA : Nat.beq (net DA MA (full n)) (full n) = true)
    (hfB : Nat.beq (net DB MB (full n)) (full n) = true)
    (hcA : ∀ c < 156, closeOK DA MA A PL c = true) (hcB : ∀ c < 156, closeOK DB MB B PL c = true)
    (h0 : Nat.beq (nthN RS 0) (Nat.shiftLeft 1 r) = true)
    (hs : ∀ k < D, Nat.beq (stepN DA MA DB MB (nthN RS k)) (nthN RS (k + 1)) = true)
    (hD : Nat.beq (nthN RS D) (full n) = true) :
    OrbitBits PL A B n r := by
  classical
  have hl' : lenN PL = 156 := Nat.eq_of_beq_eq_true hl
  have hrn : r < n := Nat.le_of_ble_eq_true hr
  have relA := pt_rel hl' hvA hcA
  have relB := pt_rel hl' hvB hcB
  have hin : ∀ i < n, (nthN RS D).testBit i = true := by
    intro i hi
    rw [Nat.eq_of_beq_eq_true hD, testBit_full]
    simpa using hi
  have step : ∀ k < D, ∀ i, (nthN RS (k + 1)).testBit i =
      (((nthN RS k).testBit i || (nthN RS k).testBit (tau DA MA i)) ||
        ((nthN RS k).testBit (tau DB MB i) || (nthN RS k).testBit (tauR DB MB i))) := by
    intro k hk i
    have e := Nat.eq_of_beq_eq_true (hs k hk)
    change ((nthN RS k ||| net DA MA (nthN RS k)) |||
      (net DB MB (nthN RS k) ||| netRev DB MB (nthN RS k))) = nthN RS (k + 1) at e
    rw [← e, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, testBit_net MA DA hvA,
      testBit_net MB DB hvB, testBit_netRev MB DB hvB]
  refine ⟨sort_inj hl' hsort, hrn, ?_, ?_, ?_, ?_⟩
  · intro c
    have := colEq_spec PL r _ hroot c (by rw [hl']; exact c.2)
    rw [ptB_eq, this]
    change bz ((1 <<< 14 : ℕ).testBit c) = _
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases hc : (c : ℕ) = 14
    · simp [bz, hc]
    · have : ¬ (14 = (c : ℕ)) := fun h => hc h.symm
      simp [bz, hc, this]
  · intro i hi
    refine ⟨tauR DA MA i, (tauR_lt_iff hvA hfA i).2 hi, ?_⟩
    rw [relA (tauR DA MA i), tau_tauR MA DA hvA]
  · intro i hi
    refine ⟨tauR DB MB i, (tauR_lt_iff hvB hfB i).2 hi, ?_⟩
    rw [relB (tauR DB MB i), tau_tauR MB DB hvB]
  · let P : ℕ → ℕ → Prop := fun i k => (nthN RS k).testBit i = true
    have hex : ∀ i < n, ∃ k, P i k := fun i hi => ⟨D, hin i hi⟩
    refine ⟨fun i => if h : ∃ k, P i k then Nat.find h else 0, ?_, ?_⟩
    · intro i hi hz
      have hm := Nat.find_spec (hex i hi)
      simp only [dite_eq_left (hex i hi)] at hz
      rw [hz] at hm
      change (nthN RS 0).testBit i = true at hm
      rw [Nat.eq_of_beq_eq_true h0] at hm
      change (1 <<< r).testBit i = true at hm
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hm
      exact (of_decide_eq_true hm).symm
    · intro i hi hpos
      simp only [dite_eq_left (hex i hi)] at hpos ⊢
      obtain ⟨k, hk⟩ : ∃ k, Nat.find (hex i hi) = k + 1 := ⟨Nat.find (hex i hi) - 1, by omega⟩
      have hm : (nthN RS (k + 1)).testBit i = true := hk ▸ Nat.find_spec (hex i hi)
      have hkD : k < D := by
        have := Nat.find_min' (hex i hi) (hin i hi)
        omega
      have hnot : ¬ (nthN RS k).testBit i = true := Nat.find_min (hex i hi) (by omega)
      have hlt : ∀ j < n, (nthN RS k).testBit j = true →
          (if h : ∃ k, P j k then Nat.find h else 0) < Nat.find (hex i hi) := by
        intro j hj hb
        rw [dite_eq_left (hex j hj), hk]
        have := Nat.find_min' (hex j hj) hb
        omega
      rw [step k hkD] at hm
      simp only [Bool.or_eq_true] at hm
      rcases hm with (hm | hm) | (hm | hm)
      · exact absurd hm hnot
      · have hj := (tau_lt_iff hvA hfA i).2 hi
        exact ⟨_, hj, hlt _ hj hm, Or.inl (relA i)⟩
      · have hj := (tau_lt_iff hvB hfB i).2 hi
        exact ⟨_, hj, hlt _ hj hm, Or.inr (Or.inl (relB i))⟩
      · have hj := (tauR_lt_iff hvB hfB i).2 hi
        refine ⟨_, hj, hlt _ hj hm, Or.inr (Or.inr ?_)⟩
        rw [relB (tauR DB MB i), tau_tauR MB DB hvB]

end CFSG.KS.StdOdd.Orbit

end
