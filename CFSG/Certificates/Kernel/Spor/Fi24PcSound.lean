module

public import Certificates.Data.Kernel.Spor.Fi24Pc
public import CFSG.Certificates.Kernel.Spor.Fi24PcGroup
public import CFSG.Certificates.Kernel.Spor.Fi24NetPtSound
import CFSG.Certificates.Kernel.Spor.Fi24FixSound
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.Fi24Pc

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24Pc CFSG.KS.Fi24NetPt CFSG.KC.Fi24NetPt CFSG.KC.Fi24Net

theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem bIf_eq (c a b : Bool) : bIf(c, a, b) = if c then a else b := by cases c <;> rfl

theorem nIf_eq (c : Bool) (a b : Nat) : nIf(c, a, b) = if c then a else b := by cases c <;> rfl

theorem beq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b := ⟨Nat.eq_of_beq_eq_true, fun h => by
  rw [h]; exact Nat.beq_refl b⟩

theorem blt_iff {a b : Nat} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem two_pow_two_mul (k : Nat) : 2 ^ (k * 2 ^ 1) = 4 ^ k := by
  rw [pow_one, mul_comm, pow_mul]
  norm_num

theorem ex_eq (u k : Nat) : ex u k = dg u k := by
  unfold ex dg
  change (u >>> (k <<< 1)) &&& (2 ^ 2 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, two_pow_two_mul]

theorem gw_eq (i : Nat) : gw i = 4 ^ i := by
  unfold gw
  change 1 <<< (i <<< 1) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, two_pow_two_mul]

theorem lowM_eq (i : Nat) : lowM i = 4 ^ i - 1 := by
  unfold lowM
  rw [gw_eq]
  rfl

theorem mod_four_pow_eq_zero : ∀ i u, u % 4 ^ i = 0 ↔ ∀ k < i, dg u k = 0
  | 0, u => by simp [Nat.mod_one]
  | i + 1, u => by
    rw [pow_succ', Nat.mod_mul]
    have hd : ∀ k, dg u (k + 1) = dg (u / 4) k := fun k => by
      unfold dg
      rw [pow_succ', Nat.div_div_eq_div_mul]
    constructor
    · intro h k hk
      have h0 : u % 4 = 0 := by omega
      have h1 : u / 4 % 4 ^ i = 0 := by omega
      rcases k with _ | k
      · simpa [dg] using h0
      · rw [hd]
        exact (mod_four_pow_eq_zero i (u / 4)).1 h1 k (by omega)
    · intro h
      have h0 : u % 4 = 0 := by simpa [dg] using h 0 (by omega)
      have h1 := (mod_four_pow_eq_zero i (u / 4)).2 fun k hk => by rw [← hd]; exact h (k + 1) (by omega)
      rw [h0, h1]

private theorem two_pow_two_mul' (k : Nat) : 2 ^ (2 * k) = 4 ^ k := by
  rw [show (4 : Nat) = 2 ^ 2 by norm_num]
  exact pow_mul 2 2 k

private theorem testBit_1431655765 {k : Nat} (hk : k < 16) :
    (1431655765 : Nat).testBit (2 * k) = true := by
  have h : ∀ k < 16, (1431655765 : Nat).testBit (2 * k) = true := by decide
  exact h k hk

private theorem testBit_two_mul_of_dg_eq_three {u k : Nat} (h : dg u k = 3) :
    u.testBit (2 * k) = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, two_pow_two_mul']
  have hq : u / 4 ^ k % 2 = 1 := by
    have h' := Nat.mod_mod_of_dvd (u / 4 ^ k) (by norm_num : 2 ∣ 4)
    unfold dg at h
    rw [← h', h]
  simp [hq]

private theorem testBit_two_mul_succ_of_dg_eq_three {u k : Nat} (h : dg u k = 3) :
    u.testBit (2 * k + 1) = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hp : 2 ^ (2 * k + 1) = 4 ^ k * 2 := by
    rw [pow_succ, two_pow_two_mul']
  rw [hp, ← Nat.div_div_eq_div_mul]
  have hq : u / 4 ^ k / 2 % 2 = 1 := by
    unfold dg at h
    omega
  simp [hq]

theorem nwOK_spec {u : Nat} (h : nwOK u = true) : u < 4 ^ 16 ∧ ∀ k, dg u k < 3 := by
  rw [nwOK, andB_eq, Bool.and_eq_true, blt_iff, beq_iff] at h
  obtain ⟨h1, h2⟩ := h
  have h2' : (u &&& (u >>> 1)) &&& 1431655765 = 0 := by
    simpa only [Nat.land_eq, Nat.shiftRight_eq'] using h2
  constructor
  · rw [show (4 : Nat) ^ 16 = 4294967296 by norm_num]
    exact h1
  · intro k
    rcases Nat.lt_or_ge k 16 with hk | hk
    · have hne : dg u k ≠ 3 := by
        intro hd
        have hbit : ((u &&& (u >>> 1)) &&& 1431655765).testBit (2 * k) = true := by
          rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight,
            show 1 + 2 * k = 2 * k + 1 by omega, testBit_1431655765 hk,
            testBit_two_mul_of_dg_eq_three hd, testBit_two_mul_succ_of_dg_eq_three hd]
          rfl
        rw [h2', Nat.zero_testBit] at hbit
        exact Bool.false_ne_true hbit
      have h4 : dg u k < 4 := Nat.mod_lt _ (by norm_num)
      omega
    · have hu : u < 4 ^ k := by
        refine lt_of_lt_of_le ?_ (Nat.pow_le_pow_right (by norm_num) hk)
        rw [show (4 : Nat) ^ 16 = 4294967296 by norm_num]
        exact h1
      unfold dg
      rw [Nat.div_eq_of_lt hu]
      norm_num

theorem dg_lt_four (u k : Nat) : dg u k < 4 := Nat.mod_lt _ (by norm_num)

theorem land_lowM_eq_zero {u i : Nat} : Nat.land u (lowM i) = 0 ↔ ∀ k < i, dg u k = 0 := by
  rw [lowM_eq, ← mod_four_pow_eq_zero]
  change u &&& (4 ^ i - 1) = 0 ↔ _
  rw [show (4 : ℕ) ^ i = 2 ^ (i * 2 ^ 1) from (two_pow_two_mul i).symm, Nat.and_two_pow_sub_one_eq_mod]

theorem land_lowM_eq_gw {c k : Nat} (h : Nat.land c (lowM (k + 1)) = gw k) :
    (∀ m < k, dg c m = 0) ∧ dg c k = 1 := by
  rw [lowM_eq, gw_eq] at h
  change c &&& (4 ^ (k + 1) - 1) = _ at h
  rw [show (4 : ℕ) ^ (k + 1) = 2 ^ ((k + 1) * 2 ^ 1) from (two_pow_two_mul _).symm,
    Nat.and_two_pow_sub_one_eq_mod, two_pow_two_mul] at h
  refine ⟨fun m hm => ?_, ?_⟩
  · have h1 : c % 4 ^ k = 0 := by
      have := Nat.mod_mod_of_dvd c (pow_dvd_pow 4 (Nat.le_succ k))
      rw [← this, h, Nat.mod_self]
    exact (mod_four_pow_eq_zero k c).1 h1 m hm
  · unfold dg
    have e : c / 4 ^ k % 4 = c % 4 ^ (k + 1) / 4 ^ k := by
      rw [pow_succ, Nat.mod_mul_right_div_self]
    rw [e, h, Nat.div_self (by positivity)]

theorem apP_nil (f : Nat → Nat → Nat) (x : Nat) : apP f [] x = x := rfl

theorem apP_cons (f : Nat → Nat → Nat) (l : Nat) (w : List Nat) (x : Nat) :
    apP f (l :: w) x = f l (apP f w x) := strictN_eq _ _

theorem apP_eq (f : Nat → Nat → Nat) (w : List Nat) (x : Nat) : apP f w x = w.foldr f x := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [apP_cons, ih, List.foldr_cons]

theorem eqP_spec {f : Nat → Nat → Nat} {B u v : List Nat} (h : eqP f B u v = true) :
    ∀ b ∈ B, u.foldr f b = v.foldr f b := by
  induction B with
  | nil => simp
  | cons b B ih =>
    have h' : (Nat.beq (apP f u b) (apP f v b) && eqP f B u v) = true := by
      rw [← bAnd_eq]; exact h
    rw [Bool.and_eq_true, beq_iff] at h'
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rw [← apP_eq, ← apP_eq]; exact h'.1
    · exact ih h'.2 c hc

open CFSG.KS.Fi24Net in
theorem testBit_walkP {W : Nat → Nat → Nat} : ∀ (w : List Nat), (∀ l ∈ w, NV (W (l / 2))) →
    ∀ v q, (walkP W w v).testBit q = v.testBit (w.foldr (LN W) q)
  | [], _, _, _ => rfl
  | l :: w, h, v, q => by
    have e : walkP W (l :: w) v = walkP W w (planeL W l v) := strictN_eq _ _
    rw [e, testBit_walkP w (fun l' hl' => h l' (List.mem_cons_of_mem l hl')) (planeL W l v) q,
      testBit_planeL (h l List.mem_cons_self)]
    rfl

open CFSG.KS.Fi24Net in
theorem LN_lt19 {W : Nat → Nat → Nat} {l : Nat} (hl : NV (W (l / 2))) {q : Nat} (hq : q < 524288) :
    LN W l q < 524288 := by
  unfold LN
  split_ifs
  · exact pF_lt hl hq
  · exact pR_lt hl hq

open CFSG.KS.Fi24Net in
theorem foldr_LN_lt {W : Nat → Nat → Nat} : ∀ (w : List Nat), (∀ l ∈ w, NV (W (l / 2))) →
    ∀ q < 524288, w.foldr (LN W) q < 524288
  | [], _, _, hq => hq
  | l :: w, h, q, hq => LN_lt19 (h l List.mem_cons_self)
      (foldr_LN_lt w (fun l' hl' => h l' (List.mem_cons_of_mem l hl')) q hq)

open CFSG.KS.Fi24Net in
theorem pcw_spec {NW XW : Nat → Nat → Nat} {words : List (List Nat)} {defs : List Nat} {j : Nat}
    (hj : NV (XW j)) (hw : ∀ l ∈ genW words defs j, NV ((if j < 4 then NW else XW) (l / 2)))
    (h : ∀ k < 19, pcwOK NW XW words defs j k = true) :
    ∀ q < 524288, pF (XW j) q = (genW words defs j).foldr (LN (if j < 4 then NW else XW)) q := by
  refine perm_of_tpl (fun q hq => pF_lt hj hq) (fun q hq => foldr_LN_lt _ hw q hq) ?_
  intro k hk q _
  have e := h k hk
  unfold pcwOK at e
  rw [CFSG.KS.Fi24Net.letB_eq'] at e
  by_cases h4 : j < 4
  · have hb : Nat.blt j 4 = true := blt_iff.2 h4
    rw [hb] at e
    change Nat.beq (walkP NW (genW words defs j) (tpl k)) (netF (XW j) (tpl k)) = true at e
    have e2 : (walkP NW (genW words defs j) (tpl k)).testBit q = (netF (XW j) (tpl k)).testBit q := by
      rw [Nat.eq_of_beq_eq_true e]
    simp only [if_pos h4] at hw ⊢
    rw [testBit_walkP _ hw, testBit_netF hj] at e2
    exact e2.symm
  · have hb : Nat.blt j 4 = false := by
      cases e' : Nat.blt j 4
      · rfl
      · exact absurd (blt_iff.1 e') h4
    rw [hb] at e
    change Nat.beq (walkP XW (genW words defs j) (tpl k)) (netF (XW j) (tpl k)) = true at e
    have e2 : (walkP XW (genW words defs j) (tpl k)).testBit q = (netF (XW j) (tpl k)).testBit q := by
      rw [Nat.eq_of_beq_eq_true e]
    simp only [if_neg h4] at hw ⊢
    rw [testBit_walkP _ hw, testBit_netF hj] at e2
    exact e2.symm

section Act

variable {G : Type*} [Group G] (act : G → Nat → Nat) (hmul : ∀ g h p, act (g * h) p = act g (act h p))
  (hone : ∀ p, act 1 p = p)
include hmul hone

theorem act_pow (g : G) (n p : Nat) : act (g ^ n) p = (act g)^[n] p := by
  induction n generalizing p with
  | zero => rw [pow_zero, hone]; rfl
  | succ n ih => rw [pow_succ, hmul, ih, Function.iterate_succ_apply]

theorem act_prod (l : List G) (p : Nat) : act l.prod p = l.foldr act p := by
  induction l with
  | nil => rw [List.prod_nil, hone]; rfl
  | cons g l ih => rw [List.prod_cons, hmul, ih, List.foldr_cons]

theorem nwL_act (x : ℕ → G) (f : Nat → Nat → Nat) (hf : ∀ k < 16, ∀ p, f (2 * k) p = act (x k) p)
    {u : Nat} (hu : ∀ k, dg u k < 3) (p : Nat) : (nwL u).foldr f p = act (nv x u) p := by
  have key : ∀ j ≤ 16, ∀ p, (Nat.rec (motive := fun _ => List Nat) List.nil
      (fun j ih => (fun k => (fun e =>
        Bool.rec (motive := fun _ => List Nat)
          (Bool.rec (motive := fun _ => List Nat) (List.cons (Nat.shiftLeft k (nat_lit 1))
            (List.cons (Nat.shiftLeft k (nat_lit 1)) ih))
            (List.cons (Nat.shiftLeft k (nat_lit 1)) ih) (Nat.beq e (nat_lit 1)))
          ih (Nat.beq e (nat_lit 0))) (ex u k)) (Nat.sub (nat_lit 15) j)) j).foldr f p =
        act (nvFrom x u (16 - j)) p := by
    intro j hj
    induction j with
    | zero => intro p; rw [nvFrom_of_ge le_rfl, hone]; rfl
    | succ j ih =>
      intro p
      have hk : 15 - j < 16 := by omega
      have e16 : 16 - (j + 1) = 15 - j := by omega
      rw [e16, nvFrom_succ hk, show 15 - j + 1 = 16 - j by omega, hmul, ← ih (by omega)]
      change (Bool.rec (motive := fun _ => List Nat) _ _ _).foldr f p = _
      have hs : Nat.shiftLeft (15 - j) 1 = 2 * (15 - j) := by
        rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, pow_one, mul_comm]
      rw [show Nat.sub 15 j = 15 - j from rfl, ex_eq]
      have hd := dg_lt_four u (15 - j)
      rcases (by omega : dg u (15 - j) = 0 ∨ dg u (15 - j) = 1 ∨ dg u (15 - j) = 2 ∨ dg u (15 - j) = 3)
        with h0 | h1 | h2 | h3
      · rw [h0]; simp [pow_zero, hone]
      · rw [h1]
        simp only [show Nat.beq 1 0 = false from rfl, show Nat.beq 1 1 = true from rfl, List.foldr_cons,
          hs, hf _ hk, pow_one]
      · rw [h2]
        simp only [show Nat.beq 2 0 = false from rfl, show Nat.beq 2 1 = false from rfl,
          List.foldr_cons, hs, hf _ hk, pow_two, hmul]
      · exact absurd h3 (by have := hu (15 - j); omega)
  exact key 16 le_rfl p

omit hmul hone in
theorem nwL_lt (u : Nat) : ∀ l ∈ nwL u, l < 32 := by
  have key : ∀ j ≤ 16, ∀ l ∈ (Nat.rec (motive := fun _ => List Nat) List.nil
      (fun j ih => (fun k => (fun e =>
        Bool.rec (motive := fun _ => List Nat)
          (Bool.rec (motive := fun _ => List Nat) (List.cons (Nat.shiftLeft k (nat_lit 1))
            (List.cons (Nat.shiftLeft k (nat_lit 1)) ih))
            (List.cons (Nat.shiftLeft k (nat_lit 1)) ih) (Nat.beq e (nat_lit 1)))
          ih (Nat.beq e (nat_lit 0))) (ex u k)) (Nat.sub (nat_lit 15) j)) j), l < 32 := by
    intro j hj
    induction j with
    | zero => intro l hl; simp at hl
    | succ j ih =>
      intro l hl
      have hs : Nat.shiftLeft (15 - j) 1 < 32 := by
        rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]; omega
      change l ∈ (Bool.rec (motive := fun _ => List Nat) _ _ _) at hl
      rw [show Nat.sub 15 j = 15 - j from rfl, ex_eq] at hl
      have hd := dg_lt_four u (15 - j)
      rcases (by omega : dg u (15 - j) = 0 ∨ dg u (15 - j) = 1 ∨ dg u (15 - j) = 2 ∨ dg u (15 - j) = 3)
        with h0 | h1 | h2 | h3
      · rw [h0] at hl
        exact ih (by omega) l hl
      · rw [h1] at hl
        rcases List.mem_cons.1 hl with rfl | hl
        · exact hs
        · exact ih (by omega) l hl
      · rw [h2] at hl
        rcases List.mem_cons.1 hl with rfl | hl
        · exact hs
        rcases List.mem_cons.1 hl with rfl | hl
        · exact hs
        · exact ih (by omega) l hl
      · rw [h3] at hl
        rcases List.mem_cons.1 hl with rfl | hl
        · exact hs
        rcases List.mem_cons.1 hl with rfl | hl
        · exact hs
        · exact ih (by omega) l hl
  exact key 16 le_rfl

@[expose] def TabF (x : ℕ → G) (OP TB : Nat) : Prop :=
  ∀ k < 16, ∀ a < 729, tb TB k 1 a < 729 ∧ opt OP (tb TB k 1 a) = act (x k) (opt OP a) ∧
    tb TB k 2 a = tb TB k 1 (tb TB k 1 a)

theorem evO_spec {x : ℕ → G} {OP TB : Nat} (hT : TabF act x OP TB) {u : Nat} (hu : ∀ k, dg u k < 3)
    {a : Nat} (ha : a < 729) : evO TB u a < 729 ∧ opt OP (evO TB u a) = act (nv x u) (opt OP a) := by
  have key : ∀ j ≤ 16, (Nat.rec (motive := fun _ => Nat) a
      (fun j ih => strictN ih (fun b => (fun k => (fun e => nIf(Nat.beq e (nat_lit 0), b, tb TB k e b))
        (ex u k)) (Nat.sub (nat_lit 15) j))) j) < 729 ∧
      opt OP (Nat.rec (motive := fun _ => Nat) a
      (fun j ih => strictN ih (fun b => (fun k => (fun e => nIf(Nat.beq e (nat_lit 0), b, tb TB k e b))
        (ex u k)) (Nat.sub (nat_lit 15) j))) j) = act (nvFrom x u (16 - j)) (opt OP a) := by
    intro j hj
    induction j with
    | zero => exact ⟨ha, by rw [nvFrom_of_ge le_rfl, hone]; rfl⟩
    | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hk : 15 - j < 16 := by omega
      have e16 : 16 - (j + 1) = 15 - j := by omega
      rw [e16, nvFrom_succ hk, show 15 - j + 1 = 16 - j by omega, hmul, ← ih2]
      change strictN _ _ < 729 ∧ opt OP (strictN _ _) = _
      rw [strictN_eq]
      dsimp only
      rw [show Nat.sub 15 j = 15 - j from rfl, ex_eq]
      generalize (Nat.rec (motive := fun _ => Nat) a
        (fun j ih => strictN ih (fun b => (fun k => (fun e => nIf(Nat.beq e (nat_lit 0), b, tb TB k e b))
          (ex u k)) (Nat.sub (nat_lit 15) j))) j) = b at ih1 ⊢
      obtain ⟨t1, t2, t3⟩ := hT _ hk b ih1
      rcases (by have := hu (15 - j); omega : dg u (15 - j) = 0 ∨ dg u (15 - j) = 1 ∨ dg u (15 - j) = 2)
        with h0 | h1 | h2
      · rw [h0, pow_zero, hone]; exact ⟨ih1, rfl⟩
      · rw [h1, pow_one]; exact ⟨t1, t2⟩
      · rw [h2]
        change tb TB (15 - j) 2 b < 729 ∧ opt OP (tb TB (15 - j) 2 b) = _
        obtain ⟨s1, s2, -⟩ := hT _ hk _ t1
        rw [t3, pow_two, hmul, ← t2]
        exact ⟨s1, s2⟩
  exact key 16 le_rfl

theorem evW_spec {x : ℕ → G} {OP TB : Nat} (hT : TabF act x OP TB) {ws : List Nat}
    (hw : ∀ w ∈ ws, ∀ k, dg w k < 3) {a : Nat} (ha : a < 729) :
    evW TB ws a < 729 ∧ opt OP (evW TB ws a) = act (ws.map (nv x)).prod (opt OP a) := by
  induction ws with
  | nil => exact ⟨ha, by rw [List.map_nil, List.prod_nil, hone]; rfl⟩
  | cons w ws ih =>
    obtain ⟨i1, i2⟩ := ih fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')
    have e : evW TB (w :: ws) a = evO TB w (evW TB ws a) := strictN_eq _ _
    obtain ⟨o1, o2⟩ := evO_spec act hmul hone hT (hw w List.mem_cons_self) i1
    rw [e, List.map_cons, List.prod_cons, hmul, ← i2]
    exact ⟨o1, o2⟩

end Act

theorem land3 (g : Nat) : Nat.land g 3 = g % 4 := by
  change g &&& (2 ^ 2 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem fldA (g : Nat) : fld(g, nat_lit 2, nat_lit 4294967295) = g / 4 % 2 ^ 32 := by
  change (g >>> 2) &&& (2 ^ 32 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem shr34 (g : Nat) : Nat.shiftRight g 34 = g / 2 ^ 34 := Nat.shiftRight_eq_div_pow g 34

theorem kidsL_cons (i y g : Nat) (L G : List Nat) :
    kidsL i (y :: L) (g :: G) = kids i y g (kidsL i L G) := rfl

theorem beq_false' {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem kids_eq (i y g : Nat) (rest : List Nat) : kids i y g rest =
    if g % 4 = 0 then rest else if g % 4 = 1 then y :: rest else
      y :: (y + 4 ^ i) :: (y + 2 * 4 ^ i) :: rest := by
  unfold kids
  rw [land3]
  dsimp only
  by_cases h0 : g % 4 = 0
  · rw [if_pos h0, h0]
    rfl
  · by_cases h1 : g % 4 = 1
    · rw [if_neg h0, if_pos h1, h1]
      rfl
    · rw [if_neg h0, if_neg h1, beq_false' h0, beq_false' h1]
      change y :: (Nat.add y (gw i)) :: (Nat.add y (Nat.shiftLeft (gw i) 1)) :: rest = _
      rw [gw_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, pow_one, mul_comm]
      rfl

theorem mem_kids_rest {i y g a : Nat} {rest : List Nat} (h : a ∈ rest) : a ∈ kids i y g rest := by
  rw [kids_eq]
  split_ifs <;> simp [h]

theorem mem_kids_one {i y g : Nat} {rest : List Nat} (h : g % 4 = 1) : y ∈ kids i y g rest := by
  rw [kids_eq, if_neg (by omega), if_pos h]
  exact List.mem_cons_self

theorem mem_kids_two {i y g : Nat} {rest : List Nat} (h : g % 4 = 2) {e : Nat} (he : e < 3) :
    y + e * 4 ^ i ∈ kids i y g rest := by
  rw [kids_eq, if_neg (by omega), if_neg (by omega)]
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2) with rfl | rfl | rfl <;> simp

theorem mem_kidsL {i : Nat} : ∀ {L G : List Nat} {j : Nat}, j < L.length → j < G.length →
    (G[j]! % 4 = 1 → L[j]! ∈ kidsL i L G) ∧
      (G[j]! % 4 = 2 → ∀ e < 3, L[j]! + e * 4 ^ i ∈ kidsL i L G)
  | [], _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, _, h => absurd h (by simp)
  | y :: L, g :: G, 0, _, _ => by
    simp only [List.getElem!_cons_zero, kidsL_cons]
    exact ⟨fun h => mem_kids_one h, fun h e he => mem_kids_two h he⟩
  | y :: L, g :: G, j + 1, h1, h2 => by
    simp only [List.getElem!_cons_succ, kidsL_cons]
    have ih := mem_kidsL (i := i) (L := L) (G := G) (j := j) (by simpa using h1) (by simpa using h2)
    exact ⟨fun h => mem_kids_rest (ih.1 h), fun h e he => mem_kids_rest (ih.2 h e he)⟩

theorem kidsL_inv {i : Nat} : ∀ {L G : List Nat} {z : Nat}, z ∈ kidsL i L G →
    ∃ y ∈ L, ∃ e < 3, z = y + e * 4 ^ i
  | [], _, _, h => by simp [kidsL] at h
  | _ :: _, [], _, h => by simp [kidsL] at h
  | y :: L, g :: G, z, h => by
    rw [kidsL_cons, kids_eq] at h
    have rest : z ∈ kidsL i L G → ∃ y' ∈ y :: L, ∃ e < 3, z = y' + e * 4 ^ i := fun h' => by
      obtain ⟨y', hy', e, he, rfl⟩ := kidsL_inv h'
      exact ⟨y', List.mem_cons_of_mem _ hy', e, he, rfl⟩
    split_ifs at h
    · exact rest h
    · rcases List.mem_cons.1 h with h1 | h
      · exact ⟨y, List.mem_cons_self, 0, by norm_num, by rw [h1]; ring⟩
      · exact rest h
    · rcases List.mem_cons.1 h with h1 | h
      · exact ⟨y, List.mem_cons_self, 0, by norm_num, by rw [h1]; ring⟩
      rcases List.mem_cons.1 h with h1 | h
      · exact ⟨y, List.mem_cons_self, 1, by norm_num, by rw [h1]; ring⟩
      rcases List.mem_cons.1 h with h1 | h
      · exact ⟨y, List.mem_cons_self, 2, by norm_num, by rw [h1]⟩
      · exact rest h

theorem dg_kid {y e i : Nat} (hy : y < 4 ^ i) (hyd : ∀ k, dg y k < 3) (he : e < 3) :
    ∀ k, dg (y + e * 4 ^ i) k < 3 := by
  intro k
  rcases lt_trichotomy k i with h | rfl | h
  · rw [dg_add_lt h]; exact hyd k
  · rw [dg_add_self hy (by omega)]; exact he
  · rw [dg_add_gt hy he h]; norm_num

section Cover

variable {G : Type*} [Group G] [Finite G]

@[expose] def TagFact (x : ℕ → G) (i y g : ℕ) : Prop :=
  (g % 4 = 0 → g / 4 % 2 ^ 32 < 4 ^ 16 ∧ (∀ k, dg (g / 4 % 2 ^ 32) k < 3) ∧
    (∃ k < i, dg (g / 4 % 2 ^ 32) k ≠ 0) ∧ nv x y ^ 3 = nv x (g / 4 % 2 ^ 32)) ∧
  (g % 4 = 1 → (∀ k ≤ i, dg (g / 2 ^ 34) k = 0) ∧
    nv x (g / 4 % 2 ^ 32) * nv x y = nv x y * x i * nv x (g / 4 % 2 ^ 32) * nv x (g / 2 ^ 34)) ∧
  g % 4 ≠ 3

structure ClassCert (x : ℕ → G) (L T : ℕ → List ℕ) : Prop where
  zero : L 0 = [0]
  lt : ∀ i < 16, ∀ y ∈ L i, y < 4 ^ i
  len : ∀ i < 16, (L i).length = (T i).length
  kids : ∀ i < 16, L (i + 1) = kidsL i (L i) (T i)
  tag : ∀ i < 16, ∀ j < (L i).length, TagFact x i ((L i)[j]!) ((T i)[j]!)

variable {x : ℕ → G} {pw : ℕ → ℕ} {cj : ℕ → ℕ → ℕ}

theorem cover (hP : PcPres x pw cj) (hl : 3 ^ 16 ≤ Nat.card (Nsub x 0)) {L T : ℕ → List ℕ}
    (hC : ClassCert x L T) {g : G} (hg : g ∈ Nsub x 0) (h3 : g ^ 3 = 1) :
    ∃ y ∈ L 16, ∃ c ∈ Nsub x 0, c * g * c⁻¹ = nv x y := by
  have claim : ∀ i ≤ 16, ∃ y ∈ L i, ∃ c ∈ Nsub x 0, (nv x y)⁻¹ * (c * g * c⁻¹) ∈ Nsub x i := by
    intro i hi
    induction i with
    | zero => exact ⟨0, by rw [hC.zero]; simp, 1, one_mem _, by rw [nv_zero]; simpa using hg⟩
    | succ i ih =>
      obtain ⟨y, hy, c, hc, hm⟩ := ih (by omega)
      have hi16 : i < 16 := by omega
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
      have hY : nv x (L i)[j] ∈ Nsub x 0 := nv_mem fun _ h => absurd h (Nat.not_lt_zero _)
      have hh : c * g * c⁻¹ ∈ Nsub x 0 := mul_mem (mul_mem hc hg) (inv_mem hc)
      have hh3 : (c * g * c⁻¹) ^ 3 = 1 := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
        rw [show c * g * c⁻¹ * (c * g * c⁻¹) * (c * g * c⁻¹) = c * (g * g * g) * c⁻¹ by group,
          ← pow_three' g, h3]
        group
      obtain ⟨e, he, hm'⟩ := decomp hP hi16 hm
      have htag := hC.tag i hi16 j hj
      rw [getElem!_pos (L i) j hj] at htag
      have hjT : j < (T i).length := by rw [← hC.len i hi16]; exact hj
      have hk := mem_kidsL (i := i) (L := L i) (G := T i) hj hjT
      rw [getElem!_pos (L i) j hj] at hk
      rw [← hC.kids i hi16] at hk
      generalize (T i)[j]! = t at htag hk
      generalize hYd : nv x (L i)[j] = Y at hY hm hm'
      generalize hhd : c * g * c⁻¹ = h at hh hh3 hm hm'
      have hYh : h = Y * x i ^ e * ((x i ^ e)⁻¹ * (Y⁻¹ * h)) := by group
      generalize (x i ^ e)⁻¹ * (Y⁻¹ * h) = m' at hm' hYh
      rcases (by omega : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3) with t0 | t1 | t2 | t3
      · exfalso
        obtain ⟨ha16, hadg, ⟨k, hk', hkne⟩, hcube⟩ := htag.1 t0
        have := cube_mem_of hP hY hh3 hm
        rw [← hYd, hcube] at this
        exact hkne (dg_zero hP hl ha16 hadg this k hk')
      · obtain ⟨hbdg, hf⟩ := htag.2.1 t1
        rw [hYd] at hf
        have hB : nv x (t / 2 ^ 34) ∈ Nsub x (i + 1) := nv_mem fun k hk => hbdg k (by omega)
        have hCm : nv x (t / 4 % 2 ^ 32) ∈ Nsub x 0 := nv_mem fun _ h => absurd h (Nat.not_lt_zero _)
        generalize nv x (t / 4 % 2 ^ 32) = C at hCm hf
        generalize nv x (t / 2 ^ 34) = Bn at hB hf
        refine ⟨(L i)[j], hk.1 t1, ?_⟩
        rw [hYd]
        rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2) with rfl | rfl | rfl
        · refine ⟨c, hc, ?_⟩
          rw [hhd, ← (by group : (x i ^ 0)⁻¹ * (Y⁻¹ * h) = Y⁻¹ * h)]
          rw [pow_zero, mul_one] at hYh
          rw [hYh]
          simpa using hm'
        · refine ⟨C⁻¹ * c, mul_mem (inv_mem hCm) hc, ?_⟩
          have hh1 : h = Y * x i * m' := by rw [hYh, pow_one]
          have := fuse_one hP hCm hB hf hm' hh1
          have e2 : C⁻¹ * c * g * (C⁻¹ * c)⁻¹ = C⁻¹ * (c * g * c⁻¹) * C⁻¹⁻¹ := by group
          rw [e2, hhd]
          exact this
        · obtain ⟨m'', hm'', he2⟩ := fuse_two hP hi16 hCm hB hf hm' hYh
          refine ⟨C⁻¹ * (C⁻¹ * c), mul_mem (inv_mem hCm) (mul_mem (inv_mem hCm) hc), ?_⟩
          have := fuse_one hP hCm hB hf hm'' he2
          have e2 : C⁻¹ * (C⁻¹ * c) * g * (C⁻¹ * (C⁻¹ * c))⁻¹ =
              C⁻¹ * (C⁻¹ * (c * g * c⁻¹) * C⁻¹⁻¹) * C⁻¹⁻¹ := by
            simp only [mul_inv_rev, inv_inv, mul_assoc]
          rw [e2, hhd]
          exact this
      · refine ⟨(L i)[j] + e * 4 ^ i, hk.2 t2 e he, c, hc, ?_⟩
        rw [nv_add hi16 (hC.lt i hi16 _ (List.getElem_mem hj)) he, hYd, hhd, hYh]
        have e3 : (Y * x i ^ e)⁻¹ * (Y * x i ^ e * m') = m' := by group
        rw [e3]
        exact hm'
      · exact absurd t3 htag.2.2
  obtain ⟨y, hy, c, hc, hm⟩ := claim 16 le_rfl
  refine ⟨y, hy, c, hc, ?_⟩
  rw [Nsub_top, Subgroup.mem_bot, inv_mul_eq_one] at hm
  exact hm.symm

end Cover

theorem eqO_spec {TB : Nat} {B l₁ l₂ : List Nat} (h : eqO TB B l₁ l₂ = true) :
    ∀ b ∈ B, evW TB l₁ b = evW TB l₂ b := by
  induction B with
  | nil => simp
  | cons b B ih =>
    have h' : (Nat.beq (evW TB l₁ b) (evW TB l₂ b) && eqO TB B l₁ l₂) = true := by
      rw [← bAnd_eq]; exact h
    rw [Bool.and_eq_true, beq_iff] at h'
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h'.1
    · exact ih h'.2 c hc

theorem eqL_spec : ∀ {l m : List Nat}, eqL l m = true → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [eqL])
  | _ :: _, [], h => absurd h (by simp [eqL])
  | a :: l, b :: m, h => by
    have h' : (Nat.beq a b && eqL l m) = true := by rw [← bAnd_eq]; exact h
    rw [Bool.and_eq_true, beq_iff] at h'
    rw [h'.1, eqL_spec h'.2]

theorem lenL_eq (l : List Nat) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => change Nat.succ (lenL l) = _; rw [ih]; rfl

theorem relOK_spec {f : Nat → Nat → Nat} {PW CJ j : Nat} (h : relOK f PW CJ j = true) :
    (nwOK (f32 PW j) = true ∧ Nat.land (f32 PW j) (lowM (j + 1)) = 0 ∧
      eqP f cb [2 * j, 2 * j, 2 * j] (nwL (f32 PW j)) = true) ∧
    ∀ k, j < k → k < 16 → nwOK (f32 CJ (16 * j + k)) = true ∧
      Nat.land (f32 CJ (16 * j + k)) (lowM (k + 1)) = gw k ∧
      eqP f cb [2 * j + 1, 2 * k, 2 * j] (nwL (f32 CJ (16 * j + k))) = true := by
  unfold relOK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hA, hrec⟩ := h
  rw [andB_eq, Bool.and_eq_true] at hA
  obtain ⟨hXY, hZ⟩ := hA
  rw [andB_eq, Bool.and_eq_true] at hXY
  obtain ⟨hX, hY⟩ := hXY
  rw [beq_iff] at hY
  have hj1 : Nat.shiftLeft j 1 = 2 * j := by
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, pow_one, mul_comm]
  refine ⟨⟨hX, ?_, ?_⟩, ?_⟩
  · simpa using hY
  · simpa only [hj1] using hZ
  · intro k hjk hk16
    have hj4 : Nat.shiftLeft j 4 = 16 * j := by
      rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, show (2 : ℕ) ^ 4 = 16 from by norm_num, mul_comm]
    have harg : Nat.add (Nat.shiftLeft j 4) k = 16 * j + k := by
      rw [hj4]
      rfl
    have hlow : Nat.add k 1 = k + 1 := rfl
    have hlow1 : Nat.add (2 * j) 1 = 2 * j + 1 := rfl
    have hk1 : Nat.shiftLeft k 1 = 2 * k := by
      rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, pow_one, mul_comm]
    have hf := CFSG.KC.Fi24FixS.recAnd (fun k => bIf(Nat.blt j k,
      CFSG.KC.LceS.letB (f32 CJ (Nat.add (Nat.shiftLeft j 4) k)) (fun c =>
        andB (andB (nwOK c) (Nat.beq (Nat.land c (lowM (Nat.add k 1))) (gw k)))
          (eqP f cb [Nat.add (Nat.shiftLeft j 1) 1, Nat.shiftLeft k 1, Nat.shiftLeft j 1]
            (nwL c))), true)) 16 hrec k hk16
    have hblt : Nat.blt j k = true := blt_iff.2 hjk
    rw [hblt] at hf
    simp only [CFSG.KS.Fi24Net.letB_eq'] at hf
    rw [andB_eq, Bool.and_eq_true] at hf
    obtain ⟨hfk, hfz⟩ := hf
    rw [andB_eq, Bool.and_eq_true] at hfk
    obtain ⟨hfn, hfe⟩ := hfk
    rw [beq_iff] at hfe
    exact ⟨by rw [harg] at hfn; exact hfn,
      by rw [harg] at hfe; rw [hlow] at hfe; exact hfe,
      by rw [harg] at hfz; rw [hj1, hlow1, hk1] at hfz; exact hfz⟩

private theorem oOK_lt_of_lt_of_le {f : ℕ → ℕ} {n : ℕ} (hf : ∀ a < n, f a < f (a + 1)) :
    ∀ b, ∀ a < b, b ≤ n → f a < f b := by
  intro b
  induction b with
  | zero => intro a ha; exact absurd ha (Nat.not_lt_zero a)
  | succ b ih =>
    intro a ha hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h | rfl
    · exact lt_trans (ih a h (by omega)) (hf b (by omega))
    · exact hf a (by omega)

theorem oOK_spec {OP : Nat} (h : oOK OP = true) :
    (∀ a < 729, opt OP a < 306936) ∧ ∀ a < 729, ∀ b < 729, opt OP a = opt OP b → a = b := by
  unfold oOK at h
  rw [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h728, hall⟩ := h
  have h728' : opt OP 728 < 306936 := blt_iff.1 h728
  have hstep : ∀ a < 728, opt OP a < opt OP (a + 1) := fun a ha =>
    blt_iff.1 (CFSG.KC.Fi24FixS.allBelow_spec hall (by norm_num) a ha)
  refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 ha with hlt | rfl
    · exact lt_trans (oOK_lt_of_lt_of_le hstep 728 a hlt le_rfl) h728'
    · exact h728'
  · rcases lt_trichotomy a b with hlt | rfl | hgt
    · exact absurd hab (ne_of_lt (oOK_lt_of_lt_of_le hstep b a hlt (by omega)))
    · rfl
    · exact absurd hab.symm (ne_of_lt (oOK_lt_of_lt_of_le hstep a b hgt (by omega)))

theorem tabOK_spec {XW : Nat → Nat → Nat} {OP TB k a : Nat} (h : tabOK XW OP TB k a = true) :
    tb TB k 1 a < 729 ∧ letN XW (2 * k) (opt OP a) = opt OP (tb TB k 1 a) ∧
      tb TB k 2 a = tb TB k 1 (tb TB k 1 a) := by
  unfold tabOK at h
  simp only [CFSG.KS.Fi24Net.letB_eq'] at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hb1, hb2⟩ := h
  rw [bAnd_eq, Bool.and_eq_true] at hb2
  obtain ⟨hbe, hbs⟩ := hb2
  rw [blt_iff] at hb1
  rw [beq_iff] at hbe
  rw [beq_iff] at hbs
  have hk1 : Nat.shiftLeft k 1 = 2 * k := by
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, pow_one, mul_comm]
  exact ⟨hb1, by simpa only [hk1] using hbe, hbs⟩

inductive OReach (TB : Nat) (gs : List Nat) (b : Nat) : Nat → Prop
  | base : OReach TB gs b b
  | step {p : Nat} (g : Nat) : g ∈ gs → OReach TB gs b p → OReach TB gs b (evO TB g p)

private theorem bAnd_true_iff {a b : Bool} : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  rw [bAnd_eq, Bool.and_eq_true]

private theorem recAndL {f : Nat → Bool} : ∀ gs : List Nat,
    List.rec (motive := fun _ => Bool) true (fun g _ ih => bAnd(f g, ih)) gs = true →
      ∀ g ∈ gs, f g = true
  | [], _, g, hg => by simp at hg
  | g₀ :: gs, h, g, hg => by
    have hh : bAnd(f g₀, List.rec (motive := fun _ => Bool) true
        (fun g _ ih => bAnd(f g, ih)) gs) = true := h
    rw [bAnd_true_iff] at hh
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hh.1
    · exact recAndL gs hh.2 g hg

private theorem orbOK_gens {TB : Nat} {B gs R : List Nat} {l : Nat}
    (h : orbOK TB B gs R l = true) :
    ∀ g ∈ gs, nwOK g = true ∧ fixB TB g B l = true := by
  have h1 : List.rec (motive := fun _ => Bool) true
      (fun g _ ih => bAnd(andB (nwOK g) (fixB TB g B l), ih)) gs = true := by
    unfold orbOK at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    exact h.1
  intro g hg
  have h2 := recAndL (f := fun g => andB (nwOK g) (fixB TB g B l)) gs h1 g hg
  rw [andB_eq, Bool.and_eq_true] at h2
  exact h2

private theorem fixB_aux {TB g : Nat} : ∀ (k : Nat) (B : List Nat),
    fixB TB g B k = true → ∀ m < k, m < B.length → evO TB g (B[m]!) = B[m]!
  | 0, _, _, m, hm, _ => absurd hm (Nat.not_lt_zero m)
  | k + 1, [], _, m, _, hlen => absurd hlen (by simp)
  | k + 1, b :: B, h, m, hm, hlen => by
    have h' : bAnd(Nat.beq (evO TB g b) b, fixB TB g B k) = true := h
    rw [bAnd_true_iff, beq_iff] at h'
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rw [List.getElem!_cons_zero]
      exact h'.1
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [List.getElem!_cons_succ]
      exact fixB_aux k B h'.2 m' (by omega) (by simpa using hlen)

private theorem nth_mem {gs : List Nat} {h : Nat} (hh : h < gs.length) : nth gs h ∈ gs := by
  induction gs generalizing h with
  | nil => simp at hh
  | cons g gs ih =>
    cases h with
    | zero => exact List.mem_cons_self
    | succ h => exact List.mem_cons_of_mem _ (ih (by simpa using hh))

private theorem land_20 (S : Nat) : Nat.land S 1048575 = S % 2 ^ 20 := by
  change S &&& (2 ^ 20 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

private theorem shr_20 (S : Nat) : Nat.shiftRight S 20 = S / 2 ^ 20 :=
  Nat.shiftRight_eq_div_pow S 20

private theorem land_10 (r : Nat) : Nat.land r 1023 = r % 2 ^ 10 := by
  change r &&& (2 ^ 10 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

private theorem land_pa (r : Nat) :
    Nat.land (Nat.shiftRight r 10) 1023 = r / 2 ^ 10 % 2 ^ 10 := by
  change Nat.shiftRight r 10 &&& (2 ^ 10 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod,
    show Nat.shiftRight r 10 = r / 2 ^ 10 from Nat.shiftRight_eq_div_pow r 10]

private def OrbAcc (TB : Nat) (gs : List Nat) (b0 r S : Nat) : Prop :=
  (S % 2 ^ 20 = 0 ∧ r % 2 ^ 10 = b0) ∨
    (S % 2 ^ 20 ≠ 0 ∧ (S / 2 ^ 20).testBit (r / 2 ^ 10 % 2 ^ 10) = true ∧
      r / 2 ^ 20 < gs.length ∧
      evO TB (nth gs (r / 2 ^ 20)) (r / 2 ^ 10 % 2 ^ 10) = r % 2 ^ 10)

private noncomputable def orbC1 (TB : Nat) (gs : List Nat) (b0 r S : Nat) : Bool :=
  bIf(Nat.beq (S % 2 ^ 20) 0, Nat.beq (r % 2 ^ 10) b0,
    bAnd((S / 2 ^ 20).testBit (r / 2 ^ 10 % 2 ^ 10),
      bAnd(Nat.blt (r / 2 ^ 20) gs.length,
        Nat.beq (evO TB (nth gs (r / 2 ^ 20)) (r / 2 ^ 10 % 2 ^ 10)) (r % 2 ^ 10))))

private noncomputable def orbC2 (r S : Nat) : Bool :=
  bAnd(Nat.blt (r % 2 ^ 10) 729, notB ((S / 2 ^ 20).testBit (r % 2 ^ 10)))

private theorem orbC1_iff {TB : Nat} {gs : List Nat} {b0 r S : Nat} :
    orbC1 TB gs b0 r S = true ↔ OrbAcc TB gs b0 r S := by
  unfold orbC1 OrbAcc
  rw [bIf_eq]
  by_cases hs : S % 2 ^ 20 = 0
  · rw [if_pos (beq_iff.2 hs)]
    constructor
    · intro h
      exact Or.inl ⟨hs, beq_iff.1 h⟩
    · intro h
      rcases h with ⟨-, hb⟩ | ⟨hne, -⟩
      · exact beq_iff.2 hb
      · exact absurd hs hne
  · rw [if_neg (by rw [beq_false' hs]; simp)]
    constructor
    · intro h
      rw [bAnd_true_iff, bAnd_true_iff] at h
      exact Or.inr ⟨hs, h.1, blt_iff.1 h.2.1, beq_iff.1 h.2.2⟩
    · intro h
      rcases h with ⟨h0, -⟩ | ⟨-, hbit, hlt, hev⟩
      · exact absurd h0 hs
      · rw [bAnd_true_iff, bAnd_true_iff]
        exact ⟨hbit, blt_iff.2 hlt, beq_iff.2 hev⟩

private theorem orbC2_iff {r S : Nat} :
    orbC2 r S = true ↔ r % 2 ^ 10 < 729 ∧
      (S / 2 ^ 20).testBit (r % 2 ^ 10) = false := by
  unfold orbC2
  rw [bAnd_true_iff, notB_eq, blt_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]; rfl⟩

private theorem orbStep_eq_succ {TB : Nat} {gs : List Nat} {b0 r S : Nat}
    (hacc : OrbAcc TB gs b0 r S) (ha : r % 2 ^ 10 < 729)
    (hbit : (S / 2 ^ 20).testBit (r % 2 ^ 10) = false) :
    orbStep TB gs b0 r S =
      (S % 2 ^ 20 + 1) + ((S / 2 ^ 20) ||| (1 <<< (r % 2 ^ 10))) <<< 20 := by
  unfold orbStep
  dsimp only
  rw [land_20 S, shr_20 S, land_10 r, land_pa r, shr_20 r, lenL_eq]
  change nIf(orbC1 TB gs b0 r S,
    nIf(orbC2 r S,
      (S % 2 ^ 20 + 1) + ((S / 2 ^ 20) ||| (1 <<< (r % 2 ^ 10))) <<< 20,
      1048575), 1048575) =
    (S % 2 ^ 20 + 1) + ((S / 2 ^ 20) ||| (1 <<< (r % 2 ^ 10))) <<< 20
  simp only [show orbC1 TB gs b0 r S = true from orbC1_iff.2 hacc,
    show orbC2 r S = true from orbC2_iff.2 ⟨ha, hbit⟩]

private theorem orbStep_eq_fail {TB : Nat} {gs : List Nat} {b0 r S : Nat}
    (h : ¬ (OrbAcc TB gs b0 r S ∧ r % 2 ^ 10 < 729 ∧
      (S / 2 ^ 20).testBit (r % 2 ^ 10) = false)) :
    orbStep TB gs b0 r S = 1048575 := by
  unfold orbStep
  dsimp only
  rw [land_20 S, shr_20 S, land_10 r, land_pa r, shr_20 r, lenL_eq]
  change nIf(orbC1 TB gs b0 r S,
    nIf(orbC2 r S,
      (S % 2 ^ 20 + 1) + ((S / 2 ^ 20) ||| (1 <<< (r % 2 ^ 10))) <<< 20,
      1048575), 1048575) = 1048575
  by_cases h1 : OrbAcc TB gs b0 r S
  · have hc1 : orbC1 TB gs b0 r S = true := orbC1_iff.2 h1
    have hc2 : orbC2 r S = false := by
      cases h2 : orbC2 r S with
      | false => rfl
      | true =>
        exact absurd ⟨h1, (orbC2_iff.1 h2).1, (orbC2_iff.1 h2).2⟩ h
    simp only [hc1, hc2]
  · have hc1 : orbC1 TB gs b0 r S = false := by
      cases h2 : orbC1 TB gs b0 r S with
      | false => rfl
      | true => exact absurd (orbC1_iff.1 h2) h1
    simp only [hc1]

private theorem orbStep_fail_absorb {TB : Nat} {gs : List Nat} {b0 r : Nat} :
    orbStep TB gs b0 r 1048575 = 1048575 := by
  apply orbStep_eq_fail
  rintro ⟨⟨hs0, -⟩ | ⟨-, hbit, -, -⟩, -, -⟩
  · rw [show (1048575 : Nat) % 2 ^ 20 = 1048575 by norm_num] at hs0
    omega
  · rw [show (1048575 : Nat) / 2 ^ 20 = 0 by norm_num, Nat.zero_testBit] at hbit
    exact Bool.noConfusion hbit

private theorem orbRun_cons (TB : Nat) (gs : List Nat) (b0 r : Nat) (R : List Nat) (S : Nat) :
    orbRun TB gs b0 (r :: R) S = orbRun TB gs b0 R (orbStep TB gs b0 r S) :=
  strictN_eq _ _

private theorem orbRun_fail {TB : Nat} {gs : List Nat} {b0 : Nat} : ∀ R : List Nat,
    orbRun TB gs b0 R 1048575 = 1048575
  | [] => rfl
  | _ :: R => by
    rw [orbRun_cons, orbStep_fail_absorb, orbRun_fail R]

private def OrbInv (TB : Nat) (gs : List Nat) (b0 : Nat) (S s M : Nat) (Sf : Finset Nat) : Prop :=
  S = s + 2 ^ 20 * M ∧ s < 2 ^ 20 ∧ s = Sf.card ∧
    (∀ x, M.testBit x = true ↔ x ∈ Sf) ∧
    ∀ a ∈ Sf, a < 729 ∧ OReach TB gs b0 a

private theorem orbInv_zero (TB : Nat) (gs : List Nat) (b0 : Nat) : OrbInv TB gs b0 0 0 0 ∅ := by
  refine ⟨by norm_num, by norm_num, by simp, ?_, ?_⟩
  · intro x
    rw [Nat.zero_testBit]
    simp
  · simp

private theorem orbInv_step {TB : Nat} {gs : List Nat} {b0 r S s M : Nat} {Sf : Finset Nat}
    (hInv : OrbInv TB gs b0 S s M Sf) (hacc : OrbAcc TB gs b0 r S)
    (ha : r % 2 ^ 10 < 729)
    (hbit : (S / 2 ^ 20).testBit (r % 2 ^ 10) = false) :
    ∃ M', OrbInv TB gs b0 (orbStep TB gs b0 r S) (s + 1) M' (insert (r % 2 ^ 10) Sf) := by
  obtain ⟨hS, hs20, hs, hM, hreach⟩ := hInv
  have hmod : S % 2 ^ 20 = s := by
    rw [hS, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs20]
  have hdiv : S / 2 ^ 20 = M := by
    rw [hS, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hs20, Nat.zero_add]
  have hle : Sf.card ≤ 729 := by
    have hsub : Sf ⊆ Finset.range 729 := fun x hx => Finset.mem_range.2 (hreach x hx).1
    simpa using Finset.card_le_card hsub
  have hbitM : M.testBit (r % 2 ^ 10) = false := by rwa [hdiv] at hbit
  have hnot : r % 2 ^ 10 ∉ Sf := by
    intro hmem
    have hb := (hM _).2 hmem
    rw [hbitM] at hb
    exact Bool.false_ne_true hb
  have hcard : s + 1 < 2 ^ 20 := by omega
  refine ⟨S / 2 ^ 20 ||| 2 ^ (r % 2 ^ 10), ?_, hcard, ?_, ?_, ?_⟩
  · rw [orbStep_eq_succ hacc ha hbit, hmod, hdiv, Nat.one_shiftLeft, Nat.shiftLeft_eq]
    ring
  · rw [Finset.card_insert_of_notMem hnot]
    omega
  · intro x
    rw [Nat.testBit_or, Nat.testBit_two_pow, Finset.mem_insert]
    by_cases hx : x = r % 2 ^ 10
    · simp [hx]
    · have hxa : r % 2 ^ 10 ≠ x := fun h => hx h.symm
      have hb : decide (r % 2 ^ 10 = x) = false := by
        rw [decide_eq_false_iff_not]
        exact hxa
      rw [hb]
      simp only [Bool.or_false, hx, false_or]
      rw [hdiv]
      exact hM x
  · intro a ha'
    rw [Finset.mem_insert] at ha'
    rcases ha' with rfl | ha'
    · refine ⟨ha, ?_⟩
      rcases hacc with ⟨-, hb0⟩ | ⟨-, hbit', hlt, hev⟩
      · rw [hb0]
        exact OReach.base
      · rw [hdiv] at hbit'
        have hpa : r / 2 ^ 10 % 2 ^ 10 ∈ Sf := (hM _).1 hbit'
        have hstep := OReach.step (nth gs (r / 2 ^ 20)) (nth_mem hlt)
          (hreach _ hpa).2
        rwa [← hev]
    · exact hreach a ha'

private theorem orbRun_inv {TB : Nat} {gs : List Nat} {b0 : Nat} (R : List Nat) :
    ∀ (S s M : Nat) (Sf : Finset Nat), OrbInv TB gs b0 S s M Sf →
      orbRun TB gs b0 R S = 1048575 ∨
        ∃ M' Sf', OrbInv TB gs b0 (orbRun TB gs b0 R S) (s + R.length) M' Sf' := by
  induction R with
  | nil =>
    intro S s M Sf hInv
    exact Or.inr ⟨M, Sf, hInv⟩
  | cons r R ih =>
    intro S s M Sf hInv
    rw [orbRun_cons]
    by_cases hacc : OrbAcc TB gs b0 r S ∧ r % 2 ^ 10 < 729 ∧
        (S / 2 ^ 20).testBit (r % 2 ^ 10) = false
    · obtain ⟨M', hInv'⟩ := orbInv_step hInv hacc.1 hacc.2.1 hacc.2.2
      rcases ih (orbStep TB gs b0 r S) (s + 1) M' (insert (r % 2 ^ 10) Sf) hInv' with h | h
      · exact Or.inl h
      · obtain ⟨M'', Sf'', hInv''⟩ := h
        have e : (s + 1) + R.length = s + (r :: R).length := by
          rw [List.length_cons]
          omega
        rw [e] at hInv''
        exact Or.inr ⟨M'', Sf'', hInv''⟩
    · exact Or.inl (by rw [orbStep_eq_fail hacc, orbRun_fail])

theorem orbOK_spec_ {TB : Nat} {B gs R : List Nat} {l : Nat} (hR : R.length ≤ 729)
    (h : orbOK TB B gs R l = true) :
    (∀ g ∈ gs, nwOK g = true ∧ ∀ m < l, m < B.length → evO TB g (B[m]!) = B[m]!) ∧
    ∃ S : Finset Nat, S.card = R.length ∧ ∀ a ∈ S, a < 729 ∧ OReach TB gs (nth B l) a := by
  have hgens := orbOK_gens h
  refine ⟨fun g hg => ⟨(hgens g hg).1, fun m hm hlt => ?_⟩, ?_⟩
  · exact fixB_aux l B (hgens g hg).2 m hm hlt
  · have h2 : Nat.land (orbRun TB gs (nth B l) R 0) 1048575 = lenL R := by
      unfold orbOK at h
      rw [bAnd_eq, Bool.and_eq_true] at h
      exact beq_iff.1 h.2
    rw [land_20, lenL_eq] at h2
    rcases orbRun_inv R 0 0 0 ∅ (orbInv_zero TB gs (nth B l)) with hfail | ⟨M, Sf, hInv⟩
    · rw [hfail] at h2
      norm_num at h2
      omega
    · obtain ⟨-, -, hs, -, hreach⟩ := hInv
      exact ⟨Sf, by omega, hreach⟩

private theorem kidsOK_all {i : Nat} {L : List Nat}
    (h : List.rec (motive := fun _ => Bool) true
      (fun y _ ih => bAnd(andB (nwOK y) (Nat.blt y (gw i)), ih)) L = true) :
    ∀ y ∈ L, nwOK y = true ∧ y < 4 ^ i := by
  intro y hy
  have hy' := recAndL (f := fun y => andB (nwOK y) (Nat.blt y (gw i))) L h y hy
  rw [andB_eq, Bool.and_eq_true, gw_eq, blt_iff] at hy'
  exact hy'

theorem kidsOK_spec {i : Nat} {L L' G : List Nat} (h : kidsOK i L L' G = true) :
    (∀ y ∈ L, nwOK y = true ∧ y < 4 ^ i) ∧ L.length = G.length ∧ L' = kidsL i L G := by
  unfold kidsOK at h
  obtain ⟨h1, h2⟩ := CFSG.KC.Fi24FixS.bAnd_true h
  obtain ⟨hbeq, heq⟩ := CFSG.KC.Fi24FixS.bAnd_true h2
  exact ⟨kidsOK_all h1, by simpa [lenL_eq] using beq_iff.1 hbeq, (eqL_spec heq).symm⟩

theorem repOK_spec {TB : Nat} {B : List Nat} {i y g : Nat} (h : repOK TB B i y g = true) :
    (g % 4 = 0 → nwOK (g / 4 % 2 ^ 32) = true ∧ Nat.land (g / 4 % 2 ^ 32) (lowM i) ≠ 0 ∧
      eqO TB B [y, y, y] [g / 4 % 2 ^ 32] = true) ∧
    (g % 4 = 1 → nwOK (g / 4 % 2 ^ 32) = true ∧ nwOK (g / 2 ^ 34) = true ∧
      Nat.land (g / 2 ^ 34) (lowM (i + 1)) = 0 ∧
      eqO TB B [g / 4 % 2 ^ 32, y] [y, gw i, g / 4 % 2 ^ 32, g / 2 ^ 34] = true) ∧
    g % 4 ≠ 3 := by
  unfold repOK at h
  dsimp only at h
  rw [land3, fldA, shr34] at h
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have hb0 : Nat.beq (g % 4) 0 = true := by rw [beq_iff]; exact h0
    rw [hb0] at h
    dsimp only at h
    rw [bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hq : Nat.beq (Nat.land (g / 4 % 2 ^ 32) (lowM i)) 0 = false := by
      rw [notB_eq, Bool.not_eq_true'] at h2
      exact h2
    exact ⟨h1, Nat.ne_of_beq_eq_false hq, h3⟩
  · intro h1
    have hb0 : Nat.beq (g % 4) 0 = false := beq_false' (by omega)
    have hb1 : Nat.beq (g % 4) 1 = true := by rw [beq_iff]; exact h1
    rw [hb0, hb1] at h
    dsimp only at h
    rw [bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true,
      beq_iff] at h
    obtain ⟨h1', h2', h3', h4'⟩ := h
    exact ⟨h1', h2', h3', h4'⟩
  · intro h3
    have hb0 : Nat.beq (g % 4) 0 = false := beq_false' (by omega)
    have hb1 : Nat.beq (g % 4) 1 = false := beq_false' (by omega)
    have hb2 : Nat.beq (g % 4) 2 = false := beq_false' (by omega)
    rw [hb0, hb1, hb2] at h
    exact Bool.false_ne_true h

private def pairAll (P : Nat → Nat → Bool) : List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun y _ ih G => List.rec (motive := fun _ => Bool) true
      (fun g G' _ => bAnd(P y g, ih G')) G)

private theorem pairAll_spec {P : Nat → Nat → Bool} :
    ∀ (L G : List Nat), pairAll P L G = true →
      ∀ j < L.length, j < G.length → P L[j]! G[j]! = true := by
  intro L
  induction L with
  | nil => intro G h j hj; simp at hj
  | cons y L ih =>
    intro G h j hjL hjG
    cases G with
    | nil => simp at hjG
    | cons g G =>
      change bAnd(P y g, pairAll P L G) = true at h
      rw [bAnd_eq, Bool.and_eq_true] at h
      cases j with
      | zero => simpa using h.1
      | succ k => exact ih G h.2 k (by simpa using hjL) (by simpa using hjG)

private theorem takeL_eq {α : Type} (n : Nat) (l : List α) : takeL n l = l.take n := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons a l ih =>
    cases n with
    | zero => rfl
    | succ n => change a :: takeL n l = _; rw [ih n, List.take_succ_cons]

private theorem dropL_eq {α : Type} (n : Nat) (l : List α) : dropL n l = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => change dropL n [] = _; rw [ih []]; simp
    | cons a l => change dropL n l = _; exact ih l

private theorem getElem!_slice {l : List Nat} {j : Nat} :
    (takeL 64 (dropL (64 * (j / 64)) l))[j % 64]! = l[j]! := by
  rw [takeL_eq, dropL_eq, List.getElem!_eq_getElem?_getD,
    List.getElem?_take_of_lt (l := l.drop (64 * (j / 64))) (i := j % 64) (j := 64)
      (Nat.mod_lt j (by norm_num)), List.getElem?_drop, Nat.div_add_mod,
    List.getElem!_eq_getElem?_getD]

private theorem pairAll_slices {P : Nat → Nat → Bool} {L G : List Nat} {N : Nat}
    (hN : L.length ≤ 64 * N)
    (h : ∀ s < N, pairAll P (takeL 64 (dropL (64 * s) L)) (takeL 64 (dropL (64 * s) G)) = true) :
    ∀ j < L.length, j < G.length → P L[j]! G[j]! = true := by
  intro j hjL hjG
  have hs : j / 64 < N := by
    have hm := Nat.mul_div_le j 64
    omega
  have hlenL : j % 64 < (takeL 64 (dropL (64 * (j / 64)) L)).length := by
    rw [takeL_eq, dropL_eq, List.length_take, List.length_drop]
    have hm := Nat.div_add_mod j 64
    have h64 := Nat.mod_lt j (by norm_num : 0 < 64)
    omega
  have hlenG : j % 64 < (takeL 64 (dropL (64 * (j / 64)) G)).length := by
    rw [takeL_eq, dropL_eq, List.length_take, List.length_drop]
    have hm := Nat.div_add_mod j 64
    have h64 := Nat.mod_lt j (by norm_num : 0 < 64)
    omega
  have hrec := pairAll_spec (P := P) (L := takeL 64 (dropL (64 * (j / 64)) L))
    (G := takeL 64 (dropL (64 * (j / 64)) G)) (h (j / 64) hs) (j % 64) hlenL hlenG
  rw [getElem!_slice (l := L), getElem!_slice (l := G)] at hrec
  exact hrec

theorem repsOK_slices {TB : Nat} {B L G : List Nat} {i : Nat} (hL : L.length ≤ 2048)
    (h : ∀ s < 32, repsOK TB B i (takeL 64 (dropL (64 * s) L)) (takeL 64 (dropL (64 * s) G)) = true) :
    ∀ j < L.length, j < G.length → repOK TB B i (L[j]!) (G[j]!) = true := by
  exact pairAll_slices (P := repOK TB B i) (N := 32) hL h

theorem finsOK_slices {TB RP : Nat} {B L F : List Nat} (hL : L.length ≤ 1088)
    (h : ∀ s < 17, finsOK TB B RP (takeL 64 (dropL (64 * s) L)) (takeL 64 (dropL (64 * s) F)) = true) :
    ∀ j < L.length, j < F.length → finOK TB B RP (L[j]!) (F[j]!) = true := by
  exact pairAll_slices (P := finOK TB B RP) (N := 17) hL h

theorem finOK_spec {TB RP : Nat} {B : List Nat} {y f : Nat} (h : finOK TB B RP y f = true) :
    (f % 4 = 0 → y = 0) ∧
    (f % 4 = 1 → nwOK (f / 4 % 2 ^ 32) = true ∧ f / 4 % 2 ^ 32 ≠ 0 ∧
      eqO TB B [y, y, y] [f / 4 % 2 ^ 32] = true) ∧
    (f % 4 ≠ 0 → f % 4 ≠ 1 → f % 4 = 2 ∧ f / 4 % 2 ^ 32 < 824 ∧ nwOK (f / 2 ^ 34) = true ∧
      eqO TB B [f / 2 ^ 34, y] [f32 RP (f / 4 % 2 ^ 32), f / 2 ^ 34] = true) := by
  unfold finOK at h
  dsimp only at h
  rw [land3, fldA, shr34] at h
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have hb0 : Nat.beq (f % 4) 0 = true := by rw [beq_iff]; exact h0
    rw [hb0] at h
    dsimp only at h
    rwa [beq_iff] at h
  · intro h1
    have hb0 : Nat.beq (f % 4) 0 = false := beq_false' (by omega)
    have hb1 : Nat.beq (f % 4) 1 = true := by rw [beq_iff]; exact h1
    rw [hb0, hb1] at h
    dsimp only at h
    rw [bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1', h2', h3'⟩ := h
    have hq : Nat.beq (f / 4 % 2 ^ 32) 0 = false := by
      rw [notB_eq, Bool.not_eq_true'] at h2'
      exact h2'
    exact ⟨h1', Nat.ne_of_beq_eq_false hq, h3'⟩
  · intro h0 h1
    have hb0 : Nat.beq (f % 4) 0 = false := beq_false' h0
    have hb1 : Nat.beq (f % 4) 1 = false := beq_false' h1
    rw [hb0, hb1] at h
    dsimp only at h
    rw [bAnd_eq, Bool.and_eq_true, beq_iff] at h
    obtain ⟨h2, h3⟩ := h
    rw [bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true, blt_iff] at h3
    obtain ⟨hlt, hw, heq⟩ := h3
    exact ⟨h2, hlt, hw, heq⟩

theorem xchunk_spec {X : Nat → Bool} {g : Nat}
    (h : Nat.rec (motive := fun _ => Bool) true
      (fun m ih => bAnd(bIf(Nat.blt (Nat.add (Nat.mul (nat_lit 8) g) m) (nat_lit 824),
        X (Nat.add (Nat.mul (nat_lit 8) g) m), true), ih)) (nat_lit 8) = true) :
    ∀ m < 8, 8 * g + m < 824 → X (8 * g + m) = true := by
  intro m hm hlt
  have h1 := CFSG.KC.Fi24FixS.recAnd (fun m =>
    bIf(Nat.blt (Nat.add (Nat.mul (nat_lit 8) g) m) (nat_lit 824),
      X (Nat.add (Nat.mul (nat_lit 8) g) m), true)) 8 h m hm
  rw [bIf_eq] at h1
  have hb : Nat.blt (Nat.add (Nat.mul (nat_lit 8) g) m) (nat_lit 824) = true := by
    rw [blt_iff]
    simpa using hlt
  rw [hb] at h1
  simpa using h1

private theorem transOK_list {NW XW : Nat → Nat → Nat} {RP l : Nat} {w t B : List Nat}
    (h : List.rec (motive := fun _ => Bool) true
      (fun b _ ih => bAnd(Nat.beq (apP (letN NW) w (apP (letN NW) t b))
        (apP (letN NW) t (apP (letN XW) (nwL (f32 RP l)) b)), ih)) B = true) :
    ∀ b ∈ B, w.foldr (letN NW) (t.foldr (letN NW) b) =
      t.foldr (letN NW) ((nwL (f32 RP l)).foldr (letN XW) b) := by
  intro b hb
  have hb' := recAndL (f := fun b => Nat.beq (apP (letN NW) w (apP (letN NW) t b))
    (apP (letN NW) t (apP (letN XW) (nwL (f32 RP l)) b))) B h b hb
  rw [beq_iff] at hb'
  simpa only [apP_eq] using hb'

theorem transOK_spec {NW XW : Nat → Nat → Nat} {RP l : Nat} {w t : List Nat}
    (h : transOK NW XW RP l w t = true) : nwOK (f32 RP l) = true ∧
    ∀ b ∈ cb, w.foldr (letN NW) (t.foldr (letN NW) b) =
      t.foldr (letN NW) ((nwL (f32 RP l)).foldr (letN XW) b) := by
  unfold transOK at h
  rw [andB_eq, Bool.and_eq_true] at h
  exact ⟨h.1, transOK_list h.2⟩

end CFSG.KS.Fi24Pc

end
