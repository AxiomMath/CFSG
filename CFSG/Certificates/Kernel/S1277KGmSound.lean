module

public import Certificates.Data.Kernel.S1277KGm
public import Certificates.Data.S1277MLine
public import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.S1277Gm

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm

theorem mul_mod_two_eq (x n : ℕ) : x * (n % 2) = if n % 2 = 1 then x else 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem sVF_eq (c v : ℕ) : sVF c v = sV c v := by
  rw [sVF, sV, mul_mod_two_eq, mul_mod_two_eq]

theorem appF_eq (A : Mc) (v : ℕ) : appF A v = A.app v := by
  simp only [appF, Mc.app, sVF_eq]

theorem mulF_eq (A B : Mc) : mulF A B = A.mul B := by
  simp only [mulF, Mc.mul, appF_eq]

theorem memS_insS (s i j : ℕ) :
    memS (insS s j) i = (memS s i || (i == j && decide (j < 262144))) := by
  have h64 : (18446744073709551616 : ℕ) = 2 ^ 64 := by norm_num
  have h1 : (j + 1) % 18446744073709551616 < 2 ^ (i + 64) := by
    rw [h64]
    exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  unfold memS insS
  rw [Nat.testBit_xor, Nat.testBit_lt_two_pow h1, Bool.xor_false, Nat.testBit_or,
    Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases hij : i = j
  · subst hij
    cases decide (i < 262144) <;> simp
  · have : ¬ j + 64 = i + 64 := by omega
    simp [hij, Ne.symm hij, this]

def SRel (a : Array Bool) (s : ℕ) : Prop := a.size = 262144 ∧ ∀ i, a.getD i false = memS s i

theorem SRel.set {a : Array Bool} {s : ℕ} (h : SRel a s) (j : ℕ) :
    SRel (a.set! j true) (insS s j) := by
  refine ⟨by simp [h.1], fun i => ?_⟩
  rw [memS_insS, ← h.2 i]
  simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, h.1]
  by_cases hij : j = i
  · subst hij
    by_cases hj : j < 262144
    · simp [hj]
    · have : a[j]? = none := Array.getElem?_eq_none (by rw [h.1]; omega)
      simp [hj, this]
  · have : (i == j) = false := by simpa using Ne.symm hij
    simp [hij, this]

theorem SRel.init : SRel (Array.replicate 262144 false) 0 := by
  refine ⟨by simp, fun i => ?_⟩
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, memS, Nat.zero_testBit,
    Bool.and_false]
  split <;> rfl

theorem bfsAdd_sim (gens : List Mc) (x : Mc) :
    ∀ (p : Array Bool × List Mc) (q : ℕ × List Mc), SRel p.1 q.1 → p.2 = q.2 →
      SRel (bfsAdd gens p x).1 (bfsAddK gens q x).1 ∧ (bfsAdd gens p x).2 = (bfsAddK gens q x).2 := by
  induction gens with
  | nil => intro p q h1 h2; exact ⟨h1, h2⟩
  | cons g gs ih =>
    intro p q h1 h2
    simp only [bfsAdd, bfsAddK, List.foldl_cons] at ih ⊢
    rw [mulF_eq, h1.2]
    cases hm : memS q.1 (mcIdx (x.mul g))
    · simp only [Bool.false_eq_true, ↓reduceIte, cond_false]
      exact ih _ _ (h1.set _) (by rw [h2])
    · simp only [↓reduceIte, cond_true]
      exact ih _ _ h1 h2

theorem fold_sim (gens : List Mc) :
    ∀ (fr : List Mc) (p : Array Bool × List Mc) (q : ℕ × List Mc), SRel p.1 q.1 → p.2 = q.2 →
      SRel (fr.foldl (bfsAdd gens) p).1 (fr.foldl (bfsAddK gens) q).1 ∧
        (fr.foldl (bfsAdd gens) p).2 = (fr.foldl (bfsAddK gens) q).2 := by
  intro fr
  induction fr with
  | nil => intro p q h1 h2; exact ⟨h1, h2⟩
  | cons x xs ih =>
    intro p q h1 h2
    rw [List.foldl_cons, List.foldl_cons]
    obtain ⟨e1, e2⟩ := bfsAdd_sim gens x p q h1 h2
    exact ih _ _ e1 e2

theorem bfs_eq_bfsK (gens : List Mc) :
    ∀ (n : ℕ) (st : Array Bool × List Mc × List Mc) (sk : ℕ × List Mc × List Mc),
      SRel st.1 sk.1 → st.2 = sk.2 → bfs gens n st = bfsK gens n sk := by
  intro n
  induction n with
  | zero =>
    rintro ⟨a, al, fr⟩ ⟨s, al', fr'⟩ _ h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    rfl
  | succ n ih =>
    rintro ⟨a, al, fr⟩ ⟨s, al', fr'⟩ h1 h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    simp only [bfs, bfsK]
    split
    · rfl
    · obtain ⟨e1, e2⟩ := fold_sim gens fr (a, []) (s, []) h1 rfl
      refine ih _ _ ?_ ?_
      · exact e1
      · simp only [bfsStep, bfsStepK]
        rw [e2]

theorem bfs_eq_bfsK' (gens : List Mc) (n : ℕ) {a : Array Bool} {s : ℕ} (h : SRel a s)
    (al fr : List Mc) : bfs gens n (a, al, fr) = bfsK gens n (s, al, fr) :=
  bfs_eq_bfsK gens n (a, al, fr) (s, al, fr) h rfl

theorem init_sim : SRel ((Array.replicate 262144 false).set! (mcIdx Mc.one) true)
    (insS 0 (mcIdx Mc.one)) := SRel.init.set _

theorem gmList_eq_gmK : gmList = gmK := by
  rw [gmList.eq_1, gmK.eq_1]
  exact bfs_eq_bfsK' gmGens 64 init_sim [Mc.one] [Mc.one]

theorem closureM_eq (gens : List Mc) :
    closureM gens = bfsK gens 64 (insS 0 (mcIdx Mc.one), [Mc.one], [Mc.one]) := by
  rw [closureM.eq_1]
  exact bfs_eq_bfsK' gens 64 init_sim [Mc.one] [Mc.one]

theorem eq_of_eqMc : ∀ (L : List Mc) (N : List ℕ), eqMc L N = true → L = N.map Mc.ofIdx := by
  intro L
  induction L with
  | nil =>
    intro N h
    cases N with
    | nil => rfl
    | cons _ _ => simp [eqMc] at h
  | cons A L ih =>
    intro N h
    cases N with
    | nil => simp [eqMc] at h
    | cons n N =>
      obtain ⟨a0, a1, a2⟩ := A
      simp only [eqMc, Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
      rw [List.map_cons, ← ih N h3, Mc.ofIdx, h0, h1, h2]

theorem eq_of_eqB6 : ∀ (L : List B6) (N : List ℕ), eqB6 L N = true → L = N.map B6.ofP := by
  intro L
  induction L with
  | nil =>
    intro N h
    cases N with
    | nil => rfl
    | cons _ _ => simp [eqB6] at h
  | cons B L ih =>
    intro N h
    cases N with
    | nil => simp [eqB6] at h
    | cons p N =>
      obtain ⟨b0, b1, b2, b3, b4, b5⟩ := B
      simp only [eqB6, Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
      rw [List.map_cons, ← ih N h6, B6.ofP, h0, h1, h2, h3, h4, h5]

theorem bit_mul (v i x : ℕ) : x * ((v >>> i) % 2) = bitV v i x := by
  rw [bitV, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, mul_mod_two_eq]
  simp

theorem bit_mul0 (v x : ℕ) : x * (v % 2) = bitV v 0 x := by
  rw [← bit_mul, Nat.shiftRight_zero]

theorem appP_eq (p v : ℕ) : appP p v = (B6.ofP p).app v := by
  simp only [appP, B6.app, B6.ofP, bit_mul]
  rw [bit_mul0]

theorem term_lt (x b : ℕ) : x % 64 * (b % 2) < 2 ^ 6 := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp [h] <;> omega

theorem appP_lt (p v : ℕ) : appP p v < 64 := by
  have h := Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow (term_lt p v) (term_lt (p >>> 6) (v >>> 1))) (term_lt (p >>> 12) (v >>> 2)))
    (term_lt (p >>> 18) (v >>> 3))) (term_lt (p >>> 24) (v >>> 4))) (term_lt (p >>> 30) (v >>> 5))
  exact h

theorem testBit_foldl (x : ℕ) : ∀ (l : List ℕ) (m : ℕ),
    (l.foldl (fun m y => m ||| 1 <<< y) m).testBit x = true ↔ m.testBit x = true ∨ x ∈ l := by
  intro l
  induction l with
  | nil => intro m; simp
  | cons y ys ih =>
    intro m
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr h

theorem testBit_maskL (l : List ℕ) (x : ℕ) : (maskL l).testBit x = true ↔ x ∈ l := by
  rw [maskL, testBit_foldl]
  simp

theorem card_eq_pc64 (l : List ℕ) (hl : ∀ x ∈ l, x < 64) : l.toFinset.card = pc64 (maskL l) := by
  have nd : ((List.range 64).filter fun i => (maskL l).testBit i).Nodup :=
    List.nodup_range.filter _
  have e : ((List.range 64).filter fun i => (maskL l).testBit i).toFinset = l.toFinset := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, testBit_maskL]
    exact ⟨fun h => h.2, fun h => ⟨hl x h, h⟩⟩
  rw [pc64, ← e, List.toFinset_card_of_nodup nd]

theorem dedupAux_spec : ∀ (l acc : List ℕ), acc.Nodup →
    (Certificates.Data.S1277MLine.dedupAux acc l).Nodup ∧
      ∀ x, x ∈ Certificates.Data.S1277MLine.dedupAux acc l ↔ x ∈ acc ∨ x ∈ l := by
  intro l
  induction l with
  | nil => intro acc h; simpa [Certificates.Data.S1277MLine.dedupAux] using h
  | cons y ys ih =>
    intro acc h
    rw [Certificates.Data.S1277MLine.dedupAux]
    by_cases hy : y ∈ acc
    · rw [if_pos (List.elem_iff.2 hy)]
      refine ⟨(ih acc h).1, fun x => ?_⟩
      rw [(ih acc h).2, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl hy
        · exact Or.inr h
    · rw [if_neg (fun e => hy (List.elem_iff.1 e))]
      have h' : (y :: acc).Nodup := List.nodup_cons.2 ⟨hy, h⟩
      refine ⟨(ih _ h').1, fun x => ?_⟩
      rw [(ih _ h').2, List.mem_cons, List.mem_cons]
      tauto

theorem orbitSize_eq_card (G : List B6) (c : ℕ) :
    Certificates.Data.S1277MLine.orbitSize G c = (G.map fun B => B.app c).toFinset.card := by
  obtain ⟨nd, hm⟩ := dedupAux_spec (G.map fun B => B.app c) [] List.nodup_nil
  rw [Certificates.Data.S1277MLine.orbitSize, Certificates.Data.S1277MLine.dedupN,
    ← List.toFinset_card_of_nodup nd]
  congr 1
  ext x
  simp [hm]

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem map_app (P : List ℕ) (c : ℕ) :
    (P.map B6.ofP).map (fun B => B.app c) = P.map fun p => appP p c := by
  rw [List.map_map]
  congr 1
  funext p
  exact (appP_eq p c).symm

theorem orb_of_orbChk (P : List ℕ) (h : orbChk P = true) :
    ((P.map B6.ofP).map fun B => B.app 5).toFinset.card = 45 ∧
      ∀ c < 64, ((P.map B6.ofP).map fun B => B.app c).toFinset.card = 45 →
        ∃ B ∈ P.map B6.ofP, B.app 5 = c := by
  have hb : ∀ c, ∀ x ∈ P.map (fun p => appP p c), x < 64 := by
    intro c x hx
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
    exact appP_lt p c
  rw [orbChk, strictB_eq] at h
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨h5, hc⟩ := h
  refine ⟨by rw [map_app, card_eq_pc64 _ (hb 5), h5], fun c hc64 hcard => ?_⟩
  rw [map_app, card_eq_pc64 _ (hb c)] at hcard
  rcases hc c hc64 with h | h
  · obtain ⟨p, hp, e⟩ := List.mem_map.1 ((testBit_maskL _ c).1 h)
    exact ⟨B6.ofP p, List.mem_map_of_mem hp, by rw [← appP_eq, e]⟩
  · rw [hcard] at h
    exact absurd h (by decide)

end CFSG.KS.S1277Gm

end
