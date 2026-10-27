module

public import Certificates.Data.Kernel.YModel.Text
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Mathlib.Data.List.Basic
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas
import all Init.Data.String.Slice
import all Init.Data.String.Search
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
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.YModel.TextSem

open CFSG.KC CFSG.KC.YModel

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem blt_false {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false :=
  Bool.eq_false_iff.mpr fun h' => h (Nat.blt_eq.mp h')

theorem brec_and {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

@[expose] def dval (ds : List Nat) : Nat := ds.foldl (fun v d => v * 10 + (d - 48)) 0

@[expose] def IsDig (d : Nat) : Prop := 48 ≤ d ∧ d < 58

@[expose] def TokOK (x : Nat) (p : List Nat) : Prop := p ≠ [] ∧ (∀ d ∈ p, IsDig d) ∧ dval p = x

@[expose] noncomputable def gv (w cur j : Nat) (rest : List Nat) : Nat := cur ||| (joinW w rest <<< (w * (32 - j)))

theorem dval_snoc (ds : List Nat) (d : Nat) : dval (ds ++ [d]) = dval ds * 10 + (d - 48) := by
  unfold dval
  rw [List.foldl_append]
  rfl

theorem decV_eq (c : Nat) : decV c = if c < 48 then 10 else if c < 58 then c - 48 else 10 := by
  unfold decV
  by_cases h1 : c < 48
  · rw [Nat.blt_eq.mpr h1, if_pos h1]
  · rw [blt_false h1, if_neg h1]
    by_cases h2 : c < 58
    · rw [Nat.blt_eq.mpr h2, if_pos h2]
      rfl
    · rw [blt_false h2, if_neg h2]

theorem decV_dig {c : Nat} (h : Nat.blt (decV c) 10 = true) : IsDig c ∧ decV c = c - 48 := by
  have h' := Nat.blt_eq.mp h
  rw [decV_eq] at h' ⊢
  by_cases h1 : c < 48
  · rw [if_pos h1] at h'
    omega
  · rw [if_neg h1] at h' ⊢
    by_cases h2 : c < 58
    · rw [if_pos h2]
      exact ⟨⟨by omega, h2⟩, rfl⟩
    · rw [if_neg h2] at h'
      omega

theorem joinW_head (w : Nat) (rest : List Nat) :
    lhead rest ||| (joinW w (ltail rest) <<< (w * 32)) = joinW w rest := by
  cases rest with
  | nil =>
    change 0 ||| (0 <<< (w * 32)) = 0
    simp
  | cons c cs =>
    change c ||| (joinW w cs <<< (w * 32)) = Nat.lor c (Nat.shiftLeft (joinW w cs) (Nat.mul 32 w))
    rw [Nat.mul_comm]
    rfl

theorem or_shl_shr (a b s w : Nat) : (a ||| (b <<< (s + w))) >>> w = (a >>> w) ||| (b <<< s) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  congr 1
  by_cases h : i ≥ s
  · rw [decide_eq_true h, decide_eq_true (by omega), show w + i - (s + w) = i - s by omega]
  · rw [decide_eq_false h, decide_eq_false (by omega)]
    simp

theorem or_shl_shr' (a b w : Nat) : (a ||| (b <<< w)) >>> w = (a >>> w) ||| b := by
  have := or_shl_shr a b 0 w
  rwa [Nat.zero_add, Nat.shiftLeft_zero] at this

theorem gv_mod (w cur j : Nat) (rest : List Nat) (hj : j < 32) : gv w cur j rest % 2 ^ w = cur % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold gv
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < w
  · have : ¬ i ≥ w * (32 - j) := by
      have : w ≤ w * (32 - j) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    simp [hi, this]
  · simp [hi]

theorem tokEnd_spec {w lines : Nat} {C : Nat → List Nat} {E : Nat → Nat} {nl : Bool}
    {L e t x cur j : Nat} {rest : List Nat} {k : Nat → Nat → Nat → Nat → List Nat → Bool}
    (h : tokEnd w lines C E nl L e t x cur j rest k = true) :
    0 < t ∧ x = cur % 2 ^ w ∧
      (nl = false → (j + 1 = 32 → cur >>> w = 0 ∧ k L (e + 1) (lhead rest) 0 (ltail rest) = true) ∧
        (j + 1 ≠ 32 → k L (e + 1) (cur >>> w) (j + 1) rest = true)) ∧
      (nl = true → L < lines ∧ e + 1 = E L ∧
        k (L + 1) 0 (lhead (C (L + 1))) 0 (ltail (C (L + 1))) = true) := by
  unfold tokEnd at h
  simp only [strictB_eq] at h
  obtain ⟨h1, h⟩ := brec_and h
  obtain ⟨_, h⟩ := brec_and h
  obtain ⟨h3, h⟩ := brec_and h
  have hx : x = cur % 2 ^ w := by
    have := Nat.eq_of_beq_eq_true h3
    rw [this]
    change cur &&& ((1 <<< w) - 1) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
  refine ⟨Nat.blt_eq.mp h1, hx, fun hnl => ?_, fun hnl => ?_⟩
  · subst hnl
    dsimp only at h
    constructor
    · intro hj
      have : Nat.beq (Nat.succ j) 32 = true := by rw [Nat.beq_eq]; exact hj
      rw [this] at h
      dsimp only at h
      obtain ⟨h4, h5⟩ := brec_and h
      exact ⟨Nat.eq_of_beq_eq_true h4, h5⟩
    · intro hj
      have : Nat.beq (Nat.succ j) 32 = false := by
        cases hb : Nat.beq (Nat.succ j) 32
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) hj
      rw [this] at h
      dsimp only at h
      exact h
  · subst hnl
    dsimp only at h
    obtain ⟨h4, h⟩ := brec_and h
    obtain ⟨h5, h⟩ := brec_and h
    obtain ⟨_, h⟩ := brec_and h
    obtain ⟨_, h⟩ := brec_and h
    exact ⟨Nat.blt_eq.mp h4, Nat.eq_of_beq_eq_true h5, h⟩

theorem decRun_cons (w lines sgn : Nat) (C : Nat → List Nat) (E : Nat → Nat) (c : Nat)
    (bs : List Nat) (L e t v ng cur j : Nat) (rest : List Nat) :
    decRun w lines sgn C E (c :: bs) L e t v ng cur j rest = strictB (decV c) (fun d =>
      bIf(Nat.blt d (nat_lit 10),
        strictB (Nat.add (Nat.mul v (nat_lit 10)) d) (fun v' =>
          strictB (Nat.succ t) (fun t' => decRun w lines sgn C E bs L e t' v' ng cur j rest)),
      bIf(Nat.beq c (nat_lit 45),
        bAnd(Nat.ble sgn L, bAnd(Nat.beq t (nat_lit 0), bAnd(Nat.beq ng (nat_lit 0),
          decRun w lines sgn C E bs L e t v (nat_lit 1) cur j rest))),
      bIf(Nat.beq c (nat_lit 32),
        tokEnd w lines C E false L e t (tokCode sgn L v ng) cur j rest
          (fun L' e' cur' j' rest' => decRun w lines sgn C E bs L' e' (nat_lit 0) (nat_lit 0)
            (nat_lit 0) cur' j' rest'),
      bIf(Nat.beq c (nat_lit 10),
        tokEnd w lines C E true L e t (tokCode sgn L v ng) cur j rest
          (fun L' e' cur' j' rest' => decRun w lines sgn C E bs L' e' (nat_lit 0) (nat_lit 0)
            (nat_lit 0) cur' j' rest'),
        false))))) := rfl

theorem decRun_step {w lines sgn : Nat} {C : Nat → List Nat} {E : Nat → Nat} {c : Nat}
    {bs : List Nat} {L e t v ng cur j : Nat} {rest : List Nat}
    (h : decRun w lines sgn C E (c :: bs) L e t v ng cur j rest = true) :
    (IsDig c ∧ decRun w lines sgn C E bs L e (t + 1) (v * 10 + (c - 48)) ng cur j rest = true) ∨
    (c = 45 ∧ sgn ≤ L ∧ t = 0 ∧ ng = 0 ∧ decRun w lines sgn C E bs L e t v 1 cur j rest = true) ∨
    (c = 32 ∧ tokEnd w lines C E false L e t (tokCode sgn L v ng) cur j rest
      (fun L' e' cur' j' rest' => decRun w lines sgn C E bs L' e' 0 0 0 cur' j' rest') = true) ∨
    (c = 10 ∧ tokEnd w lines C E true L e t (tokCode sgn L v ng) cur j rest
      (fun L' e' cur' j' rest' => decRun w lines sgn C E bs L' e' 0 0 0 cur' j' rest') = true) := by
  rw [decRun_cons, strictB_eq] at h
  cases hd : Nat.blt (decV c) 10
  · rw [hd] at h
    dsimp only at h
    cases h45 : Nat.beq c 45
    · rw [h45] at h
      dsimp only at h
      cases h32 : Nat.beq c 32
      · rw [h32] at h
        dsimp only at h
        cases h10 : Nat.beq c 10
        · rw [h10] at h
          dsimp only at h
          exact absurd h (by decide)
        · rw [h10] at h
          dsimp only at h
          exact Or.inr (Or.inr (Or.inr ⟨Nat.eq_of_beq_eq_true h10, h⟩))
      · rw [h32] at h
        dsimp only at h
        exact Or.inr (Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true h32, h⟩))
    · rw [h45] at h
      dsimp only at h
      obtain ⟨h1, h⟩ := brec_and h
      obtain ⟨h2, h⟩ := brec_and h
      obtain ⟨h3, h⟩ := brec_and h
      exact Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true h45, Nat.le_of_ble_eq_true h1,
        Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, h⟩)
  · rw [hd] at h
    dsimp only at h
    rw [strictB_eq, strictB_eq] at h
    obtain ⟨hdig, he⟩ := decV_dig hd
    rw [he] at h
    exact Or.inl ⟨hdig, h⟩

theorem not_dig_10 : ¬ IsDig 10 := by unfold IsDig; omega
theorem not_dig_32 : ¬ IsDig 32 := by unfold IsDig; omega

theorem no_nl {w lines sgn : Nat} {C : Nat → List Nat} {E : Nat → Nat} :
    ∀ (bs : List Nat) (L e t v ng cur j : Nat) (rest : List Nat), lines ≤ L →
      decRun w lines sgn C E bs L e t v ng cur j rest = true → 10 ∉ bs
  | [], _, _, _, _, _, _, _, _, _, _ => List.not_mem_nil
  | c :: bs, L, e, t, v, ng, cur, j, rest, hL, h => by
    rcases decRun_step h with ⟨hc, h'⟩ | ⟨rfl, -, -, -, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩
    · intro hm
      rcases List.mem_cons.mp hm with hm | hm
      · subst hm
        exact not_dig_10 hc
      · exact no_nl bs L e _ _ _ cur j rest hL h' hm
    · intro hm
      rcases List.mem_cons.mp hm with hm | hm
      · exact absurd hm (by decide)
      · exact no_nl bs L e t v 1 cur j rest hL h' hm
    · obtain ⟨-, -, hk, -⟩ := tokEnd_spec h'
      intro hm
      rcases List.mem_cons.mp hm with hm | hm
      · exact absurd hm (by decide)
      · by_cases hj : j + 1 = 32
        · exact no_nl bs L _ 0 0 0 _ 0 _ hL ((hk rfl).1 hj).2 hm
        · exact no_nl bs L _ 0 0 0 _ _ rest hL ((hk rfl).2 hj) hm
    · obtain ⟨-, -, -, hk⟩ := tokEnd_spec h'
      exact absurd (hk rfl).1 (by omega)

theorem getLast?_tail {c : Nat} {bs : List Nat} (h : (c :: bs).getLast? = some 10) (hc : c ≠ 10) :
    bs.getLast? = some 10 := by
  cases bs with
  | nil =>
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    exact absurd h hc
  | cons b bs => rwa [List.getLast?_cons_cons] at h

theorem splitOnP_tok {tok l : List Nat} (ht : ∀ d ∈ tok, d ≠ 32) :
    List.splitOnP (· == 32) (tok ++ 32 :: l) = tok :: List.splitOnP (· == 32) l :=
  List.splitOnP_append_cons_of_forall_mem (fun d hd => by
    rw [beq_eq_false_iff_ne]
    exact ht d hd) 32 rfl l

theorem splitOnP_tok_end {tok : List Nat} (ht : ∀ d ∈ tok, d ≠ 32) :
    List.splitOnP (· == 32) tok = [tok] :=
  List.splitOnP_eq_singleton (fun d hd => by
    rw [beq_eq_false_iff_ne]
    exact ht d hd)

@[expose] def TokS (sgn L x : Nat) (p : List Nat) : Prop :=
  (L < sgn ∧ TokOK x p) ∨ (sgn ≤ L ∧ ((∃ v, TokOK v p ∧ x = 2 * v) ∨
    ∃ v q, p = 45 :: q ∧ TokOK v q ∧ x = 2 * v + 1))

theorem TokS.unsigned {sgn L x : Nat} {p : List Nat} (h : TokS sgn L x p) (hL : L < sgn) :
    TokOK x p := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · omega

theorem TokS.chars {sgn L x : Nat} {p : List Nat} (h : TokS sgn L x p) :
    p ≠ [] ∧ ∀ d ∈ p, d = 45 ∨ IsDig d := by
  rcases h with ⟨-, hne, hd, -⟩ | ⟨-, ⟨v, ⟨hne, hd, -⟩, -⟩ | ⟨v, q, rfl, ⟨-, hd, -⟩, -⟩⟩
  · exact ⟨hne, fun d h => Or.inr (hd d h)⟩
  · exact ⟨hne, fun d h => Or.inr (hd d h)⟩
  · refine ⟨List.cons_ne_nil _ _, fun d h => ?_⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (hd d h)

theorem tokS_pre {sgn L ng : Nat} {tok : List Nat} (hne : tok ≠ []) (ht : ∀ d ∈ tok, IsDig d)
    (hng : ng = 0 ∨ (ng = 1 ∧ sgn ≤ L)) :
    TokS sgn L (tokCode sgn L (dval tok) ng) (List.replicate ng 45 ++ tok) := by
  have hT : TokOK (dval tok) tok := ⟨hne, ht, rfl⟩
  unfold tokCode
  by_cases hL : L < sgn
  · rw [Nat.blt_eq.mpr hL]
    rcases hng with rfl | ⟨-, h⟩
    · exact Or.inl ⟨hL, hT⟩
    · omega
  · rw [blt_false hL]
    refine Or.inr ⟨by omega, ?_⟩
    rcases hng with rfl | ⟨rfl, -⟩
    · exact Or.inl ⟨dval tok, hT, rfl⟩
    · exact Or.inr ⟨dval tok, tok, rfl, hT, rfl⟩

theorem pre_ne {ng : Nat} {tok : List Nat} (ht : ∀ d ∈ tok, IsDig d) :
    ∀ d ∈ List.replicate ng 45 ++ tok, d ≠ 32 := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · rw [List.eq_of_mem_replicate hd]
    decide
  · have := ht d hd
    unfold IsDig at this
    omega

@[expose] def LineOK (sgn w : Nat) (C : Nat → List Nat) (E : Nat → Nat) (L : Nat) (l : List Nat) :
    Prop :=
  (List.splitOnP (· == 32) l).length = E L ∧ ∀ e (he : e < (List.splitOnP (· == 32) l).length),
    TokS sgn L (fieldAt w (joinW w (C L)) e) (List.splitOnP (· == 32) l)[e]

theorem line_run {w lines sgn : Nat} {C : Nat → List Nat} {E : Nat → Nat} :
    ∀ (bs : List Nat) (L e : Nat) (tok : List Nat) (ng cur j : Nat) (rest : List Nat),
      L < lines → j < 32 → (∀ d ∈ tok, IsDig d) → (ng = 0 ∨ (ng = 1 ∧ sgn ≤ L)) →
      gv w cur j rest = joinW w (C L) >>> (w * e) →
      decRun w lines sgn C E bs L e tok.length (dval tok) ng cur j rest = true →
      bs.getLast? = some 10 →
      ∃ l bs', bs = l ++ 10 :: bs' ∧ 10 ∉ l ∧
        decRun w lines sgn C E bs' (L + 1) 0 0 0 0 (lhead (C (L + 1))) 0 (ltail (C (L + 1))) = true ∧
        (List.splitOnP (· == 32) (List.replicate ng 45 ++ tok ++ l)).length + e = E L ∧
        ∀ i (hi : i < (List.splitOnP (· == 32) (List.replicate ng 45 ++ tok ++ l)).length),
          TokS sgn L (fieldAt w (joinW w (C L)) (e + i))
            (List.splitOnP (· == 32) (List.replicate ng 45 ++ tok ++ l))[i]
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, hl => by simp at hl
  | c :: bs, L, e, tok, ng, cur, j, rest, hL, hj, ht, hng, hg, h, hl => by
    have hfield : cur % 2 ^ w = fieldAt w (joinW w (C L)) e := by
      rw [← gv_mod w cur j rest hj, hg, fieldAt_eq_mod]
    rcases decRun_step h with ⟨hc, h'⟩ | ⟨rfl, hs, ht0, hn0, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩
    ·
      have hc10 : c ≠ 10 := fun e => not_dig_10 (e ▸ hc)
      have h' : decRun w lines sgn C E bs L e (tok ++ [c]).length (dval (tok ++ [c])) ng cur j rest =
          true := by
        rw [List.length_append, List.length_singleton, dval_snoc]
        exact h'
      obtain ⟨l, bs', e1, e2, e3, e4, e5⟩ := line_run bs L e (tok ++ [c]) ng cur j rest hL hj
        (fun d hd => by
          rcases List.mem_append.mp hd with hd | hd
          · exact ht d hd
          · rw [List.mem_singleton.mp hd]; exact hc) hng hg h' (getLast?_tail hl hc10)
      have hpre : List.replicate ng 45 ++ tok ++ c :: l = List.replicate ng 45 ++ (tok ++ [c]) ++ l := by
        simp
      refine ⟨c :: l, bs', by rw [e1]; rfl, ?_, e3, ?_, ?_⟩
      · intro hm
        rcases List.mem_cons.mp hm with hm | hm
        · exact hc10 hm.symm
        · exact e2 hm
      · rw [hpre]
        exact e4
      · rw [hpre]
        exact e5
    ·
      have htok : tok = [] := List.eq_nil_of_length_eq_zero ht0
      subst htok hn0
      obtain ⟨l, bs', e1, e2, e3, e4, e5⟩ := line_run bs L e [] 1 cur j rest hL hj
        (fun d hd => absurd hd List.not_mem_nil) (Or.inr ⟨rfl, hs⟩) hg h'
        (getLast?_tail hl (by decide))
      have hpre : List.replicate 0 45 ++ [] ++ 45 :: l = List.replicate 1 45 ++ [] ++ l := rfl
      refine ⟨45 :: l, bs', by rw [e1]; rfl, ?_, e3, ?_, ?_⟩
      · intro hm
        rcases List.mem_cons.mp hm with hm | hm
        · exact absurd hm (by decide)
        · exact e2 hm
      · rw [hpre]
        exact e4
      · rw [hpre]
        exact e5
    ·
      obtain ⟨h1, h2, hk, -⟩ := tokEnd_spec h'
      have hne : tok ≠ [] := fun hn => by subst hn; simp at h1
      have htok : TokS sgn L (fieldAt w (joinW w (C L)) e) (List.replicate ng 45 ++ tok) := by
        rw [← hfield, ← h2]
        exact tokS_pre hne ht hng
      have hcont : ∃ cur' j' rest', j' < 32 ∧
          gv w cur' j' rest' = joinW w (C L) >>> (w * (e + 1)) ∧
          decRun w lines sgn C E bs L (e + 1) ([] : List Nat).length (dval []) 0 cur' j' rest' =
            true := by
        have hshift : joinW w (C L) >>> (w * (e + 1)) = gv w cur j rest >>> w := by
          rw [hg, Nat.mul_succ, Nat.shiftRight_add]
        by_cases hj1 : j + 1 = 32
        · obtain ⟨hz, hk⟩ := (hk rfl).1 hj1
          refine ⟨lhead rest, 0, ltail rest, by decide, ?_, hk⟩
          rw [hshift]
          unfold gv
          rw [show 32 - j = 1 by omega, Nat.mul_one, or_shl_shr', hz, Nat.zero_or, Nat.sub_zero,
            joinW_head]
        · refine ⟨cur >>> w, j + 1, rest, by omega, ?_, (hk rfl).2 hj1⟩
          rw [hshift]
          unfold gv
          rw [show 32 - j = 32 - (j + 1) + 1 by omega, Nat.mul_succ, or_shl_shr]
      obtain ⟨cur', j', rest', hj', hg', hc'⟩ := hcont
      obtain ⟨l, bs', e1, e2, e3, e4, e5⟩ := line_run bs L (e + 1) [] 0 cur' j' rest' hL hj'
        (fun d hd => absurd hd List.not_mem_nil) (Or.inl rfl) hg' hc' (getLast?_tail hl (by decide))
      rw [List.replicate_zero, List.nil_append, List.nil_append] at e4 e5
      refine ⟨32 :: l, bs', by rw [e1]; rfl, ?_, e3, ?_, ?_⟩
      · intro hm
        rcases List.mem_cons.mp hm with hm | hm
        · exact absurd hm (by decide)
        · exact e2 hm
      · rw [splitOnP_tok (pre_ne ht), List.length_cons]
        omega
      · intro i hi
        simp only [splitOnP_tok (pre_ne ht)] at hi ⊢
        cases i with
        | zero => simpa using htok
        | succ i =>
          simp only [List.getElem_cons_succ]
          rw [show e + (i + 1) = e + 1 + i by omega]
          exact e5 i (by simp at hi; omega)
    ·
      obtain ⟨h1, h2, -, hk⟩ := tokEnd_spec h'
      obtain ⟨-, hE, hk⟩ := hk rfl
      have hne : tok ≠ [] := fun hn => by subst hn; simp at h1
      have htok : TokS sgn L (fieldAt w (joinW w (C L)) e) (List.replicate ng 45 ++ tok) := by
        rw [← hfield, ← h2]
        exact tokS_pre hne ht hng
      refine ⟨[], bs, rfl, List.not_mem_nil, hk, ?_, ?_⟩
      · rw [List.append_nil, splitOnP_tok_end (pre_ne ht)]
        simp only [List.length_singleton]
        omega
      · intro i hi
        simp only [List.append_nil, splitOnP_tok_end (pre_ne ht), List.length_singleton] at hi ⊢
        have : i = 0 := by omega
        subst this
        simpa using htok
where
  fieldAt_eq_mod : ∀ {w X e : Nat}, (X >>> (w * e)) % 2 ^ w = fieldAt w X e := fun {w X e} => by
    change _ = (X >>> (w * e)) &&& ((1 <<< w) - 1)
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]

theorem decRun_lines {w lines sgn : Nat} {C : Nat → List Nat} {E : Nat → Nat} :
    ∀ (n : Nat) (bs : List Nat) (L : Nat), L + n = lines →
      decRun w lines sgn C E bs L 0 0 0 0 (lhead (C L)) 0 (ltail (C L)) = true →
      (bs = [] ∨ bs.getLast? = some 10) →
      ∃ ls : List (List Nat), ls.length = n ∧ bs = (ls.map (· ++ [10])).flatten ∧
        ∀ i (hi : i < ls.length), 10 ∉ ls[i] ∧ LineOK sgn w C E (L + i) ls[i]
  | 0, bs, L, hn, h, hl => by
    have h10 := no_nl bs L 0 0 0 0 _ 0 _ (by omega) h
    refine ⟨[], rfl, ?_, fun i hi => absurd hi (by simp)⟩
    rcases hl with hl | hl
    · rw [hl]; rfl
    · exact absurd (List.mem_of_getLast? hl) h10
  | n + 1, bs, L, hn, h, hl => by
    rcases hl with rfl | hl
    · change Bool.rec (motive := fun _ => Bool) false _ (Nat.beq L lines) = true at h
      have : Nat.beq L lines = false := by
        cases hb : Nat.beq L lines
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) (by omega)
      rw [this] at h
      exact absurd h (by decide)
    have hg : gv w (lhead (C L)) 0 (ltail (C L)) = joinW w (C L) >>> (w * 0) := by
      unfold gv
      rw [Nat.mul_zero, Nat.shiftRight_zero, Nat.sub_zero, joinW_head]
    obtain ⟨l, bs', e1, e2, e3, e4, e5⟩ := line_run bs L 0 [] 0 (lhead (C L)) 0 (ltail (C L))
      (by omega) (by decide) (fun d hd => absurd hd List.not_mem_nil) (Or.inl rfl) hg h hl
    rw [List.replicate_zero, List.nil_append, List.nil_append] at e4 e5
    have hl' : bs' = [] ∨ bs'.getLast? = some 10 := by
      rcases bs'.eq_nil_or_concat with h' | ⟨bs'', b, rfl⟩
      · exact Or.inl h'
      · right
        rw [e1] at hl
        simp only [List.getLast?_append, List.getLast?_cons, List.getLast?_concat] at hl ⊢
        simpa using hl
    obtain ⟨ls, f1, f2, f3⟩ := decRun_lines n bs' (L + 1) (by omega) e3 hl'
    refine ⟨l :: ls, by simp [f1], by rw [e1, f2]; simp, fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨e2, by simpa using e4, fun e he => by simpa using e5 e he⟩
    | succ i =>
      have := f3 i (by simp at hi; omega)
      rw [show L + (i + 1) = L + 1 + i by omega]
      simpa using this

theorem charOfNat_toNat {x : Nat} (hx : x < 128) : (Char.ofNat x).toNat = x := by
  simp [Char.ofNat, Char.ofNatAux, Nat.isValidChar, hx, (by omega : x < 55296), Char.toNat]

theorem charOfNat_beq {x y : Nat} (hx : x < 128) (hy : y < 128) :
    (Char.ofNat x == Char.ofNat y) = (x == y) := by
  by_cases h : x = y
  · subst h
    simp
  · have : Char.ofNat x ≠ Char.ofNat y := fun e => h (by
      rw [← charOfNat_toNat hx, ← charOfNat_toNat hy, e])
    simp [this, h]

theorem splitOnPPrepend_map {α β : Type} (p : β → Bool) (q : α → Bool) (f : α → β) :
    ∀ (l acc : List α), (∀ x ∈ l, p (f x) = q x) →
      List.splitOnPPrepend p (l.map f) (acc.map f) = (List.splitOnPPrepend q l acc).map (List.map f)
  | [], acc, _ => by simp
  | x :: l, acc, h => by
    rw [List.map_cons, List.splitOnPPrepend_cons_eq_ite, List.splitOnPPrepend_cons_eq_ite,
      h x List.mem_cons_self]
    have ih := splitOnPPrepend_map p q f l
    split
    · rw [List.map_cons, ← List.splitOnPPrepend_nil_right, ← List.splitOnPPrepend_nil_right,
        ← List.map_nil (f := f), ih [] (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      simp
    · rw [← List.map_cons, ih (x :: acc) (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem splitOnP_map {α β : Type} (p : β → Bool) (q : α → Bool) (f : α → β) (l : List α)
    (h : ∀ x ∈ l, p (f x) = q x) :
    List.splitOnP p (l.map f) = (List.splitOnP q l).map (List.map f) := by
  have := splitOnPPrepend_map p q f l [] h
  simpa using this

theorem splitOnP_lines {α : Type} (p : α → Bool) {s : α} (hs : p s = true) :
    ∀ ls : List (List α), (∀ l ∈ ls, ∀ x ∈ l, p x = false) →
      List.splitOnP p ((ls.map (· ++ [s])).flatten) = ls ++ [[]]
  | [], _ => by simp
  | l :: ls, h => by
    rw [List.map_cons, List.flatten_cons, List.append_assoc, List.singleton_append,
      List.splitOnP_append_cons_of_forall_mem (h l List.mem_cons_self) s hs,
      splitOnP_lines p hs ls (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))]
    rfl

theorem toNat!_of {s : String} {v : Nat} (h : s.toNat? = some v) : s.toNat! = v := by
  unfold String.toNat? String.Slice.toNat? at h
  unfold String.toNat! String.Slice.toNat!
  split at h
  · rw [if_pos ‹_›]
    exact Option.some.inj h
  · exact absurd h (by simp)

theorem ofDigitChars_map (ds : List Nat) (hd : ∀ d ∈ ds, IsDig d) :
    Nat.ofDigitChars 10 (ds.map Char.ofNat) 0 = dval ds := by
  rw [Nat.ofDigitChars_eq_foldl, List.foldl_map, show '0'.toNat = 48 from rfl]
  unfold dval
  generalize 0 = a
  induction ds generalizing a with
  | nil => rfl
  | cons d ds ih =>
    rw [List.foldl_cons, List.foldl_cons]
    have hd0 := hd d List.mem_cons_self
    unfold IsDig at hd0
    rw [charOfNat_toNat (x := d) (by omega), Nat.mul_comm]
    exact ih (fun x hx => hd x (List.mem_cons_of_mem _ hx)) _

theorem tok_value {p : List Nat} {x : Nat} (h : TokOK x p) :
    (String.ofList (p.map Char.ofNat)).toNat! = x := by
  obtain ⟨hne, hd, hv⟩ := h
  apply toNat!_of
  rw [CFSG.KS.SporSch.LyTxt.toNat_digits (fun c hc => ?_) (by simpa using hne),
    ofDigitChars_map p hd, hv]
  obtain ⟨d, hdm, rfl⟩ := List.mem_map.mp hc
  have := hd d hdm
  unfold IsDig at this
  apply CFSG.KS.SporSch.LyTxt.isDigit_of
  rw [charOfNat_toNat (x := d) (by omega), Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq]
  omega

theorem foldl_push (ps : List String) (acc : Array Nat) (h : ∀ p ∈ ps, p.isEmpty = false) :
    ps.foldl (fun a t => if t.isEmpty then a else a.push t.toNat!) acc =
      acc ++ (ps.map String.toNat!).toArray := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, if_neg (by simp [h p List.mem_cons_self]),
      ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    simp

theorem isEmpty_ofList (l : List Char) : (String.ofList l).isEmpty = l.isEmpty := by
  cases l with
  | nil => rfl
  | cons c l => simp

theorem mem_intercalate_sep {α : Type} {s x : α} : ∀ ts : List (List α),
    x ∈ [s].intercalate ts → x = s ∨ ∃ t ∈ ts, x ∈ t
  | [], h => by simp at h
  | [t], h => Or.inr ⟨t, List.mem_singleton_self t, by simpa using h⟩
  | t :: u :: r, h => by
    rw [List.intercalate_cons_cons] at h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inr ⟨t, List.mem_cons_self, h⟩
      · exact Or.inl (List.mem_singleton.mp h)
    · rcases mem_intercalate_sep (u :: r) h with h | ⟨t', ht', hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', hx⟩

theorem dig_lt {d : Nat} (h : IsDig d) : d < 128 := by unfold IsDig at h; omega

theorem line_chars {sgn w : Nat} {C : Nat → List Nat} {E : Nat → Nat} {L : Nat} {l : List Nat}
    (h : LineOK sgn w C E L l) : (∀ x ∈ l, x < 128 ∧ x ≠ 10) ∧ l ≠ [] := by
  obtain ⟨-, htok⟩ := h
  set toks := List.splitOnP (· == 32) l with htoks
  have hl : l = [32].intercalate toks := by
    rw [htoks, ← List.splitOn_eq_splitOnP, List.intercalate_splitOn]
  have hmem : ∀ x ∈ l, x = 32 ∨ x = 45 ∨ IsDig x := by
    intro x hx
    rw [hl] at hx
    rcases mem_intercalate_sep toks hx with hx | ⟨p, hp, hxp⟩
    · exact Or.inl hx
    · obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hp
      exact Or.inr ((htok e he).chars.2 x hxp)
  refine ⟨fun x hx => ?_, fun hn => ?_⟩
  · rcases hmem x hx with rfl | rfl | hd
    · decide
    · decide
    · exact ⟨dig_lt hd, fun e => not_dig_10 (e ▸ hd)⟩
  · have : toks = [[]] := by rw [htoks, hn, List.splitOnP_nil]
    have h0 := (htok 0 (by rw [this]; simp)).chars.1
    simp [this] at h0

theorem parseNats_line {sgn w : Nat} {C : Nat → List Nat} {E : Nat → Nat} {L : Nat} {l : List Nat}
    (h : LineOK sgn w C E L l) (hL : L < sgn) :
    CFSG.YGroups.ModelNative.parseNats (String.ofList (l.map Char.ofNat)) =
      Array.ofFn (n := E L) (fun i => fieldAt w (joinW w (C L)) i.val) := by
  obtain ⟨hlt, -⟩ := line_chars h
  obtain ⟨hlen, htok'⟩ := h
  have htok := fun e he => (htok' e he).unsigned hL
  set toks := List.splitOnP (· == 32) l with htoks
  unfold CFSG.YGroups.ModelNative.parseNats
  rw [CFSG.KS.SporSch.LyTxt.splitOn_sp, List.splitOnPPrepend_nil_right,
    splitOnP_map (· == ' ') (· == 32) Char.ofNat l (fun x hx => charOfNat_beq (hlt x hx).1 (by decide)),
    ← htoks, List.map_map, foldl_push _ _ (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hq
      rw [Function.comp_apply, isEmpty_ofList]
      simpa using (htok e he).1)]
  apply Array.ext
  · simp [hlen]
  · intro i h1 h2
    simp only [List.map_map, Array.size_append, List.size_toArray, List.length_map] at h1
    simp only [Array.getElem_ofFn]
    simp only [Array.empty_append, List.getElem_toArray, List.getElem_map, Function.comp_apply]
    exact tok_value (htok i (by simpa using h1))

@[expose] def decI (x : Nat) : Int := if x % 2 = 1 then -((x / 2 : Nat) : Int) else ((x / 2 : Nat) : Int)

theorem toInt!_of {s : String} {v : Int} (h : s.toInt? = some v) : s.toInt! = v := by
  unfold String.toInt? at h
  unfold String.toInt! String.Slice.toInt!
  rw [h]

theorem digits_map {p : List Nat} (hd : ∀ d ∈ p, IsDig d) : ∀ c ∈ p.map Char.ofNat, c.isDigit = true := by
  intro c hc
  obtain ⟨d, hdm, rfl⟩ := List.mem_map.mp hc
  have := hd d hdm
  unfold IsDig at this
  apply CFSG.KS.SporSch.LyTxt.isDigit_of
  rw [charOfNat_toNat (x := d) (by omega), Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq]
  omega

theorem tokS_int {sgn L x : Nat} {p : List Nat} (h : TokS sgn L x p) (hL : sgn ≤ L) :
    (String.ofList (p.map Char.ofNat)).toInt! = decI x := by
  rcases h with ⟨h, -⟩ | ⟨-, ⟨v, ⟨hne, hd, hv⟩, rfl⟩ | ⟨v, q, rfl, ⟨hne, hd, hv⟩, rfl⟩⟩
  · omega
  · apply toInt!_of
    have := CFSG.KS.SporSch.LyTxt.tv_pos (digits_map hd) (by simpa using hne)
    unfold CFSG.KS.SporSch.LyTxt.tv at this
    rw [this, ofDigitChars_map p hd, hv]
    unfold decI
    rw [if_neg (by omega)]
    congr 2
    omega
  · apply toInt!_of
    have := CFSG.KS.SporSch.LyTxt.tv_neg (digits_map hd) (by simpa using hne)
    unfold CFSG.KS.SporSch.LyTxt.tv at this
    rw [List.map_cons, show Char.ofNat 45 = '-' from rfl, this, ofDigitChars_map q hd, hv]
    unfold decI
    rw [if_pos (by omega)]
    congr 3
    omega

theorem parseInts_line {sgn w : Nat} {C : Nat → List Nat} {E : Nat → Nat} {L : Nat} {l : List Nat}
    (h : LineOK sgn w C E L l) (hL : sgn ≤ L) :
    CFSG.YGroups.ModelNative.parseInts (String.ofList (l.map Char.ofNat)) =
      (List.range (E L)).map fun i => decI (fieldAt w (joinW w (C L)) i) := by
  obtain ⟨hlt, -⟩ := line_chars h
  obtain ⟨hlen, htok⟩ := h
  set toks := List.splitOnP (· == 32) l with htoks
  unfold CFSG.YGroups.ModelNative.parseInts
  rw [CFSG.KS.SporSch.LyTxt.splitOn_sp, List.splitOnPPrepend_nil_right,
    splitOnP_map (· == ' ') (· == 32) Char.ofNat l (fun x hx => charOfNat_beq (hlt x hx).1 (by decide)),
    ← htoks, List.filterMap_map, List.filterMap_map]
  have hf : ∀ p ∈ toks, (((fun t : String => if t.isEmpty = true then none else some t.toInt!) ∘
      String.ofList) ∘ List.map Char.ofNat) p = some (String.ofList (p.map Char.ofNat)).toInt! := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hp
    simp only [Function.comp_apply, isEmpty_ofList]
    rw [if_neg (by simpa using (htok e he).chars.1)]
  rw [List.filterMap_congr hf, List.filterMap_eq_map']
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact tokS_int (htok i (by simpa using h1)) hL

theorem textLines_eq {sgn w : Nat} {C : Nat → List Nat} {E : Nat → Nat} {bs : List Nat}
    {ls : List (List Nat)} (hbs : bs = (ls.map (· ++ [10])).flatten)
    (hls : ∀ i (hi : i < ls.length), 10 ∉ ls[i] ∧ LineOK sgn w C E (0 + i) ls[i]) :
    CFSG.YGroups.ModelNative.textLines (String.ofList (bs.map Char.ofNat)) =
      ls.map fun l => String.ofList (l.map Char.ofNat) := by
  have hc := fun i (hi : i < ls.length) => line_chars (hls i hi).2
  have hall : ∀ x ∈ bs, x < 128 := by
    intro x hx
    rw [hbs] at hx
    obtain ⟨_, hl', hx⟩ := List.mem_flatten.mp hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
      exact ((hc i hi).1 x hx).1
    · rw [List.mem_singleton.mp hx]; decide
  unfold CFSG.YGroups.ModelNative.textLines
  rw [CFSG.KS.SporSch.LyTxt.splitOn_nl, List.splitOnPPrepend_nil_right,
    splitOnP_map (· == '\n') (· == 10) Char.ofNat bs (fun x hx => charOfNat_beq (hall x hx) (by decide)),
    hbs, splitOnP_lines (· == 10) rfl ls (fun l hl x hx => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
      simpa using ((hc i hi).1 x hx).2)]
  rw [List.map_append, List.map_append, List.filter_append]
  simp only [List.map_cons, List.map_nil, List.filter_cons, isEmpty_ofList]
  simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
    List.append_nil]
  rw [List.filter_eq_self.mpr, List.map_map]
  · rfl
  intro s hs
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hs
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl'
  rw [isEmpty_ofList]
  simpa using (hc i hi).2

theorem parsePerms_of_decBind {bs : List Nat} {w lines : Nat} {C : Nat → List Nat} {E : Nat → Nat}
    (h : decBind bs w lines lines C E = true) (hl : bs.getLast? = some 10) :
    CFSG.YGroups.ModelNative.parsePerms (String.ofList (bs.map Char.ofNat)) =
      ((List.range lines).map fun L =>
        Array.ofFn (n := E L) (fun i => fieldAt w (joinW w (C L)) i.val)).toArray := by
  unfold decBind at h
  obtain ⟨-, h⟩ := brec_and h
  obtain ⟨-, h⟩ := brec_and h
  obtain ⟨ls, hlen, hbs, hls⟩ := decRun_lines lines bs 0 (by omega) h (Or.inr hl)
  unfold CFSG.YGroups.ModelNative.parsePerms
  rw [textLines_eq hbs hls]
  congr 1
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp only [List.map_map, List.getElem_map, Function.comp_apply]
    have hi : i < ls.length := by simpa using h1
    have := (hls i hi).2
    rw [Nat.zero_add] at this
    rw [List.getElem_range]
    exact parseNats_line this (by omega)

theorem chain_of_decBind {bs : List Nat} {w lines : Nat} {C : Nat → List Nat} {E : Nat → Nat}
    (h : decBind bs w lines 1 C E = true) (hl : bs.getLast? = some 10) (hpos : 0 < lines) :
    CFSG.YGroups.ModelNative.chainBase (String.ofList (bs.map Char.ofNat)) =
        Array.ofFn (n := E 0) (fun i => fieldAt w (joinW w (C 0)) i.val) ∧
      CFSG.YGroups.ModelNative.chainWords (String.ofList (bs.map Char.ofNat)) =
        ((List.range (lines - 1)).map fun L =>
          (List.range (E (L + 1))).map fun i => decI (fieldAt w (joinW w (C (L + 1))) i)).toArray := by
  unfold decBind at h
  obtain ⟨-, h⟩ := brec_and h
  obtain ⟨-, h⟩ := brec_and h
  obtain ⟨ls, hlen, hbs, hls⟩ := decRun_lines lines bs 0 (by omega) h (Or.inr hl)
  unfold CFSG.YGroups.ModelNative.chainBase CFSG.YGroups.ModelNative.chainWords
  rw [textLines_eq hbs hls]
  obtain ⟨l0, ls', rfl⟩ : ∃ l0 ls', ls = l0 :: ls' := by
    cases ls with
    | nil => simp at hlen; omega
    | cons l0 ls' => exact ⟨l0, ls', rfl⟩
  refine ⟨?_, ?_⟩
  · simp only [List.map_cons, List.headD_cons]
    exact parseNats_line (hls 0 (by simp)).2 (by decide)
  · simp only [List.map_cons, List.drop_succ_cons, List.drop_zero, List.map_map]
    congr 1
    apply List.ext_getElem
    · simp at hlen ⊢
      omega
    · intro i h1 h2
      simp only [List.getElem_map, Function.comp_apply, List.getElem_range]
      have hi : i + 1 < (l0 :: ls').length := by simpa using h1
      have := (hls (i + 1) hi).2
      rw [Nat.zero_add] at this
      exact parseInts_line this (by omega)

@[expose] noncomputable def lastB : List (Nat × Nat) → Option Nat
  | [] => none
  | (N, len) :: L => (lastB L).or (decChunk len N []).getLast?

theorem decChunk_append (len : Nat) : ∀ (N : Nat) (t : List Nat),
    decChunk len N t = decChunk len N [] ++ t := by
  induction len with
  | zero => intro N t; rfl
  | succ len ih =>
    intro N t
    change List.cons _ (decChunk len _ t) = List.cons _ (decChunk len _ []) ++ t
    rw [ih, List.cons_append]

theorem getLast?_bytesOf_eq : ∀ CH : List (Nat × Nat), (bytesOf CH).getLast? = lastB CH
  | [] => rfl
  | (N, len) :: L => by
    change (decChunk len N (bytesOf L)).getLast? = _
    rw [decChunk_append, List.getLast?_append, getLast?_bytesOf_eq L]
    rfl

theorem getLast?_bytesOf {CH : List (Nat × Nat)} (h : lastB CH = some 10) :
    (bytesOf CH).getLast? = some 10 := by
  rw [getLast?_bytesOf_eq, h]

end CFSG.KC.YModel.TextSem

end
