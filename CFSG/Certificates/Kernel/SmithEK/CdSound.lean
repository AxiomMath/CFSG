module

public import Certificates.Data.Kernel.SmithEKCd
public import CFSG.Certificates.Kernel.SmithEK.OSound
public import CFSG.LargeExtraspecial.S14SMKTransCheck
public import CFSG.Sporadic.Th.TableSpec
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.SmithE.K

open CFSG.KC.Misc.O73 CFSG.F4.Native

theorem cdCo_eq (c i : Nat) : cdCo c i = coord c i := by
  unfold cdCo coord
  have h3 : (3 : Nat) = 2 ^ 2 - 1 := rfl
  change (c >>> (2 * i)) &&& 3 = _
  rw [Nat.shiftRight_eq_div_pow, h3, Nat.and_two_pow_sub_one_eq_mod, pow_mul]
  rfl

theorem cdMul_eq (x y : Nat) : cdMul x y = f4mul x y := rfl

theorem cdMapC_rec (g : Nat → Nat → Nat) (c : Nat) : ∀ n,
    Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.add acc (Nat.mul (g i (cdCo c i)) (Nat.pow 4 i))) n =
      (List.range n).foldl (fun acc i => acc + g i (coord c i) * 4 ^ i) 0
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, ← cdMapC_rec g c n, List.foldl_cons, List.foldl_nil,
      ← cdCo_eq]
    rfl

theorem cdMapC_eq (g : Nat → Nat → Nat) (c : Nat) :
    cdMapC g c = (List.range 6).foldl (fun acc i => acc + g i (coord c i) * 4 ^ i) 0 :=
  cdMapC_rec g c 6

theorem cdFrob_eq (c : Nat) : cdFrob c = frobC c := by
  unfold cdFrob frobC
  rw [cdMapC_eq]
  rfl

theorem cdDlt_eq (c : Nat) : cdDlt c = dltC c := by
  unfold cdDlt dltC
  rw [cdMapC_eq]
  refine congrArg (fun f => List.foldl f 0 (List.range 6)) ?_
  funext acc i
  have hb : Nat.blt i 2 = decide (i < 2) :=
    Bool.eq_iff_iff.2 (by rw [Nat.blt_eq, decide_eq_true_iff])
  rw [hb, cdMul_eq]
  by_cases hi : i < 2 <;> simp [hi]

theorem cdLead_eq (c : Nat) : cdLead c = leadC c := by
  have e : cdLead c = (List.range 6).foldr
      (fun i acc => bif Nat.beq (coord c i) 0 then acc else coord c i) 0 := by
    unfold cdLead
    simp only [cdCo_eq]
    rfl
  rw [e]
  unfold leadC
  refine congrArg (fun f => List.foldr f 0 (List.range 6)) ?_
  funext i acc
  cases h : Nat.beq (coord c i) 0
  · have h' := Nat.ne_of_beq_eq_false h
    simp [h']
  · have h' := Nat.eq_of_beq_eq_true h
    simp [h']

theorem cdNorm_eq (c : Nat) : cdNorm c = normC c := by
  unfold cdNorm normC scaleC
  rw [cdMapC_eq, cdLead_eq]
  rfl

theorem cdFB_rec (u v : Nat) : ∀ n,
    Nat.rec (motive := fun _ => Bool) false
      (fun k acc => xor acc (xor (bitK u (Nat.mul 2 k) && bitK v (Nat.add (Nat.mul 2 k) 1))
        (bitK u (Nat.add (Nat.mul 2 k) 1) && bitK v (Nat.mul 2 k)))) n =
      (List.range n).foldl (fun acc k => acc ^^
        ((u.testBit (2 * k) && v.testBit (2 * k + 1)) ^^ (u.testBit (2 * k + 1) && v.testBit (2 * k))))
        false
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, ← cdFB_rec u v n, List.foldl_cons, List.foldl_nil,
      ← bitK_eq, ← bitK_eq, ← bitK_eq, ← bitK_eq]
    rfl

theorem cdFB_eq (u v : Nat) : cdFB u v = fB u v := cdFB_rec u v 10

theorem cd_xorSel_cons (b : Nat) (bs : List Nat) (m : Nat) :
    xorSel (b :: bs) m = (if m % 2 = 1 then b else 0) ^^^ xorSel bs (m / 2) := rfl

theorem cdSel_go (m : Nat) : ∀ (bs : List Nat) (k : Nat),
    List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun b _ ih k => Nat.xor (bif bitK m k then b else 0) (ih (Nat.succ k))) bs k =
      xorSel bs (m >>> k)
  | [], _ => rfl
  | b :: bs, k => by
    have ih := cdSel_go m bs (k + 1)
    rw [Nat.shiftRight_succ] at ih
    have e1 : bitK m k = decide ((m >>> k) % 2 = 1) := by
      have e : bitK m k = Nat.beq ((m >>> k) % 2) 1 := by
        unfold bitK
        rw [← Nat.and_one_is_mod]
        rfl
      rw [e]
      exact Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, decide_eq_true_iff])
    rw [cd_xorSel_cons, ← ih]
    change Nat.xor (bif bitK m k then b else 0) _ = _
    rw [e1]
    by_cases hk : (m >>> k) % 2 = 1 <;> simp [hk] <;> rfl

theorem cdSel_eq (bs : List Nat) (m : Nat) : cdSel bs m = xorSel bs m := by
  have h := cdSel_go m bs 0
  rw [Nat.shiftRight_zero] at h
  exact h

theorem cd_div_two_xor (m m' : Nat) : (m ^^^ m') / 2 = m / 2 ^^^ m' / 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, ← Nat.testBit_succ, ← Nat.testBit_succ, ← Nat.testBit_succ, Nat.testBit_xor]

theorem cd_ite_xor_mod (m m' b : Nat) : (if (m ^^^ m') % 2 = 1 then b else 0) =
    (if m % 2 = 1 then b else 0) ^^^ (if m' % 2 = 1 then b else 0) := by
  have h' : decide ((m ^^^ m') % 2 = 1) = (decide (m % 2 = 1) ^^ decide (m' % 2 = 1)) := by
    rw [← Nat.testBit_zero, ← Nat.testBit_zero, ← Nat.testBit_zero, Nat.testBit_xor]
  by_cases ha : m % 2 = 1 <;> by_cases hb : m' % 2 = 1
  · rw [decide_eq_true ha, decide_eq_true hb] at h'
    rw [if_neg (of_decide_eq_false h'), if_pos ha, if_pos hb, Nat.xor_self]
  · rw [decide_eq_true ha, decide_eq_false hb] at h'
    rw [if_pos (of_decide_eq_true h'), if_pos ha, if_neg hb, Nat.xor_zero]
  · rw [decide_eq_false ha, decide_eq_true hb] at h'
    rw [if_pos (of_decide_eq_true h'), if_neg ha, if_pos hb, Nat.zero_xor]
  · rw [decide_eq_false ha, decide_eq_false hb] at h'
    rw [if_neg (of_decide_eq_false h'), if_neg ha, if_neg hb, Nat.xor_zero]

theorem cd_xor_four (a b c d : Nat) : a ^^^ b ^^^ (c ^^^ d) = a ^^^ c ^^^ (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> cases d.testBit i <;> rfl

theorem cd_xorSel_xor : ∀ (bs : List Nat) (m m' : Nat),
    xorSel bs (m ^^^ m') = xorSel bs m ^^^ xorSel bs m'
  | [], _, _ => (Nat.xor_self 0).symm
  | b :: bs, m, m' => by
    rw [cd_xorSel_cons, cd_xorSel_cons, cd_xorSel_cons, cd_div_two_xor, cd_xorSel_xor bs, cd_ite_xor_mod,
      cd_xor_four]

theorem cd_xor_mod (a b n : Nat) : (a ^^^ b) % 2 ^ n = a % 2 ^ n ^^^ b % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  cases decide (i < n) <;> cases a.testBit i <;> cases b.testBit i <;> rfl

theorem cdIndK_sound {bs : List Nat} (h : cdIndK bs = true) : indepOK bs = true := by
  have h1 := (recAll_iff (fun m => !Nat.beq (Nat.mod (cdSel bs (Nat.succ m)) (Nat.pow 2 20)) 0)
    (Nat.sub (Nat.pow 2 (lenK bs)) 1)).1 h
  have hnz : ∀ x, 0 < x → x < 2 ^ bs.length → xorSel bs x % 2 ^ 20 ≠ 0 := by
    intro x hx hxl
    have h2 := h1 (x - 1) (by
      change x - 1 < 2 ^ lenK bs - 1
      rw [lenK_eq]
      omega)
    rw [Bool.not_eq_true'] at h2
    have h3 := Nat.ne_of_beq_eq_false h2
    have e : Nat.succ (x - 1) = x := by omega
    rw [e, cdSel_eq] at h3
    exact h3
  refine CFSG.Sporadic.Th.allIn_eq_true.2 fun m _ hm =>
    CFSG.Sporadic.Th.allIn_eq_true.2 fun m' _ hm' => ?_
  rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne]
  by_cases hmm : m = m'
  · exact Or.inl hmm
  · refine Or.inr fun he => ?_
    have hx : 0 < m ^^^ m' := by
      rcases Nat.eq_zero_or_pos (m ^^^ m') with h0 | h0
      · refine absurd ?_ hmm
        calc m = m ^^^ (m' ^^^ m') := by rw [Nat.xor_self, Nat.xor_zero]
          _ = (m ^^^ m') ^^^ m' := (Nat.xor_assoc _ _ _).symm
          _ = m' := by rw [h0, Nat.zero_xor]
      · exact h0
    apply hnz _ hx (Nat.xor_lt_two_pow hm hm')
    rw [cd_xorSel_xor, cd_xor_mod, he, Nat.xor_self]

theorem cdRecAll2_iff (p q : Nat → Bool) : ∀ n : Nat,
    Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && p k && q k) n = true ↔
      ∀ k < n, p k = true ∧ q k = true
  | 0 => ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | n + 1 => by
    have e : Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && p k && q k) (n + 1) =
        (Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && p k && q k) n && p n && q n) :=
      rfl
    rw [e, Bool.and_eq_true, Bool.and_eq_true, cdRecAll2_iff p q n]
    constructor
    · rintro ⟨⟨h, hp⟩, hq⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h k hk
      · exact ⟨hp, hq⟩
    · intro h
      exact ⟨⟨fun k hk => h k (by omega), (h n (by omega)).1⟩, (h n (by omega)).2⟩

theorem cdMapK_sound {f : Nat → Nat} {PC : List Nat} {T : Nat} (h : cdMapK f PC T = true) :
    ∀ p < 693, at' 10 T p < 693 ∧ PC.getD (at' 10 T p) 0 = cdNorm (f (PC.getD p 0)) := by
  have h1 := (cdRecAll2_iff (fun p => Nat.blt (at' 10 T p) 693)
    (fun p => Nat.beq (PC.getD (at' 10 T p) 0) (cdNorm (f (PC.getD p 0)))) 693).1 h
  intro p hp
  have h2 := h1 p hp
  exact ⟨Nat.le_of_ble_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem cdInvK_sound {As : List Nat} {B : Nat} (h : cdInvK As B = true) :
    ∀ x < 693, at' 10 B x < 693 ∧ As.foldr (fun A y => at' 10 A y) (at' 10 B x) = x := by
  have h1 := (cdRecAll2_iff (fun x => Nat.blt (at' 10 B x) 693)
    (fun x => Nat.beq (As.foldr (fun A y => at' 10 A y) (at' 10 B x)) x) 693).1 h
  intro x hx
  have h2 := h1 x hx
  exact ⟨Nat.le_of_ble_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem cdCompK_sound {L : Nat} {As : List Nat} (h : cdCompK L As = true) :
    ∀ x < 693, at' 10 L x = As.foldr (fun A y => at' 10 A y) x := by
  have h1 := (recAll_iff (fun x => Nat.beq (at' 10 L x) (As.foldr (fun A y => at' 10 A y) x))
    693).1 h
  exact fun x hx => Nat.eq_of_beq_eq_true (h1 x hx)

theorem cdSaK_sound {W : List Nat} {L : Nat} {S : List Nat} (h : cdSaK W L S = true) :
    S.length = 21 ∧ (∀ s ∈ S, s < 21) ∧ ∀ k < 21, W.getD (S.getD k 0) 0 = at' 10 L (W.getD k 0) := by
  unfold cdSaK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, lenK_eq, ltK_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h4 := (recAll_iff (fun k => Nat.beq (W.getD (S.getD k 0) 0) (at' 10 L (W.getD k 0))) 21).1 h3
  exact ⟨h1, h2, fun k hk => Nat.eq_of_beq_eq_true (h4 k hk)⟩

theorem cdRedK_sound {TP : Nat → Nat} {W : List Nat} {L : Nat} {C S R : List Nat} {a e : Nat}
    (h : cdRedK TP W L C S R a e = true) :
    (∃ x < 693, cdImg TP W L a (cdImg TP W L a x) ≠ x) ∨
      ∃ b < 512, ∃ r ∈ R, a ^^^ b ^^^ amK C S b = r := by
  unfold cdRedK at h
  cases hb : bitK e 0
  · rw [hb, cond_false, Bool.and_eq_true, Bool.and_eq_true, memK_iff, Nat.beq_eq] at h
    obtain ⟨⟨-, hm⟩, he⟩ := h
    exact Or.inr ⟨Nat.mod (Nat.div e 2) 512, Nat.mod_lt _ (by omega), Nat.div (Nat.div e 2) 512,
      he ▸ hm, he⟩
  · rw [hb, cond_true, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
    exact Or.inl ⟨Nat.div e 2, h.1, Nat.ne_of_beq_eq_false h.2⟩

theorem cdRedAll_sound {TP : Nat → Nat} {W : List Nat} {L : Nat} {C S R : List Nat} :
    ∀ {RD : List Nat} {k : Nat}, cdRedAll TP W L C S R RD k = true →
      ∀ i < RD.length, cdRedK TP W L C S R (k + i) (RD.getD i 0) = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | e :: RD, k, h, i, hi => by
    have e' : cdRedAll TP W L C S R (e :: RD) k =
        (cdRedK TP W L C S R k e && cdRedAll TP W L C S R RD (k + 1)) := rfl
    rw [e', Bool.and_eq_true] at h
    cases i with
    | zero =>
      rw [Nat.add_zero, List.getD_cons_zero]
      exact h.1
    | succ i =>
      have h2 := cdRedAll_sound h.2 i (by simpa using hi)
      have e2 : k + (i + 1) = k + 1 + i := by omega
      rw [List.getD_cons_succ, e2]
      exact h2

theorem cdPlK_sound {TP : Nat → Nat} {W : List Nat} {L a : Nat} {PL : List (List Nat)}
    {PM : List Nat} {i i' : Nat} (h : cdPlK TP W L a PL PM i i' = true) :
    i < 891 ∧ i' < 891 ∧ ∀ x ∈ PL.getD i [], (PM.getD i' 0).testBit (cdImg TP W L a x) = true := by
  unfold cdPlK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, fun x hx => by rw [← bitK_eq]; exact h.2 x hx⟩

theorem cdPairs_vecs {TP : Nat → Nat} {W : List Nat} {L a : Nat} {PL : List (List Nat)}
    {PM WT : List Nat} : ∀ {ps : List Nat}, cdPairs TP W L a PL PM ps = true →
      ∀ v ∈ cdVecs WT ps, ∃ i i', cdPlK TP W L a PL PM i i' = true ∧
        v = WT.getD i' 0 ^^^ WT.getD i 0
  | [], _, v, hv => by simp [cdVecs] at hv
  | [_], h, _, _ => by simp [cdPairs] at h
  | i :: i' :: r, h, v, hv => by
    rw [cdPairs, Bool.and_eq_true] at h
    rw [cdVecs, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨i, i', h.1, rfl⟩
    · exact cdPairs_vecs h.2 v hv

theorem cdVecs_length (WT : List Nat) : ∀ ps : List Nat, (cdVecs WT ps).length = ps.length / 2
  | [] => by simp [cdVecs]
  | [_] => by simp [cdVecs]
  | i :: i' :: r => by
    rw [cdVecs, List.length_cons, cdVecs_length WT r, List.length_cons, List.length_cons]
    omega

theorem cdRepK_sound {TP : Nat → Nat} {W LT : List Nat} {PL : List (List Nat)} {PM WT : List Nat}
    {r : List Nat} (h : cdRepK TP W LT PL PM WT r = true) :
    (r.drop 5).length = 10 ∧
      cdPairs TP W (LT.getD (r.getD 0 0) 0) (r.getD 1 0) PL PM (r.drop 5) = true ∧
      indepOK (cdVecs WT (r.drop 5)) = true ∧
      (r.getD 2 0 = 0 → cdPlK TP W (LT.getD (r.getD 0 0) 0) (r.getD 1 0) PL PM (r.getD 3 0)
          (r.getD 4 0) = true ∧ fB (WT.getD (r.getD 4 0) 0) (WT.getD (r.getD 3 0) 0) = true) ∧
      (r.getD 2 0 = 1 → r.getD 3 0 < 891 ∧ ∀ x ∈ PL.getD (r.getD 3 0) [],
          cdImg TP W (LT.getD (r.getD 0 0) 0) (r.getD 1 0) x = x) ∧
      (r.getD 2 0 = 0 ∨ r.getD 2 0 = 1 ∨ r.getD 2 0 = 2) := by
  unfold cdRepK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenK_eq] at h
  obtain ⟨⟨⟨hlen, hpairs⟩, hind⟩, hcase⟩ := h
  refine ⟨hlen, hpairs, cdIndK_sound hind, fun ht => ?_, fun ht => ?_, ?_⟩
  · rw [ht, Nat.beq_refl, cond_true, Bool.and_eq_true, cdFB_eq] at hcase
    exact hcase
  · have e10 : Nat.beq 1 0 = false := rfl
    rw [ht, e10, cond_false, Nat.beq_refl, cond_true, Bool.and_eq_true, Nat.blt_eq,
      List.all_eq_true] at hcase
    exact ⟨hcase.1, fun x hx => Nat.eq_of_beq_eq_true (hcase.2 x hx)⟩
  · cases h0 : Nat.beq (r.getD 2 0) 0
    · cases h1 : Nat.beq (r.getD 2 0) 1
      · rw [h0, h1, cond_false, cond_false, Nat.beq_eq] at hcase
        exact Or.inr (Or.inr hcase)
      · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h1))
    · exact Or.inl (Nat.eq_of_beq_eq_true h0)

section Tables

open CFSG.Sporadic.Th.Native

theorem cd_toArray_get (l : List Nat) (i : Nat) : l.toArray[i]! = l.getD i 0 := by
  simp [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

theorem ptMapT_get {f : Nat → Nat} {PC : List Nat} {T : Nat} (hU : uPts () = PC.toArray)
    (hnd : PC.Nodup) (hlen : PC.length = 693) (hlt : ∀ c ∈ PC, c < 4096)
    (h : cdMapK f PC T = true) {p : Nat} (hp : p < 693) : (ptMapT f)[p]! = at' 10 T p := by
  obtain ⟨h1, h2⟩ := cdMapK_sound h p hp
  unfold ptMapT
  rw [getElem!_pos _ p (by simpa using hp), Array.getElem_ofFn]
  have e1 : (uPts ())[p]! = PC.getD p 0 := by rw [hU, cd_toArray_get]
  have hq : at' 10 T p < PC.length := by omega
  have e2 : PC.getD (at' 10 T p) 0 = PC[at' 10 T p] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
  have hc : PC[at' 10 T p] < 4096 := hlt _ (List.getElem_mem hq)
  change (uPos ())[normC (f (uPts ())[p]!)]! = _
  rw [e1, ← cdNorm_eq, ← h2, e2]
  unfold uPos
  rw [getElem!_pos _ _ (by simpa using hc), Array.getElem_ofFn, hU, List.toList_toArray]
  exact List.Nodup.idxOf_getElem hnd _ hq

theorem compTab_get (s t : Array Nat) {x : Nat} (hx : x < 693) : (compTab s t)[x]! = s[t[x]!]! := by
  unfold compTab
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem idTab_get {x : Nat} (hx : x < 693) : idTab[x]! = x := by
  unfold idTab
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem stabTab_get (T : Array Table) (g : Nat) {x : Nat} (hx : x < 693) :
    (stabTab T g)[x]! = stabAp T stabWords[g]! x := by
  unfold stabTab
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem candT_get (T : Array Table) (W0 s : Array Nat) (a : Nat) {x : Nat} (hx : x < 693) :
    (candT T W0 s a)[x]! = uaAp T W0 a 9 s[x]! := by
  unfold candT
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem uaAp_rec {T : Array Table} {W0 : Array Nat} {WL : List Nat} {TP : Nat → Nat}
    (hW : ∀ n < 9, W0[n]! = WL.getD n 0)
    (hT : ∀ n < 9, ∀ y < 693, ap T[WL.getD n 0]! y = at' 10 (TP (WL.getD n 0)) y ∧
      at' 10 (TP (WL.getD n 0)) y < 693) (a : Nat) : ∀ n ≤ 9, ∀ y < 693,
    uaAp T W0 a n y = Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
      (fun n ih y => ih (bif bitK a n then at' 10 (TP (WL.getD n 0)) y else y)) n y
  | 0, _, _, _ => rfl
  | n + 1, hn, y, hy => by
    have e : Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
        (fun n ih y => ih (bif bitK a n then at' 10 (TP (WL.getD n 0)) y else y)) (n + 1) y =
        Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
        (fun n ih y => ih (bif bitK a n then at' 10 (TP (WL.getD n 0)) y else y)) n
          (bif bitK a n then at' 10 (TP (WL.getD n 0)) y else y) := rfl
    rw [e, uaAp, bitK_eq, hW n (by omega)]
    cases a.testBit n
    · simp only [Bool.false_eq_true, ↓reduceIte, cond_false]
      exact uaAp_rec hW hT a n (by omega) y hy
    · simp only [↓reduceIte, cond_true]
      rw [(hT n (by omega) y hy).1]
      exact uaAp_rec hW hT a n (by omega) _ (hT n (by omega) y hy).2

theorem candT_cdImg {T : Array Table} {W0 s : Array Nat} {WL : List Nat} {TP : Nat → Nat}
    {L : Nat} (hW : ∀ n < 9, W0[n]! = WL.getD n 0)
    (hT : ∀ n < 9, ∀ y < 693, ap T[WL.getD n 0]! y = at' 10 (TP (WL.getD n 0)) y ∧
      at' 10 (TP (WL.getD n 0)) y < 693)
    (hs : ∀ x < 693, s[x]! = at' 10 L x ∧ at' 10 L x < 693) (a : Nat) {x : Nat} (hx : x < 693) :
    (candT T W0 s a)[x]! = cdImg TP WL L a x := by
  rw [candT_get _ _ _ _ hx, (hs x hx).1, uaAp_rec hW hT a 9 le_rfl _ (hs x hx).2]
  rfl

theorem invTab_loop {s : Array Nat} {B : Nat → Nat} (hs : ∀ x < 693, s[x]! < 693)
    (hinj : ∀ x < 693, ∀ x' < 693, s[x]! = s[x']! → x = x')
    (hB : ∀ y < 693, B y < 693 ∧ s[B y]! = y) : ∀ n ≤ 693,
    ((List.range n).foldl (fun r x => r.set! s[x]! x) (Array.replicate 693 0)).size = 693 ∧
      ∀ y < 693, ((List.range n).foldl (fun r x => r.set! s[x]! x)
        (Array.replicate 693 0))[y]! = if B y < n then B y else 0
  | 0, _ => ⟨by simp, fun y hy => by
      rw [if_neg (Nat.not_lt_zero _), List.range_zero, List.foldl_nil,
        getElem!_pos _ y (by rw [Array.size_replicate]; exact hy), Array.getElem_replicate]⟩
  | n + 1, hn => by
    obtain ⟨hsz, hget⟩ := invTab_loop hs hinj hB n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Array.set!_eq_setIfInBounds]
    refine ⟨by rw [Array.size_setIfInBounds, hsz], fun y hy => ?_⟩
    rw [getElem!_pos _ y (by rw [Array.size_setIfInBounds, hsz]; exact hy),
      Array.getElem_setIfInBounds (by rw [hsz]; exact hy)]
    by_cases hsy : s[n]! = y
    · rw [if_pos hsy]
      have e : B y = n := hinj _ (hB y hy).1 _ (by omega) (by rw [(hB y hy).2, hsy])
      rw [if_pos (by omega), e]
    · rw [if_neg hsy, ← getElem!_pos _ y (by rw [hsz]; exact hy), hget y hy]
      have hne : B y ≠ n := fun e => hsy (by rw [← e, (hB y hy).2])
      by_cases hlt : B y < n
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]

theorem invTab_get {s : Array Nat} {B : Nat → Nat} (hs : ∀ x < 693, s[x]! < 693)
    (hB : ∀ y < 693, B y < 693 ∧ s[B y]! = y) {y : Nat} (hy : y < 693) : (invTab s)[y]! = B y := by
  have hinj : ∀ x < 693, ∀ x' < 693, s[x]! = s[x']! → x = x' := by
    let F : Fin 693 → Fin 693 := fun x => ⟨s[x.val]!, hs x.val x.2⟩
    have hF : Function.Surjective F := fun y => ⟨⟨B y.val, (hB y.val y.2).1⟩,
      Fin.ext (hB y.val y.2).2⟩
    have hFi := Finite.injective_iff_surjective.2 hF
    intro x hx x' hx' he
    have := @hFi ⟨x, hx⟩ ⟨x', hx'⟩ (Fin.ext he)
    exact congrArg Fin.val this
  have h := (invTab_loop hs hinj hB 693 le_rfl).2 y hy
  rw [if_pos (hB y hy).1] at h
  exact h

theorem uaPos_get {W0 : Array Nat} {WL : List Nat} (hW : W0 = WL.toArray) (hnd : WL.Nodup)
    (hlen : WL.length = 21) {k : Nat} (hk : k < 21) : uaPos W0 (WL.getD k 0) = k := by
  have hp : ∀ j < 21, (W0[j]! == WL.getD k 0) = decide (j = k) := by
    intro j hj
    rw [hW, cd_toArray_get]
    have e : ∀ i (hi : i < 21), WL.getD i 0 = WL[i]'(by omega) := fun i hi => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [e j hj, e k hk]
    exact Bool.eq_iff_iff.2 (by
      rw [beq_iff_eq, decide_eq_true_iff]
      exact (hnd.getElem_inj_iff))
  have key : ∀ n ≤ 21, ((List.range n).find? fun j => W0[j]! == WL.getD k 0) =
      if k < n then some k else none := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.find?_append, ih (by omega), List.find?_singleton, hp n (by omega)]
      by_cases hkn : k < n
      · have h1 : k < n + 1 := by omega
        simp [hkn, h1]
      · by_cases e : n = k
        · subst e
          simp
        · have h1 : ¬ k < n + 1 := by omega
          simp [hkn, h1, e]
  unfold uaPos
  rw [key 21 le_rfl, if_pos hk]
  rfl

theorem sArrT_get {W0 s : Array Nat} {WL : List Nat} {L : Nat} {S : List Nat}
    (hW : W0 = WL.toArray) (hnd : WL.Nodup) (hlen : WL.length = 21)
    (hWl : ∀ w ∈ WL, w < 693) (hs : ∀ x < 693, s[x]! = at' 10 L x)
    (h : cdSaK WL L S = true) {k : Nat} (hk : k < 21) : (sArrT W0 s)[k]! = S.getD k 0 := by
  obtain ⟨hSl, hSlt, hS⟩ := cdSaK_sound h
  unfold sArrT
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  have hwk : WL.getD k 0 < 693 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hWl _ (List.getElem_mem _)
  have hSk : S.getD k 0 < 21 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hSlt _ (List.getElem_mem _)
  have e1 : W0[k]! = WL.getD k 0 := by rw [hW, cd_toArray_get]
  change uaPos W0 s[W0[k]!]! = _
  rw [e1, hs _ hwk, ← hS k hk, uaPos_get hW hnd hlen hSk]

theorem collAmatN_rec {s : Array Nat} {C S : List Nat} (hC : ∀ k, uaCo[k]! = C.getD k 0)
    (hs : ∀ j < 9, s[j]! = S.getD j 0) (a : Nat) : ∀ n ≤ 9, collAmatN s a n =
      Nat.rec (motive := fun _ => Nat) 0
        (fun j acc => Nat.xor acc (bif bitK a j then C.getD (S.getD j 0) 0 else 0)) n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [collAmatN, collAmatN_rec hC hs a n (by omega)]
    change _ = Nat.xor _ _
    rw [bitK_eq, hs n (by omega), hC]
    cases a.testBit n <;> rfl

theorem collAmat_amK {s : Array Nat} {C S : List Nat} (hC : ∀ k, uaCo[k]! = C.getD k 0)
    (hs : ∀ j < 9, s[j]! = S.getD j 0) (a : Nat) : collAmat s a = amK C S a :=
  collAmatN_rec hC hs a 9 le_rfl

end Tables

end CFSG.SmithE.K
