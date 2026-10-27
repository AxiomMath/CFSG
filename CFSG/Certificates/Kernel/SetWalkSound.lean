module

public import Certificates.Data.Kernel.SetWalk
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Group.Nat.Defs

public section

namespace CFSG.KC.SetWalk

open CFSG.KC.Enum

@[expose] noncomputable def act (k w m G0 G1 : Nat) : List Bool → Nat → Nat
  | [], S => S
  | b :: l, S => pcomp k w m (bif b then G1 else G0) (act k w m G0 G1 l S)

@[expose] def SortStep (T SKT : Nat → Nat) (N j : Nat) : Prop :=
  skAt SKT j < N ∧ skAt SKT (j + 1) < N ∧ keyR T (skAt SKT j) < keyR T (skAt SKT (j + 1))

theorem act_append (k w m G0 G1 : Nat) (l l' : List Bool) (S : Nat) :
    act k w m G0 G1 (l ++ l') S = act k w m G0 G1 l (act k w m G0 G1 l' S) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.cons_append, act, ih]

section WalkSpec

variable {k w m wr mr R d NC G0 G1 : Nat} {T CS CP : Nat → Nat}

def WalkOK (k w m wr mr R d NC G0 G1 : Nat) (T CS CP : Nat → Nat) (a j S e : Nat) : Prop :=
  ∀ x, j ≤ x → x < e → (∃ l, keyR T x = keyS k w m wr mr R d (act k w m G0 G1 l S)) ∨
    ∃ c < NC, a ≤ CP c % 2 ^ 20 ∧ CP c / 2 ^ 20 ≤ e ∧ CP c % 2 ^ 20 ≤ x ∧ x < CP c / 2 ^ 20 ∧
      ∃ l, CS c = act k w m G0 G1 l S

theorem WalkOK.letter {a j S e : Nat} (b : Bool)
    (h : WalkOK k w m wr mr R d NC G0 G1 T CS CP a j (act k w m G0 G1 [b] S) e) :
    WalkOK k w m wr mr R d NC G0 G1 T CS CP a j S e := by
  intro x hx1 hx2
  rcases h x hx1 hx2 with ⟨l, hl⟩ | ⟨c, hc, h1, h2, h3, h4, l, hl⟩
  · exact Or.inl ⟨l ++ [b], by rw [hl, act_append]⟩
  · exact Or.inr ⟨c, hc, h1, h2, h3, h4, l ++ [b], by rw [hl, act_append]⟩

theorem cstep_spec {go : Nat → Nat → Nat}
    (hgo : ∀ j S' e', go j S' = e' → e' ≠ 0 →
      j < e' ∧ WalkOK k w m wr mr R d NC G0 G1 T CS CP j j S' e')
    {has S j e' : Nat} (b : Bool)
    (h : cstep k w m NC T CS CP go has (bif b then G1 else G0) S j = e') (he : e' ≠ 0) :
    j ≠ 0 ∧ j ≤ e' ∧ WalkOK k w m wr mr R d NC G0 G1 T CS CP j j S e' := by
  unfold cstep at h
  simp only [CFSG.KS.PK.strictN_eq, CFSG.KS.PK.nIf_eq, CFSG.KS.PK.bAnd_eq] at h
  split_ifs at h with h1 h2 h3 h4
  · subst h
    exact ⟨he, le_rfl, fun x hx1 hx2 => absurd hx2 (by omega)⟩
  · exact absurd h.symm he
  · obtain ⟨hlt, hW⟩ := hgo _ _ _ h he
    exact ⟨fun hj0 => h2 (by rw [hj0]; rfl), le_of_lt hlt, WalkOK.letter b hW⟩
  · simp only [Bool.and_eq_true] at h4
    obtain ⟨hc, hp, hj, hs⟩ := h4
    have e1 : Nat.land (CP (Nat.land (Nat.shiftRight (rd T j) 3) 127)) 1048575 =
        CP (Nat.land (Nat.shiftRight (rd T j) 3) 127) % 2 ^ 20 :=
      Nat.and_two_pow_sub_one_eq_mod _ 20
    have e2 : Nat.shiftRight (CP (Nat.land (Nat.shiftRight (rd T j) 3) 127)) 20 =
        CP (Nat.land (Nat.shiftRight (rd T j) 3) 127) / 2 ^ 20 :=
      Nat.shiftRight_eq_div_pow _ _
    have hp' := Nat.eq_of_beq_eq_true hp
    have hj' := Nat.blt_eq.mp hj
    rw [e1] at hp'
    rw [e2] at hj' h
    refine ⟨fun hj0 => h2 (by rw [hj0]; rfl), by omega, fun x hx1 hx2 => Or.inr ⟨_, Nat.blt_eq.mp hc, by omega, by omega,
      by omega, by omega, [b], Nat.eq_of_beq_eq_true hs⟩⟩
  · exact absurd h.symm he

theorem walk_succ (D i S : Nat) : walk k w m wr mr R d NC G0 G1 T CS CP (D + 1) i S =
    if Nat.beq (keyS k w m wr mr R d S) (keyR T i) = true then
      cstep k w m NC T CS CP (walk k w m wr mr R d NC G0 G1 T CS CP D)
        (Nat.land (Nat.shiftRight (rd T i) 1) 1) (bif true then G1 else G0) S
        (cstep k w m NC T CS CP (walk k w m wr mr R d NC G0 G1 T CS CP D)
          (Nat.land (rd T i) 1) (bif false then G1 else G0) S (i + 1))
    else 0 := by
  have e : walk k w m wr mr R d NC G0 G1 T CS CP (D + 1) i S = strictN (rd T i) fun r =>
      nIf(Nat.beq (keyS k w m wr mr R d S) (Nat.shiftRight r (nat_lit 16)),
        cstep k w m NC T CS CP (walk k w m wr mr R d NC G0 G1 T CS CP D)
          (Nat.land (Nat.shiftRight r (nat_lit 1)) (nat_lit 1)) G1 S
          (cstep k w m NC T CS CP (walk k w m wr mr R d NC G0 G1 T CS CP D)
            (Nat.land r (nat_lit 1)) G0 S (Nat.succ i)),
        nat_lit 0) := rfl
  rw [e, CFSG.KS.PK.strictN_eq]
  exact CFSG.KS.PK.nIf_eq _ _ _

theorem walk_spec : ∀ D i S e, walk k w m wr mr R d NC G0 G1 T CS CP D i S = e → e ≠ 0 →
    i < e ∧ WalkOK k w m wr mr R d NC G0 G1 T CS CP (i + 1) i S e := by
  intro D
  induction D with
  | zero =>
    intro i S e h he
    exact absurd h.symm he
  | succ D ih =>
    intro i S e h he
    rw [walk_succ] at h
    split_ifs at h with hk
    · have hk' : keyR T i = keyS k w m wr mr R d (act k w m G0 G1 [] S) :=
        (Nat.eq_of_beq_eq_true hk).symm
      have ih' : ∀ j S' e', walk k w m wr mr R d NC G0 G1 T CS CP D j S' = e' → e' ≠ 0 →
          j < e' ∧ WalkOK k w m wr mr R d NC G0 G1 T CS CP j j S' e' := by
        intro j S' e' h1 h2
        obtain ⟨h3, h4⟩ := ih j S' e' h1 h2
        refine ⟨h3, fun x hx1 hx2 => ?_⟩
        rcases h4 x hx1 hx2 with h5 | ⟨c, hc, h5, h6⟩
        · exact Or.inl h5
        · exact Or.inr ⟨c, hc, by omega, h6⟩
      obtain ⟨hj2, hle2, hW2⟩ := cstep_spec ih' true h he
      obtain ⟨-, hle1, hW1⟩ := cstep_spec ih' false rfl hj2
      refine ⟨by omega, fun x hx1 hx2 => ?_⟩
      rcases Nat.lt_or_ge x (i + 1) with hx | hx
      · have hxi : x = i := by omega
        subst hxi
        exact Or.inl ⟨[], hk'⟩
      rcases Nat.lt_or_ge x (cstep k w m NC T CS CP (walk k w m wr mr R d NC G0 G1 T CS CP D)
          (Nat.land (rd T i) 1) (bif false then G1 else G0) S (i + 1)) with hx' | hx'
      · rcases hW1 x hx hx' with h1 | ⟨c, hc, h1, h2, h3, h4, h5⟩
        · exact Or.inl h1
        · exact Or.inr ⟨c, hc, h1, by omega, h3, h4, h5⟩
      · rcases hW2 x hx' hx2 with h1 | ⟨c, hc, h1, h2, h3, h4, h5⟩
        · exact Or.inl h1
        · exact Or.inr ⟨c, hc, by omega, h2, h3, h4, h5⟩
    · exact absurd h.symm he

end WalkSpec

theorem walk_sound {k w m wr mr R d NC G0 G1 N D : Nat} {T CS CP : Nat → Nat}
    (h : ∀ c < NC, chunkOK k w m wr mr R d NC G0 G1 N D T CS CP c = true) :
    ∀ c < NC, ∀ i, CP c % 2 ^ 20 ≤ i → i < CP c / 2 ^ 20 →
      ∃ l : List Bool, keyR T i = keyS k w m wr mr R d (act k w m G0 G1 l (CS c)) := by
  suffices H : ∀ n, ∀ c < NC, CP c / 2 ^ 20 - CP c % 2 ^ 20 ≤ n → ∀ i, CP c % 2 ^ 20 ≤ i →
      i < CP c / 2 ^ 20 →
      ∃ l : List Bool, keyR T i = keyS k w m wr mr R d (act k w m G0 G1 l (CS c)) from
    fun c hc => H _ c hc le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro c hc hn i hi1 hi2
  have hck := h c hc
  unfold chunkOK at hck
  simp only [CFSG.KS.PK.strictB_eq, CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at hck
  obtain ⟨-, -, -, hw⟩ := hck
  have hw' := Nat.eq_of_beq_eq_true hw
  have e1 : Nat.land (CP c) 1048575 = CP c % 2 ^ 20 := Nat.and_two_pow_sub_one_eq_mod _ 20
  have e2 : Nat.shiftRight (CP c) 20 = CP c / 2 ^ 20 := Nat.shiftRight_eq_div_pow _ _
  rw [e1, e2] at hw'
  obtain ⟨-, hW⟩ := walk_spec D _ _ _ hw' (by omega)
  rcases hW i hi1 hi2 with h1 | ⟨c', hc', h1, h2, h3, h4, l, hl⟩
  · exact h1
  · obtain ⟨l', hl'⟩ := IH (CP c' / 2 ^ 20 - CP c' % 2 ^ 20) (by omega) c' hc' le_rfl i h3 h4
    exact ⟨l' ++ l, by rw [hl', hl, act_append]⟩

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem sortOK_spec {T SKT : Nat → Nat} {N lo len : Nat} (h : sortOK T SKT N lo len = true) :
    ∀ t < len, SortStep T SKT N (lo + t) := by
  intro t ht
  have h1 := CFSG.KS.allN_spec h t ht
  simp only [strictB_eq'] at h1
  obtain ⟨ha, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h1
  obtain ⟨hb, hk⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
  exact ⟨Nat.blt_eq.mp ha, Nat.blt_eq.mp hb, Nat.blt_eq.mp hk⟩

theorem setMask_testBit {k w m S q : Nat} (h : (setMask k w m S).testBit q = true) :
    ∃ j < k, q = Nat.land (Nat.shiftRight S (w * j)) m := by
  have key : ∀ L : List Nat, (L.foldr (fun i acc =>
      Nat.lor acc (Nat.shiftLeft (nat_lit 1) fld(S, Nat.mul w i, m))) (nat_lit 0)).testBit q = true →
      ∃ j ∈ L, q = Nat.land (Nat.shiftRight S (w * j)) m := by
    intro L
    induction L with
    | nil =>
      intro h
      change Nat.testBit 0 q = true at h
      simp at h
    | cons j L ih =>
      intro h
      change (Nat.testBit (L.foldr (fun i acc =>
        Nat.lor acc (Nat.shiftLeft (nat_lit 1) fld(S, Nat.mul w i, m))) (nat_lit 0) |||
          1 <<< (S >>> (w * j) &&& m)) q) = true at h
      rw [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow] at h
      rcases h with h | h
      · obtain ⟨j', hj', e⟩ := ih h
        exact ⟨j', List.mem_cons_of_mem _ hj', e⟩
      · exact ⟨j, List.mem_cons_self, (of_decide_eq_true h).symm⟩
  unfold setMask at h
  rw [CFSG.KS.PK.foldN_eq] at h
  obtain ⟨j, hj, e⟩ := key _ h
  exact ⟨j, List.mem_range.1 hj, e⟩

theorem fixOK_spec {k w m G S : Nat} (h : fixOK k w m G S = true) :
    ∀ i < k, ∃ j < k, pg w m G (Nat.land (Nat.shiftRight S (w * i)) m) =
      Nat.land (Nat.shiftRight S (w * j)) m := by
  intro i hi
  unfold fixOK at h
  rw [strictB_eq'] at h
  have h2 := Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h i hi)
  have hb : (setMask k w m S).testBit (pg w m G fld(S, Nat.mul w i, m)) = true := by
    change (setMask k w m S >>> pg w m G fld(S, Nat.mul w i, m)) &&& 1 = 1 at h2
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow] at h2
    rw [Nat.testBit_eq_decide_div_mod_eq, h2]
    rfl
  exact setMask_testBit hb

theorem listK_spec {w m : Nat} {l : List Nat} {S : Nat} (h : listK w m l S = true) :
    (∀ i < l.length, Nat.land (Nat.shiftRight S (w * i)) m = l[i]!) ∧
      Nat.shiftRight S (w * l.length) = 0 := by
  induction l generalizing S with
  | nil =>
    have h' : Nat.beq S 0 = true := h
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    rw [Nat.eq_of_beq_eq_true h']
    exact Nat.zero_shiftRight _
  | cons a l ih =>
    have h' : Bool.rec (motive := fun _ => Bool) false (listK w m l (Nat.shiftRight S w))
        (Nat.beq (Nat.land S m) a) = true := h
    obtain ⟨ha, hl⟩ := (CFSG.KS.bAnd_iff _ _).1 h'
    obtain ⟨ih1, ih2⟩ := ih hl
    have hsh : ∀ i, Nat.shiftRight S (w * (i + 1)) =
        Nat.shiftRight (Nat.shiftRight S w) (w * i) := by
      intro i
      change S >>> (w * (i + 1)) = S >>> w >>> (w * i)
      rw [← Nat.shiftRight_add, Nat.mul_succ, Nat.add_comm]
    refine ⟨fun i hi => ?_, ?_⟩
    · cases i with
      | zero =>
        have e0 : Nat.shiftRight S (w * 0) = S := by
          rw [Nat.mul_zero]
          rfl
        rw [e0, Nat.eq_of_beq_eq_true ha]
        simp
      | succ i =>
        rw [hsh, ih1 i (by simp only [List.length_cons] at hi; omega)]
        simp
    · rw [List.length_cons, hsh]
      exact ih2

theorem inj_of_sorted {T SKT : Nat → Nat} {N : Nat} (h : ∀ j, j + 1 < N → SortStep T SKT N j) :
    ∀ a < N, ∀ b < N, keyR T a = keyR T b → a = b := by
  set s := skAt SKT with hs
  have hmono : ∀ i j, i < j → j < N → keyR T (s i) < keyR T (s j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have hstep := (h j hj).2.2
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij' | rfl
      · exact lt_trans (ih hij' (by omega)) hstep
      · exact hstep
  intro a ha b hb hab
  by_cases hN : N ≤ 1
  · omega
  have hlt : ∀ i < N, s i < N := by
    intro i hi
    by_cases hi' : i + 1 < N
    · exact (h i hi').1
    · have e : i = (N - 2) + 1 := by omega
      rw [e]
      exact (h (N - 2) (by omega)).2.1
  have hkey : ∀ i < N, ∀ j < N, keyR T (s i) = keyR T (s j) → i = j := by
    intro i hi j hj e
    rcases lt_trichotomy i j with hij | hij | hij
    · exact absurd e (ne_of_lt (hmono i j hij hj))
    · exact hij
    · exact absurd e.symm (ne_of_lt (hmono j i hij hi))
  have hinj : Set.InjOn s (Finset.range N : Set Nat) := by
    intro i hi j hj e
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hkey i hi j hj (by rw [e])
  have hsub : (Finset.range N).image s ⊆ Finset.range N := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (hlt i (Finset.mem_range.1 hi))
  have heq : (Finset.range N).image s = Finset.range N :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj])
  have ha' : a ∈ (Finset.range N).image s := by rw [heq]; exact Finset.mem_range.2 ha
  have hb' : b ∈ (Finset.range N).image s := by rw [heq]; exact Finset.mem_range.2 hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hb'
  rw [hkey i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hab]

end CFSG.KC.SetWalk

end
