module

public import CFSG.Monster.Existence.TwoPoint.ThetaTrace
public import CFSG.Certificates.Kernel.Trace6091.Tabs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.Trace6091

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Visible
  CFSG.Monster.Griess CFSG.Monster.AxisCount CFSG.Monster.Existence CFSG.Monster.B.Rep4371 Finset

@[expose] def xTerm (arr : Array ℕ) (a u : ℕ) : ℤ :=
  if Model.permCN arr a = a ∧ Model.permDN arr u = u then Model.sgnI (Model.kappaN arr a) else 0

theorem packN_lt (f : ℕ → Bool) : ∀ n, Model.packN f n < 2 ^ n
  | 0 => by simp [Model.packN]
  | n + 1 => by
    simp only [Model.packN]
    refine Nat.or_lt_two_pow (lt_trans (packN_lt f n)
      (Nat.pow_lt_pow_right (by norm_num) (by omega))) ?_
    split_ifs
    · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · positivity

theorem dualN_lt (v : ℕ) : Model.dualN v < 4096 := packN_lt _ 12

theorem thetaRec_lt (a : ℕ) : ∀ n, Model.thetaRec n a < 4096
  | 0 => by simp [Model.thetaRec]
  | n + 1 => by
    simp only [Model.thetaRec]
    split_ifs
    · exact Nat.xor_lt_two_pow (n := 12)
        (Nat.xor_lt_two_pow (n := 12) (thetaRec_lt a n) (packN_lt _ 12)) (dualN_lt _)
    · exact thetaRec_lt a n

theorem thetaN_lt (a : ℕ) : Model.thetaN a < 4096 := thetaRec_lt a 12

theorem permCN_lt' (arr : Array ℕ) (a : ℕ) : Model.permCN arr a < 4096 := packN_lt _ 12

theorem xor_eq_iff (x y d : ℕ) : x ^^^ y = d ↔ y = x ^^^ d := by
  constructor
  · intro h
    rw [← h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · intro h
    rw [h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem xor_xor_cancel (x y : ℕ) : x ^^^ (x ^^^ y) = y := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem toSC_eq_of_pauliQ {x y : Model.Pauli} (h : pauliQ x = pauliQ y) : toSC x = toSC y := by
  have h' : spinEquiv (toSC x) = spinEquiv (toSC y) := h
  exact spinEquiv.injective h'

theorem sum_range_mul (f : ℕ → ℤ) (k : ℕ) : ∀ n,
    ∑ x ∈ range (n * k), f x = ∑ t ∈ range n, ∑ i ∈ range k, f (t * k + i)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.add_mul, Nat.one_mul, sum_range_add f (n * k) k, sum_range_mul f k n, sum_range_succ]

@[expose] def pairD (q : ℕ) : ℕ :=
  Model.dualN (2 ^ ((Native.pairTab ())[q]!).1 ||| 2 ^ ((Native.pairTab ())[q]!).2)

private theorem conjPermN_s (arr : Array ℕ) (a d : ℕ) :
    (Model.conjPermN arr (false, a, d)).1 = Model.kappaN arr a :=
  Bool.false_xor (Model.kappaN arr a)

private theorem coordS {y z : Model.Pauli} (h : toSC y = toSC z) : y.1 = z.1 :=
  boolZ_injective (congrArg SpinCoord.s h)

private theorem coordA {y z : Model.Pauli} (h : toSC y = toSC z) : toC y.2.1 = toC z.2.1 :=
  congrArg SpinCoord.a h

private theorem coordD {y z : Model.Pauli} (h : toSC y = toSC z) : toD y.2.2 = toD z.2.2 :=
  congrArg SpinCoord.δ h

private theorem conjPermN_a (arr : Array ℕ) (a d : ℕ) :
    (Model.conjPermN arr (false, a, d)).2.1 = Model.permCN arr a := rfl

private theorem conjPermN_d (arr : Array ℕ) (a d : ℕ) :
    (Model.conjPermN arr (false, a, d)).2.2 =
      Model.thetaN (Model.permCN arr a) ^^^ Model.permDN arr (Model.thetaN a ^^^ d) := rfl


theorem fixTerm_perm (arr : Array ℕ) (hv : Native.permValid arr = true) (p : ℕ) (hp : p < 98280) :
    (if tgtPos (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) p = p then
      sgPos (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) p else 0) =
      xTerm arr (keyOf p).1 (Model.thetaN (keyOf p).1 ^^^ (keyOf p).2) := by
  have hg := gdSpec_perm arr (permOf arr) (permOf_spec hv)
  generalize hgdef : Native.GD.ofGen (Native.mkCtx ()) (.perm arr) = g at hg ⊢
  have hk := keyOf_lt p hp
  have hsh' : (shortOf ⟨p, hp⟩).1 = (toC (keyOf p).1, toD (keyOf p).2) := rfl
  generalize hkdef : keyOf p = k at hk hsh' ⊢
  have hy : yKey g p = Native.fastAct g.tT g.tD (false, k.1, k.2) := by rw [yKey, hkdef]
  have h1 : pauliQ (yKey g p) = pauliQ (Model.conjPermN arr (false, k.1, k.2)) := by
    rw [hy]
    exact (hg.conj (false, k.1, k.2)).symm.trans (conjQ_perm_toQ (permOf arr) (permOf_spec hv) _)
  have h2 := toSC_eq_of_pauliQ h1
  have hs : (yKey g p).1 = Model.kappaN arr k.1 := (coordS h2).trans (conjPermN_s arr k.1 k.2)
  have ha : toC (yKey g p).2.1 = toC (Model.permCN arr k.1) :=
    (coordA h2).trans (by rw [conjPermN_a])
  have hd : toD (yKey g p).2.2 =
      toD (Model.thetaN (Model.permCN arr k.1) ^^^ Model.permDN arr (Model.thetaN k.1 ^^^ k.2)) :=
    (coordD h2).trans (by rw [conjPermN_d])
  obtain ⟨hsh, -⟩ := thetaX_shortOf (permPairOf (permOf arr)) g hg.conj ⟨p, hp⟩
  have htgt : tgtPos g p = posOf ⟨(toC (yKey g p).2.1, toD (yKey g p).2.2), hsh⟩ :=
    find_eq_posOf _ _ hsh
  have hpos : posOf (shortOf ⟨p, hp⟩) = p := posOf_shortOf ⟨p, hp⟩
  have hdlt : Model.thetaN (Model.permCN arr k.1) ^^^ Model.permDN arr (Model.thetaN k.1 ^^^ k.2) <
      4096 := Nat.xor_lt_two_pow (n := 12) (thetaN_lt _) (dualN_lt _)
  have hfix : tgtPos g p = p ↔ Model.permCN arr k.1 = k.1 ∧
      Model.thetaN (Model.permCN arr k.1) ^^^ Model.permDN arr (Model.thetaN k.1 ^^^ k.2) = k.2 := by
    rw [htgt]
    constructor
    · intro h
      have e := congrArg Subtype.val (posOf_inj (h.trans hpos.symm))
      change (toC (yKey g p).2.1, toD (yKey g p).2.2) = (shortOf ⟨p, hp⟩).1 at e
      rw [hsh', Prod.mk.injEq, ha, hd] at e
      exact ⟨toC_inj (permCN_lt' _ _) hk.1 e.1, toD_inj hdlt hk.2 e.2⟩
    · rintro ⟨e1, e2⟩
      have e : (⟨(toC (yKey g p).2.1, toD (yKey g p).2.2), hsh⟩ : ShortIdx) = shortOf ⟨p, hp⟩ := by
        apply Subtype.ext
        change (toC (yKey g p).2.1, toD (yKey g p).2.2) = (shortOf ⟨p, hp⟩).1
        rw [hsh', ha, hd, e2, e1]
      rw [e]
      exact hpos
  have hfix' : tgtPos g p = p ↔ Model.permCN arr k.1 = k.1 ∧
      Model.permDN arr (Model.thetaN k.1 ^^^ k.2) = Model.thetaN k.1 ^^^ k.2 := by
    rw [hfix]
    constructor
    · rintro ⟨e1, e2⟩
      rw [e1, xor_eq_iff] at e2
      exact ⟨e1, e2⟩
    · rintro ⟨e1, e2⟩
      rw [e1, xor_eq_iff]
      exact ⟨rfl, e2⟩
  have hsg : sgPos g p = Model.sgnI (Model.kappaN arr k.1) := congrArg Model.sgnI hs
  unfold xTerm
  by_cases h : tgtPos g p = p
  · rw [ite_eq_left h, ite_eq_left (hfix'.1 h), hsg]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hfix'.2 h'))]

theorem xTrC_perm_keys (arr : Array ℕ) (hv : Native.permValid arr = true) :
    xTrC (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) =
      ∑ p ∈ range 98280, xTerm arr (keyOf p).1 (Model.thetaN (keyOf p).1 ^^^ (keyOf p).2) := by
  rw [xTrC_eq]
  exact sum_congr rfl fun p hp => fixTerm_perm arr hv p (mem_range.1 hp)

theorem xTrC_perm_blocks (arr : Array ℕ) (hv : Native.permValid arr = true) :
    xTrC (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) =
      (∑ q ∈ range 276,
          (xTerm arr 0 (Model.thetaN 0 ^^^ pairD q) + xTerm arr 63 (Model.thetaN 63 ^^^ pairD q))) +
        (∑ t ∈ range 2048, ∑ i ∈ range 24,
          xTerm arr (Model.oddCode (2 * t) i) (Model.dualN (2 ^ i))) +
        (∑ o ∈ range 759, ∑ m ∈ range 64,
          xTerm arr (Native.octCodeG (KDense.octT o) (KDense.evenT m))
            (Model.dualN (Native.spreadG (Model.wordN (KDense.octT o)) (KDense.evenT m)))) := by
  rw [xTrC_perm_keys arr hv, (rfl : (98280 : ℕ) = 276 * 2 + 2048 * 24 + 759 * 64),
    sum_range_add _ (276 * 2 + 2048 * 24) (759 * 64), sum_range_add _ (276 * 2) (2048 * 24),
    sum_range_mul _ 2 276, sum_range_mul _ 24 2048, sum_range_mul _ 64 759]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · refine sum_congr rfl fun q hq => ?_
    rw [sum_range_succ, sum_range_succ, sum_range_zero, zero_add]
    have e0 : (q * 2 + 0) / 2 = q := by omega
    have e1 : (q * 2 + 1) / 2 = q := by omega
    have f0 : (q * 2 + 0) % 2 = 0 := by omega
    have f1 : ¬ (q * 2 + 1) % 2 = 0 := by omega
    have hq := mem_range.1 hq
    rw [keyOf_pair (q * 2 + 0) (by omega), keyOf_pair (q * 2 + 1) (by omega), e0, e1,
      ite_eq_left f0, ite_eq_right f1]
    rfl
  · refine sum_congr rfl fun t ht => sum_congr rfl fun i hi => ?_
    have ht := mem_range.1 ht
    have hi := mem_range.1 hi
    have e1 : (276 * 2 + (t * 24 + i) - 552) / 24 = t := by omega
    have e2 : (276 * 2 + (t * 24 + i) - 552) % 24 = i := by omega
    rw [keyOf_odd (276 * 2 + (t * 24 + i)) (by omega) (by omega), e1, e2]
    dsimp only
    rw [xor_xor_cancel]
  · refine sum_congr rfl fun o ho => sum_congr rfl fun m hm => ?_
    have ho := mem_range.1 ho
    have hm := mem_range.1 hm
    have e1 : (276 * 2 + 2048 * 24 + (o * 64 + m) - 49704) / 64 = o := by omega
    have e2 : (276 * 2 + 2048 * 24 + (o * 64 + m) - 49704) % 64 = m := by omega
    rw [keyOf_oct (276 * 2 + 2048 * 24 + (o * 64 + m)) (by omega) (by omega), e1, e2]
    dsimp only
    rw [xor_xor_cancel, octTab_get o ho, evenTab_get m hm]

end CFSG.KC.Trace6091

end
