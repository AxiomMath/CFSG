module

public import CFSG.F3.ConjSpec

public section

namespace CFSG.F3.Native

open CFSG.Sporadic.Th.Native

theorem foldl_index (keys : Array (Array V))
    (hinj : ∀ i < keys.size, ∀ j < keys.size, keyOf keys[i]! = keyOf keys[j]! → i = j) (d : Nat) :
    ∀ n ≤ keys.size, ∀ k < n,
      ((List.range n).foldl (fun m i => m.insert (keyOf keys[i]!) i)
        (∅ : Std.HashMap (Array (Nat × Nat)) Nat)).getD (keyOf keys[k]!) d = k := by
  intro n
  induction n with
  | zero => intro _ k hk; omega
  | succ n ih =>
    intro hn k hk
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Std.HashMap.getD_insert]
    by_cases hkn : k = n
    · subst hkn
      simp
    · have hne : (keyOf keys[n]! == keyOf keys[k]!) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        exact hkn (hinj n (by omega) k (by omega) e).symm
      rw [hne]
      exact ih (by omega) k (by omega)

theorem indexOf_getD {keys : Array (Array V)}
    (hinj : ∀ i < keys.size, ∀ j < keys.size, keyOf keys[i]! = keyOf keys[j]! → i = j) {k : Nat}
    (hk : k < keys.size) : (indexOf keys).getD (keyOf keys[k]!) keys.size = k :=
  foldl_index keys hinj keys.size keys.size (Nat.le_refl _) k hk

theorem keyOf_inj {X Y : Array V} (h : keyOf X = keyOf Y) : X = Y := by
  unfold keyOf at h
  apply Array.ext
  · have := congrArg Array.size h
    simpa using this
  · intro i h1 h2
    have e := congrArg (fun a => a[i]?) h
    simp only [Array.getElem?_map, Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2,
      Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    generalize X[i] = a at e1 e2
    generalize Y[i] = b at e1 e2
    cases a
    cases b
    simp only at e1 e2
    rw [e1, e2]

theorem V.add_lt {d : Nat} {a b : V} (hap : a.p < 2 ^ d) (ham : a.m < 2 ^ d) (hbp : b.p < 2 ^ d)
    (hbm : b.m < 2 ^ d) : (a.add b).p < 2 ^ d ∧ (a.add b).m < 2 ^ d := by
  unfold V.add
  exact ⟨Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.xor_lt_two_pow hap (Nat.and_lt_two_pow _
      (Nat.or_lt_two_pow hbp hbm))) (Nat.xor_lt_two_pow hbp (Nat.and_lt_two_pow _
      (Nat.or_lt_two_pow hap ham)))) (Nat.and_lt_two_pow _ hbm),
    Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.xor_lt_two_pow ham (Nat.and_lt_two_pow _
      (Nat.or_lt_two_pow hbp hbm))) (Nat.xor_lt_two_pow hbm (Nat.and_lt_two_pow _
      (Nat.or_lt_two_pow hap ham)))) (Nat.and_lt_two_pow _ hbp)⟩

theorem comb_lt {d : Nat} {Y : Array V} (hY : ∀ j < d, Y[j]!.p < 2 ^ d ∧ Y[j]!.m < 2 ^ d) (r : V) :
    ∀ n ≤ d, (Nat.fold n (fun j _ acc => combStep Y r j acc) V.zero).p < 2 ^ d ∧
      (Nat.fold n (fun j _ acc => combStep Y r j acc) V.zero).m < 2 ^ d := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Nat.fold_zero]
    exact ⟨Nat.two_pow_pos d, Nat.two_pow_pos d⟩
  | succ n ih =>
    intro hn
    rw [Nat.fold_succ]
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨h3, h4⟩ := hY n (by omega)
    unfold combStep
    split_ifs
    · exact V.add_lt h1 h2 h3 h4
    · exact V.add_lt h1 h2 h4 h3
    · exact ⟨h1, h2⟩

theorem shiftRight_beq_zero {x d : Nat} (h : x < 2 ^ d) : (x >>> d == 0) = true := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]
  rfl

theorem lt_of_shiftRight {x d : Nat} (h : (x >>> d == 0) = true) : x < 2 ^ d := by
  rw [beq_iff_eq, Nat.shiftRight_eq_div_pow] at h
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos d)).1 h

theorem canonM_mul {d : Nat} {X Y : Array V} (hX : X.size = d) (hXw : RowsWF X)
    (hY : canonM d Y = true) : canonM d (mul d X Y) = true := by
  obtain ⟨hYs, hYc⟩ := canonM_spec hY
  have hYb : ∀ j < d, Y[j]!.p < 2 ^ d ∧ Y[j]!.m < 2 ^ d := by
    intro j hj
    have := hYc j (by omega)
    simp only [Bool.and_eq_true] at this
    exact ⟨lt_of_shiftRight this.1.2, lt_of_shiftRight this.2⟩
  unfold canonM
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  have hs : (mul d X Y).size = d := by unfold mul; rw [Array.size_map, hX]
  refine ⟨hs, fun i hi => ?_⟩
  have e := mul_getElem! (d := d) (X := X) (Y := Y) (i := i) (by rw [hX]; rwa [hs] at hi)
  rw [getElem!_pos _ i hi] at e
  rw [e]
  have hw := V.wf_comb d Y X[i]! (RowsWF.of_canonM hY) (hXw i)
  obtain ⟨h1, h2⟩ := comb_lt hYb X[i]! d (Nat.le_refl _)
  rw [← comb_eq_fold] at h1 h2
  simp only [hw, Bool.true_and, Bool.and_eq_true]
  exact ⟨shiftRight_beq_zero h1, shiftRight_beq_zero h2⟩

end CFSG.F3.Native

end
