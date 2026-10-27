module

public import Certificates.Data.D4HexF48Check
public import CFSG.Certificates.Kernel.S63K.OrbRunSound
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.KC.S63K

open CFSG.D4Hex CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def tSig (F : Array (Array ℕ)) (r : OrbRec) (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => k
  | f + 1, i => if i = 0 then k else (F[r.lab[i]!]!)[tSig F r k f r.par[i]!]!

structure TRec (r : OrbRec) (p0 : ℕ) : Prop where
  lt : ∀ i < 512, r.ord[i]! < 819
  inj : ∀ i < 512, ∀ j < 512, r.ord[i]! = r.ord[j]! → i = j
  par : ∀ i, 0 < i → i < 512 → r.par[i]! < i
  root : r.ord[0]! = p0

variable {F : Array (Array ℕ)} {r : OrbRec} {p0 k : ℕ}

theorem tSig_add (f i : ℕ) :
    tSig F r k (f + 1) i = if i = 0 then k else (F[r.lab[i]!]!)[tSig F r k f r.par[i]!]! := rfl

theorem tSig_stable (h : TRec r p0) :
    ∀ i < 512, ∀ f f', i < f → i < f' → tSig F r k f i = tSig F r k f' i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi f f' hf hf'
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨f', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    rw [tSig_add, tSig_add]
    by_cases h0 : i = 0
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0]
      have hp := h.par i (by omega) hi
      rw [ih _ hp (by omega) f f' (by omega) (by omega)]

theorem tSig_succ (h : TRec r p0) {i : ℕ} (hi : i < 512) (h0 : i ≠ 0) :
    tSig F r k 512 i = (F[r.lab[i]!]!)[tSig F r k 512 r.par[i]!]! := by
  have e : tSig F r k 512 i = (F[r.lab[i]!]!)[tSig F r k 511 r.par[i]!]! := by
    rw [tSig_add 511 i, if_neg h0]
  have hp := h.par i (by omega) hi
  rw [e, tSig_stable h _ (by omega) 511 512 (by omega) (by omega)]

@[expose] def tStep (F : Array (Array ℕ)) (r : OrbRec) (a : Array ℕ) (i : ℕ) : Array ℕ :=
  a.set! r.ord[i]! ((F[r.lab[i]!]!)[a[r.ord[r.par[i]!]!]!]!)

theorem f48TArr_eq (F : Array (Array ℕ)) (r : OrbRec) (p0 k : ℕ) :
    f48TArr F r p0 k = (List.range' 1 511).foldl (tStep F r) ((idA 819).set! p0 k) := by
  unfold f48TArr
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run]
  exact forIn_yield (tStep F r) _ (fun _ _ => rfl) _ _

@[expose] def TInv (F : Array (Array ℕ)) (r : OrbRec) (k c : ℕ) (a : Array ℕ) : Prop :=
  a.size = 819 ∧ (∀ i < c, a[r.ord[i]!]! = tSig F r k 512 i) ∧
    ∀ p < 819, (∀ i < c, r.ord[i]! ≠ p) → a[p]! = p

theorem tInv_fold (h : TRec r p0) (hp0 : p0 < 819) :
    ∀ n ≤ 511, TInv F r k (n + 1) ((List.range' 1 n).foldl (tStep F r) ((idA 819).set! p0 k))
  | 0, _ => by
    refine ⟨by simp [idA], fun i hi => ?_, fun p hp hn => ?_⟩
    · obtain rfl : i = 0 := by omega
      rw [List.range'_zero, List.foldl_nil, h.root,
        get_set _ _ (by simp [idA, hp0]), if_pos rfl, tSig_add 511 0, if_pos rfl]
    · rw [List.range'_zero, List.foldl_nil, get_set _ _ (by simp [idA, hp]),
        if_neg (by have := hn 0 (by omega); rw [h.root] at this; exact Ne.symm this),
        idA_get hp]
  | n + 1, hn => by
    obtain ⟨hs, hv, hf⟩ := tInv_fold h hp0 n (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range' 1 n).foldl (tStep F r) ((idA 819).set! p0 k) = a at hs hv hf
    have hc : 1 + 1 * n = n + 1 := by omega
    rw [hc]
    have hpar := h.par (n + 1) (by omega) (by omega)
    have hval : (F[r.lab[n + 1]!]!)[a[r.ord[r.par[n + 1]!]!]!]! = tSig F r k 512 (n + 1) := by
      rw [hv _ hpar, tSig_succ h (i := n + 1) (by omega) (by omega)]
    unfold tStep
    rw [hval]
    refine ⟨by simp [hs], fun i hi => ?_, fun p hp hn' => ?_⟩
    · rw [get_set _ _ (by rw [hs]; exact h.lt i (by omega))]
      by_cases e : i = n + 1
      · rw [if_pos (by rw [e]), e]
      · rw [if_neg (fun he => e (h.inj i (by omega) (n + 1) (by omega) he)), hv i (by omega)]
    · rw [get_set _ _ (by rw [hs]; exact hp), if_neg (Ne.symm (hn' (n + 1) (by omega)))]
      exact hf p hp fun i hi => hn' i (by omega)

theorem tArr_spec (h : TRec r p0) (hp0 : p0 < 819) :
    (f48TArr F r p0 k).size = 819 ∧
      (∀ i < 512, (f48TArr F r p0 k)[r.ord[i]!]! = tSig F r k 512 i) ∧
      ∀ p < 819, (∀ i < 512, r.ord[i]! ≠ p) → (f48TArr F r p0 k)[p]! = p := by
  rw [f48TArr_eq]
  exact tInv_fold h hp0 511 le_rfl

theorem beq_true_nat {a b : ℕ} (e : a = b) : (a == b) = true := beq_iff_eq.2 e

theorem candOK (lay : Array ℕ) (h : TRec r p0) (hp0 : p0 < 819)
    (hlay : ∀ i < 512, ¬ lay[r.ord[i]!]! ≤ 4) :
    f48CandOK lay F r p0 (f48TArr F r p0 k) k = true := by
  obtain ⟨-, hv, hf⟩ := tArr_spec (F := F) (k := k) h hp0
  unfold f48CandOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨beq_true_nat ?_, allLt_iff.2 fun p hp => ?_⟩, allLt_iff.2 fun i hi => ?_⟩
  · have e0 := hv 0 (by omega)
    rw [h.root, tSig_add 511 0, if_pos rfl] at e0
    exact e0
  · by_cases hl : 4 < lay[p]!
    · simp [hl]
    · have hn : ∀ i < 512, r.ord[i]! ≠ p := fun i hi e => hlay i hi (by rw [e]; omega)
      simp [hf p hp hn]
  · by_cases h0 : i = 0
    · simp [h0]
    · have hpar := h.par i (by omega) hi
      rw [hv i hi, hv _ (by omega), tSig_succ h hi h0]
      simp

theorem tArr_id (h : TRec r p0) (hp0 : p0 < 819)
    (ht : ∀ i, 0 < i → i < 512 → (F[r.lab[i]!]!)[r.ord[r.par[i]!]!]! = r.ord[i]!) :
    eqA 819 (f48TArr F r p0 p0) (idA 819) = true := by
  obtain ⟨-, hv, hf⟩ := tArr_spec (F := F) (k := p0) h hp0
  have hs : ∀ i < 512, tSig F r p0 512 i = r.ord[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases h0 : i = 0
      · subst h0
        rw [h.root, tSig_add 511 0, if_pos rfl]
      · have hpar := h.par i (by omega) hi
        rw [tSig_succ h hi h0, ih _ hpar (by omega), ht i (by omega) hi]
  unfold eqA
  refine allLt_iff.2 fun p hp => ?_
  rw [idA_get hp]
  by_cases hm : ∃ i < 512, r.ord[i]! = p
  · obtain ⟨i, hi, rfl⟩ := hm
    rw [hv i hi, hs i hi]
    simp
  · push Not at hm
    rw [hf p hp hm]
    simp

theorem iter_congr {g h : ℕ → ℕ} (hg : ∀ y < 819, g y = h y) (hm : ∀ y < 819, g y < 819) :
    ∀ m, ∀ z < 819, g^[m] z = h^[m] z
  | 0, _, _ => rfl
  | m + 1, z, hz => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, iter_congr hg hm m _ (hm z hz),
      hg z hz]

theorem iter_comp {b : Array ℕ} (hb : ∀ y < 819, b[y]! < 819) (m z : ℕ) (hz : z < 819) :
    (fun y => (compA 819 b b)[y]!)^[m] z = (fun y => b[y]!)^[2 * m] z := by
  rw [Function.iterate_mul]
  refine iter_congr (fun y hy => ?_) (fun y hy => ?_) m z hz
  · rw [compA_get hy]
    rfl
  · rw [compA_get hy]
    exact hb _ (hb y hy)

theorem powLoop_get :
    ∀ fuel (b r : Array ℕ) (e : ℕ), (∀ y < 819, b[y]! < 819) → (∀ x < 819, r[x]! < 819) →
      e < 2 ^ fuel → ∀ x < 819, (f48PowLoop fuel b e r)[x]! = (fun y => b[y]!)^[e] r[x]!
  | 0, b, r, e, _, _, he, x, _ => by
    obtain rfl : e = 0 := by simpa using he
    rfl
  | fuel + 1, b, r, e, hb, hr, he, x, hx => by
    unfold f48PowLoop
    by_cases h0 : e = 0
    · subst h0
      rfl
    · rw [if_neg (by simpa using h0)]
      have hb2 : ∀ y < 819, (compA 819 b b)[y]! < 819 := fun y hy => by
        rw [compA_get hy]
        exact hb _ (hb y hy)
      set r' := if (e % 2 == 1) = true then compA 819 b r else r with hr'
      have hr2 : ∀ x < 819, r'[x]! < 819 ∧ r'[x]! = (fun y => b[y]!)^[e % 2] r[x]! := by
        intro x hx
        rw [hr']
        by_cases hm : e % 2 = 1
        · rw [if_pos (by simpa using hm), compA_get hx, hm]
          exact ⟨hb _ (hr x hx), rfl⟩
        · rw [if_neg (by simpa using hm), show e % 2 = 0 by omega]
          exact ⟨hr x hx, rfl⟩
      rw [powLoop_get fuel _ _ (e / 2) hb2 (fun x hx => (hr2 x hx).1)
        (by rw [Nat.pow_succ] at he; omega) x hx, iter_comp hb _ _ (hr2 x hx).1, (hr2 x hx).2,
        ← Function.iterate_add_apply, Nat.div_add_mod]

theorem powA_get {b : Array ℕ} (hb : ∀ y < 819, b[y]! < 819) {e : ℕ} (he : e < 2 ^ 40) {x : ℕ}
    (hx : x < 819) : (f48PowA b e)[x]! = (fun y => b[y]!)^[e] x := by
  unfold f48PowA
  rw [powLoop_get 40 b _ e hb (fun x hx => by rw [idA_get hx]; exact hx) he x hx, idA_get hx]

theorem iter_mod {f : ℕ → ℕ} {c x : ℕ} (hc : f^[c] x = x) (M : ℕ) : f^[M] x = f^[M % c] x := by
  conv_lhs => rw [← Nat.mod_add_div M c, Function.iterate_add_apply, Function.iterate_mul]
  rw [Function.iterate_fixed hc]

end CFSG.KC.S63K

end
