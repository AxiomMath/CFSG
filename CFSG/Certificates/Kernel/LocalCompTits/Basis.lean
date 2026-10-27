module

public import CFSG.Certificates.Kernel.LocalCompTits.Bsearch
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.TBfsSound

public section

namespace CFSG.KC.LocalComp.TitsSound

open CFSG.KC.Enum CFSG.KS CFSG.SectionRank.Native.Tits CFSG.Sporadic.Th.Native CFSG.KC.LocalComp.Tits

private def lk : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (c, p) :: r, b => if c = b then p else lk r b

private def Sorted (ps : List (Nat × Nat)) : Prop := ps.Pairwise fun x y => y.1 < x.1

private def Good (ps : List (Nat × Nat)) : Prop :=
  ∀ x ∈ ps, x.1 < 52 ∧ x.2 ≠ 0 ∧ x.2 < 2 ^ 52 ∧ x.2.log2 = x.1

private def Rel (piv : Array Nat) (ps : List (Nat × Nat)) : Prop :=
  piv.size = 52 ∧ ∀ b < 52, piv[b]! = lk ps b

private theorem lk_of_not_key {ps : List (Nat × Nat)} {t : Nat} (h : ∀ x ∈ ps, x.1 ≠ t) :
    lk ps t = 0 := by
  induction ps with
  | nil => rfl
  | cons x r ih =>
    obtain ⟨c, p⟩ := x
    simp only [lk]
    rw [if_neg (h (c, p) (by simp))]
    exact ih fun y hy => h y (by simp [hy])

private theorem lk_of_lt {ps : List (Nat × Nat)} {t : Nat} (h : ∀ x ∈ ps, x.1 < t) :
    lk ps t = 0 :=
  lk_of_not_key fun x hx => Nat.ne_of_lt (h x hx)

private theorem mem_insK {t v : Nat} {y : Nat × Nat} :
    ∀ {ps : List (Nat × Nat)}, y ∈ insK t v ps ↔ y = (t, v) ∨ y ∈ ps
  | [] => by simp [insK]
  | (c, p) :: r => by
    simp only [insK]
    split
    · simp
    · simp only [List.mem_cons, mem_insK (ps := r)]
      exact or_left_comm

private theorem lk_insK {t v : Nat} :
    ∀ {ps : List (Nat × Nat)}, (∀ x ∈ ps, x.1 ≠ t) → ∀ b, lk (insK t v ps) b = if t = b then v else lk ps b
  | [], _, b => by simp [insK, lk]
  | (c, p) :: r, h, b => by
    have hc : c ≠ t := h (c, p) (by simp)
    simp only [insK]
    split
    · simp [lk]
    · have ih := lk_insK (v := v) (ps := r) (fun x hx => h x (by simp [hx])) b
      simp only [lk, ih]
      by_cases e1 : c = b
      · by_cases e2 : t = b
        · exact absurd (e1.trans e2.symm) hc
        · simp [e1, e2]
      · by_cases e2 : t = b <;> simp [e1, e2]

private theorem sorted_insK {t v : Nat} {ps : List (Nat × Nat)} (hs : Sorted ps)
    (h : ∀ x ∈ ps, x.1 ≠ t) : Sorted (insK t v ps) := by
  induction ps with
  | nil => simp [insK, Sorted]
  | cons x r ih =>
    obtain ⟨c, p⟩ := x
    have hc : c ≠ t := h (c, p) (by simp)
    simp only [Sorted, List.pairwise_cons] at hs
    simp only [insK]
    split
    · rename_i hlt
      simp only [Sorted, List.pairwise_cons]
      refine ⟨?_, hs⟩
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hlt
      · exact Nat.lt_trans (hs.1 y hy) hlt
    · rename_i hnlt
      simp only [Sorted, List.pairwise_cons]
      refine ⟨?_, ih hs.2 fun x hx => h x (by simp [hx])⟩
      intro y hy
      rw [mem_insK] at hy
      rcases hy with rfl | hy
      · exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt hnlt) hc.symm
      · exact hs.1 y hy

private theorem good_insK {t v : Nat} {ps : List (Nat × Nat)} (hg : Good ps)
    (h : t < 52 ∧ v ≠ 0 ∧ v < 2 ^ 52 ∧ v.log2 = t) : Good (insK t v ps) := by
  intro y hy
  rw [mem_insK] at hy
  rcases hy with rfl | hy
  · exact h
  · exact hg y hy

private theorem bit_eq (v b : Nat) : (Nat.land (Nat.shiftRight v b) 1 = 1) ↔ v.testBit b = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_true_eq]
  change (v >>> b &&& 1 = 1) ↔ _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

private theorem bit_eq' (v b : Nat) :
    Nat.beq (Nat.land (Nat.shiftRight v b) 1) 1 = true ↔ v.testBit b = true := by
  rw [Nat.beq_eq]
  exact bit_eq v b

private theorem redK_cons (b p : Nat) (ps : List (Nat × Nat)) (v : Nat) :
    redK ((b, p) :: ps) v = redK ps (if v.testBit b = true then v ^^^ p else v) := by
  simp only [redK, CFSG.KS.Raw.Orb.nIf_eq, bit_eq']
  rfl

private theorem redK_lt {ps : List (Nat × Nat)} (hg : Good ps) :
    ∀ {v : Nat}, v < 2 ^ 52 → redK ps v < 2 ^ 52 := by
  induction ps with
  | nil => intro v hv; exact hv
  | cons x r ih =>
    obtain ⟨b, p⟩ := x
    intro v hv
    rw [redK_cons]
    refine ih (fun y hy => hg y (by simp [hy])) ?_
    split
    · exact Nat.xor_lt_two_pow hv (hg (b, p) (by simp)).2.2.1
    · exact hv

private theorem redK_testBit_high {b : Nat} {r : List (Nat × Nat)} (h1 : ∀ x ∈ r, x.1 < b)
    (h2 : ∀ x ∈ r, x.2 < 2 ^ (x.1 + 1)) : ∀ v, (redK r v).testBit b = v.testBit b := by
  induction r with
  | nil => intro v; rfl
  | cons x r ih =>
    obtain ⟨c, p⟩ := x
    intro v
    rw [redK_cons, ih (fun y hy => h1 y (by simp [hy])) (fun y hy => h2 y (by simp [hy]))]
    split
    · have hc := h1 (c, p) (by simp)
      have hp : p < 2 ^ b :=
        Nat.lt_of_lt_of_le (h2 (c, p) (by simp)) (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_xor, Nat.testBit_lt_two_pow hp]
      simp
    · rfl

private theorem redK_clear {ps : List (Nat × Nat)} (hs : Sorted ps) (hg : Good ps) :
    ∀ v, ∀ x ∈ ps, (redK ps v).testBit x.1 = false := by
  induction ps with
  | nil => intro v x hx; simp at hx
  | cons y r ih =>
    obtain ⟨b, p⟩ := y
    intro v x hx
    simp only [Sorted, List.pairwise_cons] at hs
    rw [redK_cons]
    have hgr : Good r := fun z hz => hg z (by simp [hz])
    rcases List.mem_cons.1 hx with rfl | hx
    · simp only
      have hgp := hg (b, p) (by simp)
      rw [redK_testBit_high hs.1 (fun z hz => by
        have hz' := hg z (by simp [hz])
        rw [← hz'.2.2.2]; exact Nat.lt_log2_self)]
      split
      · rename_i hv
        rw [Nat.testBit_xor, hv]
        have : p.testBit b = true := by
          have := Nat.testBit_log2 hgp.2.1
          rwa [hgp.2.2.2] at this
        simp [this]
      · exact Bool.eq_false_iff.2 ‹_›
    · exact ih hs.2 hgr _ x hx

private theorem topK_eq : ∀ (c v : Nat), v < 2 ^ c → v ≠ 0 → topK c v = v.log2
  | 0, v, h, h0 => by simp at h; omega
  | c + 1, v, h, h0 => by
    simp only [topK, CFSG.KS.Raw.Orb.nIf_eq, bit_eq']
    by_cases hv : v.testBit c = true
    · rw [if_pos hv]
      have h2 := Nat.ge_two_pow_of_testBit hv
      symm
      exact Nat.log2_eq_iff h0 |>.2 ⟨h2, h⟩
    · rw [if_neg hv]
      have : v < 2 ^ c := by
        refine Nat.lt_of_not_ge fun hge => hv ?_
        have : v.log2 = c := Nat.log2_eq_iff h0 |>.2 ⟨hge, h⟩
        rw [← this]
        exact Nat.testBit_log2 h0
      exact topK_eq c v this h0

private def stepb (piv : Array Nat) (b v : Nat) : Nat :=
  if (v.testBit b && piv[b]! != 0) = true then v ^^^ piv[b]! else v

private theorem foldr_range_succ' (f : Nat → Nat → Nat) (M s : Nat) :
    (List.range (M + 1)).foldr f s = (List.range M).foldr f (f M s) := by
  rw [List.range_succ, List.foldr_append]
  rfl

private theorem foldl_desc (g : Nat → Nat → Nat) : ∀ n s,
    (List.range n).foldl (fun s k => g (n - 1 - k) s) s = (List.range n).foldr g s
  | 0, _ => rfl
  | n + 1, s => by
    rw [foldr_range_succ', List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    have e : ∀ k, n + 1 - 1 - Nat.succ k = n - 1 - k := fun k => by omega
    have e0 : n + 1 - 1 - 0 = n := by omega
    have e1 : (fun (x y : Nat) => g (n + 1 - 1 - y.succ) x) = fun s k => g (n - 1 - k) s := by
      funext x y
      rw [e y]
    rw [e0, e1]
    exact foldl_desc g n _

private theorem red_eq {piv : Array Nat} :
    ∀ (c : Nat), c ≤ 52 → ∀ (ps : List (Nat × Nat)), Sorted ps → Good ps → (∀ x ∈ ps, x.1 < c) →
      (∀ b < c, piv[b]! = lk ps b) → ∀ v, (List.range c).foldr (stepb piv) v = redK ps v
  | 0, _, ps, _, _, hk, _, v => by
    cases ps with
    | nil => rfl
    | cons x r => exact absurd (hk x (by simp)) (by omega)
  | c + 1, hc, ps, hs, hg, hk, hl, v => by
    rw [foldr_range_succ']
    cases ps with
    | nil =>
      have e : stepb piv c v = v := by
        simp [stepb, hl c (by omega), lk]
      rw [e]
      exact red_eq c (by omega) [] hs hg (by simp) (fun b hb => hl b (by omega)) v
    | cons x r =>
      obtain ⟨b, p⟩ := x
      simp only [Sorted, List.pairwise_cons] at hs
      have hgb := hg (b, p) (by simp)
      have hbc : b < c + 1 := hk (b, p) (by simp)
      by_cases hb : b = c
      · subst hb
        have e : stepb piv b v = if v.testBit b = true then v ^^^ p else v := by
          have := hl b (by omega)
          simp only [lk, if_true] at this
          simp only [stepb, this]
          have : (p != 0) = true := by simpa using hgb.2.1
          simp [this]
        rw [e, redK_cons]
        refine red_eq b (by omega) r hs.2 (fun z hz => hg z (by simp [hz])) hs.1 ?_ _
        intro b' hb'
        have := hl b' (by omega)
        simp only [lk] at this
        rw [this, if_neg (by omega)]
      · have e : stepb piv c v = v := by
          have := hl c (by omega)
          have h0 : lk ((b, p) :: r) c = 0 := by
            refine lk_of_lt fun z hz => ?_
            rcases List.mem_cons.1 hz with rfl | hz
            · omega
            · exact Nat.lt_trans (hs.1 z hz) (by omega)
          simp [stepb, this, h0]
        rw [e]
        exact red_eq c (by omega) ((b, p) :: r) (by simpa [Sorted] using hs) hg
          (fun z hz => by
            rcases List.mem_cons.1 hz with rfl | hz
            · omega
            · exact Nat.lt_trans (hs.1 z hz) (by omega))
          (fun b' hb' => hl b' (by omega)) v

private def innerBody (piv : Array Nat) (k v : Nat) : Id (ForInStep Nat) :=
  if (v.testBit (51 - k) && piv[51 - k]! != 0) = true then pure (ForInStep.yield (v ^^^ piv[51 - k]!))
  else pure (ForInStep.yield v)

private def outerBody (pts : Array Nat) (i : Nat) (s : Array Nat × Array Nat) :
    Id (ForInStep (Array Nat × Array Nat)) :=
  let v := Id.run (forIn (List.range' 0 52) pts[i]! (innerBody s.1))
  if (v != 0) = true then pure (ForInStep.yield (s.1.set! v.log2 v, s.2.push i))
  else pure (ForInStep.yield (s.1, s.2))

private theorem basisIdx_eq' (pts : Array Nat) :
    basisIdx pts = (Id.run (forIn (List.range' 0 pts.size)
      ((Array.replicate 52 0 : Array Nat), (#[] : Array Nat)) (outerBody pts))).2 := by
  unfold basisIdx
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private theorem inner_eq (piv : Array Nat) (v0 : Nat) :
    Id.run (forIn (List.range' 0 52) v0 (innerBody piv)) = (List.range 52).foldr (stepb piv) v0 := by
  have hb : innerBody piv = fun k v => pure (ForInStep.yield (stepb piv (51 - k) v)) := by
    funext k v
    simp only [innerBody, stepb]
    split <;> rfl
  rw [hb, List.forIn_pure_yield_eq_foldl, ← List.range_eq_range']
  have := foldl_desc (stepb piv) 52 v0
  exact this

private theorem get_set! {a : Array Nat} {i j v : Nat} (hj : j < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ j (by simp; omega), getElem!_pos a j hj]
  by_cases e : i = j
  · subst e
    simp
  · rw [Array.getElem_setIfInBounds_ne hj e]
    simp [e]

private theorem step_rel {piv : Array Nat} {ps : List (Nat × Nat)} (hr : Rel piv ps) (hs : Sorted ps)
    (hg : Good ps) {v0 : Nat} (h0 : v0 < 2 ^ 52) :
    Id.run (forIn (List.range' 0 52) v0 (innerBody piv)) = redK ps v0 ∧
      (redK ps v0 ≠ 0 →
        Rel (piv.set! (redK ps v0).log2 (redK ps v0)) (insK (topK 52 (redK ps v0)) (redK ps v0) ps) ∧
          Sorted (insK (topK 52 (redK ps v0)) (redK ps v0) ps) ∧
          Good (insK (topK 52 (redK ps v0)) (redK ps v0) ps)) := by
  have hred : Id.run (forIn (List.range' 0 52) v0 (innerBody piv)) = redK ps v0 := by
    rw [inner_eq]
    exact red_eq 52 (Nat.le_refl _) ps hs hg (fun x hx => (hg x hx).1) hr.2 v0
  refine ⟨hred, fun hne => ?_⟩
  have hlt := redK_lt hg h0
  have ht : topK 52 (redK ps v0) = (redK ps v0).log2 := topK_eq 52 _ hlt hne
  have hl52 : (redK ps v0).log2 < 52 := (Nat.log2_lt hne).2 hlt
  have hnk : ∀ x ∈ ps, x.1 ≠ (redK ps v0).log2 := by
    intro x hx e
    have h1 := redK_clear hs hg v0 x hx
    rw [e] at h1
    have := Nat.testBit_log2 hne
    rw [h1] at this
    exact Bool.false_ne_true this
  rw [ht]
  refine ⟨⟨?_, ?_⟩, sorted_insK hs hnk, good_insK hg ⟨hl52, hne, hlt, rfl⟩⟩
  · simp [hr.1]
  · intro b hb
    have hsz := hr.1
    rw [lk_insK hnk, get_set! (by omega), hr.2 b hb]

private theorem checks_basis {N : Nat} {TP : Nat → Nat} (hlt : ∀ i < N, TP i < 2 ^ 52) :
    basisIdx (Array.ofFn (n := N) fun i => TP i.val) =
      (basisK TP N 0 [] []).reverse.toArray := by
  rw [basisIdx_eq']
  have hsz : (Array.ofFn (n := N) fun i => TP i.val).size = N := by simp
  rw [hsz]
  have key := CFSG.KS.TBfs.forIn_list_yield (List.range' 0 N)
    ((Array.replicate 52 0 : Array Nat), (#[] : Array Nat))
    (outerBody (Array.ofFn (n := N) fun i => TP i.val))
    (fun j s => ∃ ps acc, Rel s.1 ps ∧ Sorted ps ∧ Good ps ∧ s.2 = acc.reverse.toArray ∧
      basisK TP (N - j) j ps acc = basisK TP N 0 [] []) ?_ ?_
  · obtain ⟨ps, acc, -, -, -, h2, h3⟩ := key
    simp only [List.length_range', Nat.sub_self] at h3
    rw [h2]
    simp only [basisK] at h3
    rw [h3]
  · intro j hj s ⟨ps, acc, hr, hs, hg, hidx, hb⟩
    have hjN : j < N := by simpa using hj
    have hget : (List.range' 0 N)[j] = j := by simp
    rw [hget]
    have hp : (Array.ofFn (n := N) fun i => TP i.val)[j]! = TP j := CFSG.KS.TBfs.ofFn_get hjN
    obtain ⟨f, hf⟩ : ∃ f, N - j = f + 1 := ⟨N - j - 1, by omega⟩
    rw [hf] at hb
    have hf' : N - (j + 1) = f := by omega
    obtain ⟨hred, hnew⟩ := step_rel hr hs hg (hlt j hjN)
    simp only [outerBody, hp, hred]
    by_cases hv : redK ps (TP j) = 0
    · refine ⟨(s.1, s.2), ?_, ps, acc, hr, hs, hg, hidx, ?_⟩
      · simp [hv]
      · simp only [basisK, hv, if_true] at hb
        rw [hf']; exact hb
    · obtain ⟨hr', hs', hg'⟩ := hnew hv
      refine ⟨(s.1.set! (redK ps (TP j)).log2 (redK ps (TP j)), s.2.push j), ?_,
        insK (topK 52 (redK ps (TP j))) (redK ps (TP j)) ps, j :: acc, hr', hs', hg', ?_, ?_⟩
      · simp [hv]
      · simp [hidx]
      · simp only [basisK, hv, if_false] at hb
        rw [hf']; exact hb
  · refine ⟨[], [], ⟨by simp, fun b hb => ?_⟩, by simp [Sorted], by simp [Good], by simp, ?_⟩
    · simp [lk, hb]
    · simp [basisK]

theorem basisIdx_eq {N : Nat} {TP : Nat → Nat} (hlt : ∀ i < N, TP i < 2 ^ 52) :
    basisIdx (Array.ofFn (n := N) fun i => TP i.val) = (basisK TP N 0 [] []).reverse.toArray :=
  checks_basis hlt

theorem checkPts_sound {N : Nat} {TP : Nat → Nat} {bv CP : List Nat} {pts : Array Nat}
    (hp : pts = Array.ofFn (n := N) (fun i => TP i.val)) (h : checkK N TP bv CP = true) :
    bv.toArray.map (bsearch pts) = (CP.take bv.length).toArray ∧
      basisIdx pts = (CP.drop bv.length).toArray := by
  subst hp
  unfold checkK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, -⟩, h4⟩ := h
  have hlt : ∀ i < N, TP i < 2 ^ 52 := by
    intro i hi
    have := (CFSG.KS.Raw.Orb.allN_iff.1 h1) i hi
    simpa [Nat.blt_eq, Nat.shiftLeft_eq] using this
  have hinc : ∀ i, i + 1 < N → TP i < TP (i + 1) := by
    intro i hi
    have := (CFSG.KS.Raw.Orb.allN_iff.1 h2) i (by omega)
    simpa [Nat.blt_eq] using this
  subst h4
  have e1 : (List.map (idxK N TP) bv ++ (basisK TP N 0 [] []).reverse).take bv.length =
      List.map (idxK N TP) bv := by
    have := List.take_left' (l₁ := List.map (idxK N TP) bv) (l₂ := (basisK TP N 0 [] []).reverse)
      (i := bv.length) (by simp)
    exact this
  have e2 : (List.map (idxK N TP) bv ++ (basisK TP N 0 [] []).reverse).drop bv.length =
      (basisK TP N 0 [] []).reverse := by
    exact List.drop_left' (by simp)
  rw [e1, e2]
  refine ⟨?_, basisIdx_eq hlt⟩
  rw [← List.map_toArray]
  congr 1
  exact funext fun v => bsearch_ofFn hlt hinc v

end CFSG.KC.LocalComp.TitsSound

end
