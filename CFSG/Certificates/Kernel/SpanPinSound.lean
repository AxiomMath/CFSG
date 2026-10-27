module

public import Certificates.Data.Kernel.SpanPin
public import CFSG.Certificates.Kernel.XorSpanSound
public import CFSG.Certificates.Kernel.Spor.BfsReplay
public import Mathlib.Data.Finset.Card

public section

namespace CFSG.KC.SpanPin

open CFSG.KC.Enum CFSG.KC.XorSpan CFSG.PSL3Four.Native CFSG.KS.BfsReplay CFSG.KS.Raw.Orb

theorem lexK_iff (a b c d : Nat) : lexK a b c d = true ↔ LexLt a b c d := by
  unfold lexK LexLt
  rw [bIf_eq, bAnd_eq]
  by_cases h : a < c
  · simp [Nat.blt_eq.mpr h, h]
  · have : Nat.blt a c = false := Bool.eq_false_iff.mpr fun e => h (Nat.blt_eq.mp e)
    simp only [this, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq,
      h, false_or]

structure PtFacts (d w m dw h hm k : Nat) (A B K W : Nat → Nat) (X : Nat → Bool) (o c i : Nat) :
    Prop where
  rref : rrefK d w m dw (K (o + i)) = true
  x : X (K (o + i)) = true
  close : ∀ l < k, wf (W (o + i)) l < c ∧
    mapsK d w m dw (img2 w m h hm (A l) (B l)) (K (o + i)) (K (o + wf (W (o + i)) l)) = true ∧
    (wf (W (o + i)) l = 0 ∨
      ¬ LexLt i l (wf (W (o + wf (W (o + i)) l)) k) (wf (W (o + wf (W (o + i)) l)) (k + 1)))
  zero : i = 0 → wf (W (o + i)) k = 0 ∧ wf (W (o + i)) (k + 1) = 0
  tree : i ≠ 0 → wf (W (o + i)) k < i ∧ wf (W (o + i)) (k + 1) < k ∧
    wf (W (o + wf (W (o + i)) k)) (wf (W (o + i)) (k + 1)) = i ∧
    (i + 1 < c → LexLt (wf (W (o + i)) k) (wf (W (o + i)) (k + 1))
      (wf (W (o + (i + 1))) k) (wf (W (o + (i + 1))) (k + 1)))

theorem ptK_facts {d w m dw h hm k : Nat} {A B K W : Nat → Nat} {X : Nat → Bool} {o c i : Nat}
    (hp : ptK d w m dw h hm k A B K W X o c i = true) :
    PtFacts d w m dw h hm k A B K W X o c i := by
  unfold ptK at hp
  simp only [strictB_eq, Nat.add_eq, Nat.succ_eq_add_one] at hp
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 hp
  obtain ⟨h2, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
  obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h3
  refine ⟨h1, h2, fun l hl => ?_, fun hi => ?_, fun hi => ?_⟩
  · have hl' := CFSG.KS.allN_spec h3 l hl
    obtain ⟨a1, a2⟩ := (CFSG.KS.bAnd_iff _ _).1 hl'
    obtain ⟨a2, a3⟩ := (CFSG.KS.bAnd_iff _ _).1 a2
    refine ⟨Nat.blt_eq.mp a1, a2, ?_⟩
    rw [bIf_eq] at a3
    by_cases hq : wf (W (o + i)) l = 0
    · exact Or.inl hq
    · have : Nat.beq (wf (W (o + i)) l) 0 = false :=
        Bool.eq_false_iff.mpr fun e => hq (Nat.eq_of_beq_eq_true e)
      rw [this] at a3
      simp only [Bool.false_eq_true, ↓reduceIte, bIf_eq] at a3
      refine Or.inr fun hlt => ?_
      have := (lexK_iff _ _ _ _).2 hlt
      rw [this] at a3
      simp at a3
  · subst hi
    rw [bIf_eq] at h4
    simp only [Nat.beq_refl, ↓reduceIte] at h4
    obtain ⟨a1, a2⟩ := (CFSG.KS.bAnd_iff _ _).1 h4
    exact ⟨Nat.eq_of_beq_eq_true a1, Nat.eq_of_beq_eq_true a2⟩
  · rw [bIf_eq] at h4
    have : Nat.beq i 0 = false := Bool.eq_false_iff.mpr fun e => hi (Nat.eq_of_beq_eq_true e)
    rw [this] at h4
    simp only [Bool.false_eq_true, ↓reduceIte] at h4
    obtain ⟨a1, a2⟩ := (CFSG.KS.bAnd_iff _ _).1 h4
    obtain ⟨a2, a3⟩ := (CFSG.KS.bAnd_iff _ _).1 a2
    obtain ⟨a3, a4⟩ := (CFSG.KS.bAnd_iff _ _).1 a3
    refine ⟨Nat.blt_eq.mp a1, Nat.blt_eq.mp a2, Nat.eq_of_beq_eq_true a3, fun hc => ?_⟩
    rw [bIf_eq] at a4
    rw [Nat.blt_eq.mpr hc] at a4
    simp only [↓reduceIte] at a4
    exact (lexK_iff _ _ _ _).1 a4

theorem ptK_key {d w m dw h hm k : Nat} {A B K W : Nat → Nat} {X : Nat → Bool} {o c i : Nat}
    (hp : ptK d w m dw h hm k A B K W X o c i = true) :
    Rref d w m dw (K (o + i)) ∧ X (K (o + i)) = true :=
  ⟨rref_of (ptK_facts hp).rref, (ptK_facts hp).x⟩

theorem spanPin_bfs {d w m dw h hm k o c cap : Nat} {A B K W : Nat → Nat} {X : Nat → Bool}
    {step : Nat → Tab → Tab} {root : Tab} (hmw : m = 2 ^ w - 1) (hdw : dw = d * w)
    (hpt : ∀ i < c, ptK d w m dw h hm k A B K W X o c i = true) (hc : 0 < c) (hcap : c ≤ cap)
    (hinj : ∀ a < c, ∀ b < c, K (o + a) = K (o + b) → a = b)
    (hstep : ∀ l < k, ∀ Kh Kq, Rref d w m dw Kh → Rref d w m dw Kq →
      mapsK d w m dw (img2 w m h hm (A l) (B l)) Kh Kq = true →
      step l (spanTab d w m Kh) = spanTab d w m Kq)
    (hroot : spanTab d w m (K o) = root) :
    bfs step k root cap = ⟨Array.ofFn (n := c) fun i => spanTab d w m (K (o + i.val)),
      Array.ofFn (n := c) fun i => wf (W (o + i.val)) k,
      Array.ofFn (n := c) fun i => wf (W (o + i.val)) (k + 1)⟩ ∧
    treeOK step k root ⟨Array.ofFn (n := c) fun i => spanTab d w m (K (o + i.val)),
      Array.ofFn (n := c) fun i => wf (W (o + i.val)) k,
      Array.ofFn (n := c) fun i => wf (W (o + i.val)) (k + 1)⟩ = true := by
  have F := fun i (hi : i < c) => ptK_facts (hpt i hi)
  have RR := fun i (hi : i < c) => rref_of (F i hi).rref
  have R : Replay step k root c (fun i => spanTab d w m (K (o + i))) (fun i => wf (W (o + i)) k)
      (fun i => wf (W (o + i)) (k + 1)) (fun i j => wf (W (o + i)) j) := by
    refine ⟨hc, by simpa using hroot, (F 0 hc).zero rfl |>.1, (F 0 hc).zero rfl |>.2,
      fun a ha b hb e => hinj a ha b hb (spanTab_inj hmw hdw (RR a ha) (RR b hb) e),
      fun i hi0 hi => ?_, fun i hi0 hi1 => ((F i (by omega)).tree (by omega)).2.2.2 hi1,
      fun i hi j hj => ?_⟩
    · obtain ⟨t1, t2, t3, -⟩ := (F i hi).tree (by omega)
      refine ⟨t1, t2, ?_⟩
      obtain ⟨-, hmap, -⟩ := (F (wf (W (o + i)) k) (by omega)).close (wf (W (o + i)) (k + 1)) t2
      rw [t3] at hmap
      exact (hstep _ t2 _ _ (RR _ (by omega)) (RR i hi) hmap).symm
    · obtain ⟨c1, c2, c3⟩ := (F i hi).close j hj
      exact ⟨c1, hstep j hj _ _ (RR i hi) (RR _ c1) c2, c3⟩
  exact bfs_replay R hcap

theorem ptK_of_slices {d w m dw h hm k : Nat} {A B K W : Nat → Nat} {X : Nat → Bool}
    {o c L S : Nat} (hcS : c ≤ L * S)
    (hs : ∀ s < S, sliceK d w m dw h hm k A B K W X o c (L * s) L = true) :
    ∀ i < c, ptK d w m dw h hm k A B K W X o c i = true := by
  intro i hi
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with e | e
    · subst e
      omega
    · exact e
  have hsl := CFSG.KS.allN_spec (hs (i / L) (by
    rw [Nat.div_lt_iff_lt_mul hL]
    rw [Nat.mul_comm] at hcS
    omega)) (i % L) (Nat.mod_lt i hL)
  rw [strictB_eq, bIf_eq] at hsl
  have e : Nat.add (L * (i / L)) (i % L) = i := Nat.div_add_mod i L
  rw [e, Nat.blt_eq.mpr hi] at hsl
  simpa using hsl

theorem inj_of_sort {cnt : Nat} {T S SI : Nat → Nat}
    (hS : ∀ i < cnt, S i < cnt ∧ SI (S i) = i ∧ (i + 1 < cnt → T (S i) < T (S (i + 1)))) :
    ∀ a < cnt, ∀ b < cnt, T a = T b → a = b := by
  have hmono : ∀ i j, i < j → j < cnt → T (S i) < T (S j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact lt_trans (ih h (by omega)) ((hS j (by omega)).2.2 hj)
      · subst h
        exact (hS i (by omega)).2.2 hj
  have hsurj : ∀ a < cnt, ∃ i < cnt, S i = a := by
    classical
    have himg : (Finset.range cnt).image S = Finset.range cnt := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
        exact Finset.mem_range.2 (hS i (Finset.mem_range.1 hi)).1
      · rw [Finset.card_image_of_injOn]
        intro i hi j hj e
        have h1 := (hS i (Finset.mem_range.1 hi)).2.1
        have h2 := (hS j (Finset.mem_range.1 hj)).2.1
        rw [← h1, ← h2]
        exact congrArg SI e
    intro a ha
    have : a ∈ (Finset.range cnt).image S := by rw [himg]; exact Finset.mem_range.2 ha
    obtain ⟨i, hi, e⟩ := Finset.mem_image.1 this
    exact ⟨i, Finset.mem_range.1 hi, e⟩
  intro a ha b hb e
  obtain ⟨i, hi, rfl⟩ := hsurj a ha
  obtain ⟨j, hj, rfl⟩ := hsurj b hb
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd e (Nat.ne_of_lt (hmono i j h hj))
  · rw [h]
  · exact absurd e.symm (Nat.ne_of_lt (hmono j i h hi))

theorem inj_of_sortK {N L S : Nat} {K SR : Nat → Nat} (hNS : N ≤ L * S)
    (hs : ∀ s < S, sortK N K SR (L * s) L = true) :
    ∀ a < N, ∀ b < N, K a = K b → a = b := by
  rcases Nat.eq_zero_or_pos L with e | hL
  · subst e
    intro a ha
    rw [Nat.zero_mul] at hNS
    omega
  refine inj_of_sort (S := fun i => wf (SR i) 0) (SI := fun s => wf (SR s) 1)
    fun i hi => ?_
  have hsl := CFSG.KS.allN_spec (hs (i / L) (by
    rw [Nat.div_lt_iff_lt_mul hL]
    rw [Nat.mul_comm] at hNS
    omega)) (i % L) (Nat.mod_lt i hL)
  rw [strictB_eq, bIf_eq] at hsl
  have e : Nat.add (L * (i / L)) (i % L) = i := Nat.div_add_mod i L
  rw [e, Nat.blt_eq.mpr hi] at hsl
  simp only [↓reduceIte, strictB_eq] at hsl
  obtain ⟨a1, a2⟩ := (CFSG.KS.bAnd_iff _ _).1 hsl
  obtain ⟨a2, a3⟩ := (CFSG.KS.bAnd_iff _ _).1 a2
  refine ⟨Nat.blt_eq.mp a1, Nat.eq_of_beq_eq_true a2, fun hi1 => ?_⟩
  rw [bIf_eq, Nat.blt_eq.mpr hi1] at a3
  simpa using a3

end CFSG.KC.SpanPin

end
