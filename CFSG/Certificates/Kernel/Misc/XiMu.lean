module

public import CFSG.Certificates.Kernel.Misc.XiBits
public import CFSG.Certificates.Kernel.J4Q.BfsOrder
public import Certificates.Data.CFSGNative.Fischer.Xi22

public section

set_option exponentiation.threshold 10000
set_option maxRecDepth 100000

namespace CFSG.KC.Misc.Xi

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46 CFSG.KC.Misc.Lines
  CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KC.J4Q.BfsOrder

abbrev MSt := Array Nat × Array Nat × Array Nat

@[expose] def muStep (ax : Flags) (h y : Nat) (st : MSt) : MSt :=
  if (ax[y]! && st.1[y]! == 1408) = true then
    (st.1.set! y st.2.1.size, st.2.1.push y, st.2.2.push h) else (st.1, st.2.1, st.2.2)

@[expose] def muInner (ax : Flags) (h y : Nat) (st : MSt) : Id (ForInStep MSt) :=
  if (ax[y]! && st.1[y]! == 1408) = true then
    pure (ForInStep.yield (st.1.set! y st.2.1.size, st.2.1.push y, st.2.2.push h))
  else pure (ForInStep.yield (st.1, st.2.1, st.2.2))

@[expose] def muOuter (A : Array Flags) (mu : Array Nat) (h : Nat) (st : MSt) :
    Id (ForInStep MSt) :=
  if h < st.2.1.size then
    (do
      let s ← forIn mu (st.1, st.2.1, st.2.2) (muInner A[st.2.1[h]!]! h)
      pure (ForInStep.yield (s.1, s.2.1, s.2.2)))
  else pure (ForInStep.done (st.1, st.2.1, st.2.2))

theorem muInner_eq (ax : Flags) (h y : Nat) (st : MSt) :
    muInner ax h y st = pure (ForInStep.yield (muStep ax h y st)) := by
  unfold muInner muStep
  split <;> rfl

theorem muTree_eq (A : Array Flags) (v : Nat)
    (hmu : 0 < (filterRange (fun x => (A[0]!)[x]! && (A[x]!)[v]!) 1408 []).toArray.size) :
    muTree A v =
      Id.run (do
        let s ← forIn [:1408]
          (((Array.replicate 1408 1408).set! (filterRange (fun x => (A[0]!)[x]! &&
            (A[x]!)[v]!) 1408 []).toArray[0]! 0,
            #[(filterRange (fun x => (A[0]!)[x]! && (A[x]!)[v]!) 1408 []).toArray[0]!], #[0]) : MSt)
          (muOuter A (filterRange (fun x => (A[0]!)[x]! && (A[x]!)[v]!) 1408 []).toArray)
        pure (s.2.1, s.2.2, s.1)) := by
  unfold muTree
  rw [if_pos hmu]
  simp only []
  unfold muOuter muInner
  rfl

theorem muLoop_eq (mu : Array Nat) (ax : Flags) (h : Nat) (st : MSt) :
    Id.run (forIn mu st (muInner ax h)) = mu.toList.foldl (fun st y => muStep ax h y st) st := by
  rw [← Array.forIn_toList]
  have e : muInner ax h = fun y st => pure (ForInStep.yield (muStep ax h y st)) :=
    funext fun y => funext fun st => muInner_eq ax h y st
  rw [e]
  simp only [List.forIn_pure_yield_eq_foldl, Id.run]
  rfl

theorem foldl_prefix_inv {α β : Type} (P : List α → β → Prop) (g : β → α → β) :
    ∀ (suf pre : List α) (b : β), P pre b →
      (∀ pre' a b', P pre' b' → a ∈ suf → P (pre' ++ [a]) (g b' a)) →
      P (pre ++ suf) (suf.foldl g b) := by
  intro suf
  induction suf with
  | nil => intro pre b h _; simpa using h
  | cons a t ih =>
    intro pre b h hstep
    rw [List.foldl_cons]
    have := ih (pre ++ [a]) (g b a) (hstep pre a b h List.mem_cons_self) (fun pre' a' b' h' ha' =>
      hstep pre' a' b' h' (List.mem_cons_of_mem a ha'))
    simpa using this

theorem inj_card_le {n b : Nat} (f : Nat → Nat) (hf : ∀ i < n, f i < b)
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j) : n ≤ b := by
  have := Finset.card_le_card_of_injOn (s := Finset.range n) (t := Finset.range b) f
    (by intro i hi; simpa using hf i (by simpa using hi))
    (by intro i hi j hj h; exact hinj i (by simpa using hi) j (by simpa using hj) h)
  simpa using this

structure MBase (A : Array Flags) (v : Nat) (st : MSt) : Prop where
  possz : st.1.size = 1408
  parsz : st.2.2.size = st.2.1.size
  ptsC : ∀ i < st.2.1.size, st.2.1[i]! < 1408 ∧ (A[0]!)[st.2.1[i]!]! = true ∧
    (A[st.2.1[i]!]!)[v]! = true ∧ st.1[st.2.1[i]!]! = i
  parOK : ∀ i < st.2.1.size, 0 < i → st.2.2[i]! < i ∧
    (A[st.2.1[st.2.2[i]!]!]!)[st.2.1[i]!]! = true
  posOK : ∀ x < 1408, st.1[x]! ≠ 1408 → st.1[x]! < st.2.1.size ∧ st.2.1[st.1[x]!]! = x
  sizeLe : st.2.1.size ≤ 1408
  sizePos : 0 < st.2.1.size

@[expose] def MProc (A : Array Flags) (v b : Nat) (st : MSt) : Prop :=
  ∀ h' < b, h' < st.2.1.size → ∀ y < 1408, (A[0]!)[y]! = true → (A[y]!)[v]! = true →
    (A[st.2.1[h']!]!)[y]! = true → st.1[y]! ≠ 1408

theorem muStep_base {A : Array Flags} {v : Nat} {st : MSt} (hB : MBase A v st) {h : Nat}
    (hh : h < st.2.1.size) {y : Nat} (hy : y < 1408) (hy0 : (A[0]!)[y]! = true)
    (hyv : (A[y]!)[v]! = true) :
    MBase A v (muStep (A[st.2.1[h]!]!) h y st) ∧
      (∀ i < st.2.1.size, (muStep (A[st.2.1[h]!]!) h y st).2.1[i]! = st.2.1[i]!) ∧
      st.2.1.size ≤ (muStep (A[st.2.1[h]!]!) h y st).2.1.size ∧
      (∀ x < 1408, st.1[x]! ≠ 1408 → (muStep (A[st.2.1[h]!]!) h y st).1[x]! ≠ 1408) ∧
      ((A[st.2.1[h]!]!)[y]! = true → (muStep (A[st.2.1[h]!]!) h y st).1[y]! ≠ 1408) := by
  unfold muStep
  by_cases hc : ((A[st.2.1[h]!]!)[y]! && st.1[y]! == 1408) = true
  · rw [if_pos hc]
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hax, hpy⟩ := hc
    have hynot : ∀ i < st.2.1.size, st.2.1[i]! ≠ y := by
      intro i hi hiy
      have := (hB.ptsC i hi).2.2.2
      rw [hiy, hpy] at this
      have := hB.sizeLe
      omega
    have hinj : ∀ i < st.2.1.size, ∀ j < st.2.1.size, st.2.1[i]! = st.2.1[j]! → i = j := by
      intro i hi j hj hij
      have h1 := (hB.ptsC i hi).2.2.2
      have h2 := (hB.ptsC j hj).2.2.2
      rw [hij] at h1
      omega
    have hsz : st.2.1.size + 1 ≤ 1408 := by
      refine inj_card_le (fun i => if i < st.2.1.size then st.2.1[i]! else y) (fun i hi => ?_)
        (fun i hi j hj hij => ?_)
      · by_cases hlt : i < st.2.1.size
        · simp only [if_pos hlt]
          exact (hB.ptsC i hlt).1
        · simp only [if_neg hlt]
          exact hy
      · by_cases hi' : i < st.2.1.size <;> by_cases hj' : j < st.2.1.size
        · simp only [if_pos hi', if_pos hj'] at hij
          exact hinj i hi' j hj' hij
        · simp only [if_pos hi', if_neg hj'] at hij
          exact absurd hij (hynot i hi')
        · simp only [if_neg hi', if_pos hj'] at hij
          exact absurd hij.symm (hynot j hj')
        · omega
    have hsize : st.2.1.size < 1408 := by omega
    have hposy : (st.1.set! y st.2.1.size)[y]! = st.2.1.size :=
      Array.getElem!_set!_self _ _ _ (by rw [hB.possz]; exact hy)
    have hposne : ∀ x, x ≠ y → (st.1.set! y st.2.1.size)[x]! = st.1[x]! := fun x hx =>
      Array.getElem!_set!_ne _ _ _ _ (fun h => hx h.symm)
    have hptsne : ∀ i < st.2.1.size, (st.2.1.push y)[i]! = st.2.1[i]! := fun i hi =>
      push_getElem!_lt _ _ hi
    have hptsy : (st.2.1.push y)[st.2.1.size]! = y := push_getElem!_size _ _
    have hparne : ∀ i < st.2.1.size, (st.2.2.push h)[i]! = st.2.2[i]! := fun i hi =>
      push_getElem!_lt _ _ (by rw [hB.parsz]; exact hi)
    have hparh : (st.2.2.push h)[st.2.1.size]! = h := by
      rw [← hB.parsz]
      exact push_getElem!_size _ _
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · show (st.1.set! y st.2.1.size).size = 1408
      rw [Array.size_set!, hB.possz]
    · show (st.2.2.push h).size = (st.2.1.push y).size
      simp [hB.parsz]
    · intro i hi
      have hi' : i < st.2.1.size + 1 := by simpa using hi
      show (st.2.1.push y)[i]! < 1408 ∧ (A[0]!)[(st.2.1.push y)[i]!]! = true ∧
        (A[(st.2.1.push y)[i]!]!)[v]! = true ∧
        (st.1.set! y st.2.1.size)[(st.2.1.push y)[i]!]! = i
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi'' | rfl
      · rw [hptsne i hi'']
        obtain ⟨a1, a2, a3, a4⟩ := hB.ptsC i hi''
        refine ⟨a1, a2, a3, ?_⟩
        rw [hposne _ (hynot i hi'')]
        exact a4
      · rw [hptsy, hposy]
        exact ⟨hy, hy0, hyv, rfl⟩
    · intro i hi hi0
      have hi' : i < st.2.1.size + 1 := by simpa using hi
      show (st.2.2.push h)[i]! < i ∧
        (A[(st.2.1.push y)[(st.2.2.push h)[i]!]!]!)[(st.2.1.push y)[i]!]! = true
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi'' | rfl
      · obtain ⟨b1, b2⟩ := hB.parOK i hi'' hi0
        rw [hparne i hi'', hptsne _ (by omega), hptsne i hi'']
        exact ⟨b1, b2⟩
      · rw [hparh, hptsne h hh, hptsy]
        exact ⟨hh, hax⟩
    · intro x hx hne
      change (st.1.set! y st.2.1.size)[x]! ≠ 1408 at hne
      show (st.1.set! y st.2.1.size)[x]! < (st.2.1.push y).size ∧
        (st.2.1.push y)[(st.1.set! y st.2.1.size)[x]!]! = x
      by_cases hxy : x = y
      · subst hxy
        rw [hposy]
        exact ⟨by simp, hptsy⟩
      · rw [hposne x hxy] at hne ⊢
        obtain ⟨c1, c2⟩ := hB.posOK x hx hne
        rw [hptsne _ c1]
        exact ⟨by simp; omega, c2⟩
    · show (st.2.1.push y).size ≤ 1408
      simpa using hsz
    · show 0 < (st.2.1.push y).size
      simp
    · exact hptsne
    · show st.2.1.size ≤ (st.2.1.push y).size
      simp
    · intro x hx hne
      change (st.1.set! y st.2.1.size)[x]! ≠ 1408
      by_cases hxy : x = y
      · subst hxy
        rw [hposy]
        omega
      · rw [hposne x hxy]
        exact hne
    · intro _
      change (st.1.set! y st.2.1.size)[y]! ≠ 1408
      rw [hposy]
      omega
  · rw [if_neg hc]
    exact ⟨hB, fun i _ => rfl, Nat.le_refl _, fun x _ hx => hx, fun hax => by
      have : st.1[y]! ≠ 1408 := by
        intro hp
        exact hc (by simp [hax, hp])
      exact this⟩

theorem muInnerLoop {A : Array Flags} {v : Nat} {st : MSt} (hB : MBase A v st) {h : Nat}
    (hh : h < st.2.1.size) (hP : MProc A v h st) (mu : Array Nat)
    (hmu : ∀ y ∈ mu.toList, y < 1408 ∧ (A[0]!)[y]! = true ∧ (A[y]!)[v]! = true)
    (hcomp : ∀ y < 1408, (A[0]!)[y]! = true → (A[y]!)[v]! = true → y ∈ mu.toList) :
    MBase A v (Id.run (forIn mu st (muInner (A[st.2.1[h]!]!) h))) ∧
    MProc A v (h + 1) (Id.run (forIn mu st (muInner (A[st.2.1[h]!]!) h))) := by
  rw [muLoop_eq]
  have key := foldl_prefix_inv
    (P := fun pre st'' => MBase A v st'' ∧ (∀ i < st.2.1.size, st''.2.1[i]! = st.2.1[i]!) ∧
      st.2.1.size ≤ st''.2.1.size ∧ (∀ x < 1408, st.1[x]! ≠ 1408 → st''.1[x]! ≠ 1408) ∧
      (∀ y ∈ pre, y < 1408 ∧ ((A[st.2.1[h]!]!)[y]! = true → st''.1[y]! ≠ 1408)))
    (fun s y => muStep (A[st.2.1[h]!]!) h y s) mu.toList [] st
    ⟨hB, fun i _ => rfl, Nat.le_refl _, fun x _ hx => hx, fun y hy => absurd hy (by simp)⟩
    (fun pre' a b' hb' ha => by
      obtain ⟨hB', hb1, hb2, hb3, hb4⟩ := hb'
      obtain ⟨hy, hy0, hyv⟩ := hmu a ha
      have hh' : h < b'.2.1.size := by omega
      have hax : A[b'.2.1[h]!]! = A[st.2.1[h]!]! := by rw [hb1 h hh]
      obtain ⟨c1, c2, c3, c4, c5⟩ := muStep_base hB' hh' hy hy0 hyv
      rw [hax] at c1 c2 c3 c4 c5
      refine ⟨c1, fun i hi => ?_, by omega, fun x hx hxv => c4 x hx (hb3 x hx hxv),
        fun y hy' => ?_⟩
      · rw [c2 i (by omega)]
        exact hb1 i hi
      · rcases List.mem_append.1 hy' with hy' | hy'
        · exact ⟨(hb4 y hy').1, fun hadj => c4 y (hb4 y hy').1 ((hb4 y hy').2 hadj)⟩
        · simp only [List.mem_singleton] at hy'
          subst hy'
          exact ⟨hy, fun hadj => c5 hadj⟩)
  obtain ⟨hB2, hb1, hb2, hb3, hb4⟩ := key
  refine ⟨hB2, fun h' hh' hh'2 y hy hy0 hyv hadj => ?_⟩
  rw [List.nil_append] at hb4
  rcases Nat.lt_succ_iff_lt_or_eq.1 hh' with hlt | rfl
  · have hlt' : h' < st.2.1.size := by omega
    rw [hb1 h' hlt'] at hadj
    exact hb3 y hy (hP h' hlt hlt' y hy hy0 hyv hadj)
  · rw [hb1 h' hh] at hadj
    exact (hb4 y (hcomp y hy hy0 hyv)).2 hadj

theorem muOuterLoop {A : Array Flags} {v : Nat} {init : MSt} (hinit : MBase A v init)
    (mu : Array Nat) (hmu : ∀ y ∈ mu.toList, y < 1408 ∧ (A[0]!)[y]! = true ∧ (A[y]!)[v]! = true)
    (hcomp : ∀ y < 1408, (A[0]!)[y]! = true → (A[y]!)[v]! = true → y ∈ mu.toList) :
    MBase A v (Id.run (forIn [:1408] init (muOuter A mu))) ∧
      MProc A v (Id.run (forIn [:1408] init (muOuter A mu))).2.1.size
        (Id.run (forIn [:1408] init (muOuter A mu))) := by
  refine forIn_range_inv (fun h st => MBase A v st ∧ MProc A v h st)
    (fun st => MBase A v st ∧ MProc A v st.2.1.size st) (muOuter A mu) 1408 init
    (fun h st hh hI => ?_) (fun st hI => ?_) ⟨hinit, fun h' hh' => absurd hh' (Nat.not_lt_zero _)⟩
  · obtain ⟨hB, hP⟩ := hI
    unfold muOuter
    by_cases hlt : h < st.2.1.size
    · rw [if_pos hlt]
      exact muInnerLoop hB hlt hP mu hmu hcomp
    · rw [if_neg hlt]
      show MBase A v st ∧ MProc A v st.2.1.size st
      refine ⟨hB, fun h' hh' hh'2 y hy hy0 hyv hadj => ?_⟩
      exact hP h' (by omega) hh'2 y hy hy0 hyv hadj
  · obtain ⟨hB, hP⟩ := hI
    exact ⟨hB, fun h' hh' hh'2 y hy hy0 hyv hadj =>
      hP h' (by have := hB.sizeLe; omega) hh'2 y hy hy0 hyv hadj⟩

theorem mu_mem_iff (A : Array Flags) (v : Nat) (y : Nat) :
    y ∈ (filterRange (fun x => (A[0]!)[x]! && (A[x]!)[v]!) 1408 []).toArray.toList ↔
      y < 1408 ∧ (A[0]!)[y]! = true ∧ (A[y]!)[v]! = true := by
  rw [List.toList_toArray, filterRange_eq, List.append_nil, List.mem_filter, List.mem_range,
    Bool.and_eq_true]

theorem muInit_base' {A : Array Flags} {v : Nat} {P : Array Nat} {m0 : Nat} (hsz : P.size = 1408)
    (hm0 : m0 < 1408) (h0 : (A[0]!)[m0]! = true) (hv : (A[m0]!)[v]! = true) (hp0 : P[m0]! = 0)
    (hpne : ∀ x < 1408, x ≠ m0 → P[x]! = 1408) : MBase A v (P, #[m0], #[0]) := by
  refine ⟨hsz, rfl, fun i hi => ?_, fun i hi hi0 => absurd hi (by simp at hi; omega),
    fun x hx hne => ?_, by simp, by simp⟩
  · have : i = 0 := by simpa using hi
    subst this
    have e : (#[m0] : Array Nat)[0]! = m0 := rfl
    show (#[m0] : Array Nat)[0]! < 1408 ∧ (A[0]!)[(#[m0] : Array Nat)[0]!]! = true ∧
      (A[(#[m0] : Array Nat)[0]!]!)[v]! = true ∧ P[(#[m0] : Array Nat)[0]!]! = 0
    rw [e]
    exact ⟨hm0, h0, hv, hp0⟩
  · change P[x]! ≠ 1408 at hne
    show P[x]! < (#[m0] : Array Nat).size ∧ (#[m0] : Array Nat)[P[x]!]! = x
    by_cases hx0 : x = m0
    · subst hx0
      rw [hp0]
      exact ⟨by simp, rfl⟩
    · rw [hpne x hx hx0] at hne
      exact absurd rfl hne

theorem muInit_base {A : Array Flags} {v : Nat} (m0 : Nat) (hm0 : m0 < 1408)
    (h0 : (A[0]!)[m0]! = true) (hv : (A[m0]!)[v]! = true) :
    MBase A v ((Array.replicate 1408 1408).set! m0 0, #[m0], #[0]) :=
  muInit_base' (by rw [Array.size_set!, Array.size_replicate]) hm0 h0 hv
    (Array.getElem!_set!_self _ _ _ (by rw [Array.size_replicate]; exact hm0))
    (fun x hx hx0 => by
      rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hx0 h.symm),
        getElem!_pos _ x (by rw [Array.size_replicate]; exact hx), Array.getElem_replicate])

theorem conn_all {V : Nat → Prop} {adjf : Nat → Nat → Prop} {m : Nat} {E : Nat → Nat}
    (hclosed : ∀ i < m, ∀ j < m, adjf (E i) (E j) → V (E i) → V (E j))
    (hsymm : ∀ i < m, ∀ j < m, adjf (E i) (E j) → adjf (E j) (E i))
    (hchain : ∀ i < m, 0 < i → ∃ j < i, adjf (E i) (E j))
    (h0 : ∃ i0 < m, V (E i0)) : ∀ i < m, V (E i) := by
  have key : ∀ n ≤ m, ∀ i < n, (V (E i) ↔ V (E 0)) := by
    intro n
    induction n with
    | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ n ih =>
      intro hn i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact ih (by omega) i hi
      · by_cases hi0 : i = 0
        · subst hi0
          exact Iff.rfl
        · obtain ⟨j, hj, hadj⟩ := hchain i (by omega) (by omega)
          have h1 := ih (by omega) j hj
          have h2 : V (E i) ↔ V (E j) :=
            ⟨hclosed i (by omega) j (by omega) hadj,
              hclosed j (by omega) i (by omega) (hsymm i (by omega) j (by omega) hadj)⟩
          exact h2.trans h1
  obtain ⟨i0, hi0, hV⟩ := h0
  have hV0 : V (E 0) := (key m (Nat.le_refl _) i0 hi0).1 hV
  intro i hi
  exact (key m (Nat.le_refl _) i hi).2 hV0

theorem muTree_fin (A : Array Flags) (v : Nat) (mu : Array Nat)
    (hmudef : mu = (filterRange (fun x => (A[0]!)[x]! && (A[x]!)[v]!) 1408 []).toArray)
    (hmu : 0 < mu.size) :
    let fin := Id.run (forIn [:1408]
      (((Array.replicate 1408 1408).set! mu[0]! 0, #[mu[0]!], #[0]) : MSt) (muOuter A mu))
    muTree A v = (fin.2.1, fin.2.2, fin.1) := by
  subst hmudef
  intro fin
  rw [muTree_eq A v hmu]
  rfl

theorem muTreeOK_of {A : Array Flags} {v m : Nat} {E : Nat → Nat}
    (hsym : ∀ x < 1408, ∀ y < 1408, (A[x]!)[y]! = (A[y]!)[x]!)
    (hm : m ≠ 0) (hE : ∀ i < m, E i < 1408)
    (hC : ∀ x, (x < 1408 ∧ (A[0]!)[x]! = true ∧ (A[x]!)[v]! = true) ↔ ∃ i < m, E i = x)
    (hchain : ∀ i < m, 0 < i → ∃ j < i, (A[E i]!)[E j]! = true) :
    muTreeOK A v (muTree A v) = true := by
  obtain ⟨mu, hmudef⟩ : ∃ mu : Array Nat,
      mu = (filterRange (fun x => (A[0]!)[x]! && (A[x]!)[v]!) 1408 []).toArray := ⟨_, rfl⟩
  have hmem : ∀ y, y ∈ mu.toList ↔ y < 1408 ∧ (A[0]!)[y]! = true ∧ (A[y]!)[v]! = true := by
    intro y
    rw [hmudef]
    exact mu_mem_iff A v y
  have hE0 : E 0 ∈ mu.toList := (hmem _).2 ((hC _).2 ⟨0, Nat.pos_of_ne_zero hm, rfl⟩)
  have hmupos : 0 < mu.size := by
    have := List.length_pos_of_mem hE0
    simpa using this
  have hm0mem : mu[0]! ∈ mu.toList := by
    rw [getElem!_pos mu 0 hmupos]
    exact Array.mem_def.1 (Array.getElem_mem hmupos)
  obtain ⟨hm01, hm02, hm03⟩ := (hmem _).1 hm0mem
  have hmu1 : ∀ y ∈ mu.toList, y < 1408 ∧ (A[0]!)[y]! = true ∧ (A[y]!)[v]! = true :=
    fun y hy => (hmem y).1 hy
  have hmu2 : ∀ y < 1408, (A[0]!)[y]! = true → (A[y]!)[v]! = true → y ∈ mu.toList :=
    fun y h1 h2 h3 => (hmem y).2 ⟨h1, h2, h3⟩
  have hinit := muInit_base (A := A) (v := v) mu[0]! hm01 hm02 hm03
  obtain ⟨hB, hP⟩ := muOuterLoop hinit mu hmu1 hmu2
  rw [muTree_fin A v mu hmudef hmupos]
  generalize Id.run (forIn [:1408]
    (((Array.replicate 1408 1408).set! mu[0]! 0, #[mu[0]!], #[0]) : MSt) (muOuter A mu)) = fin
    at hB hP ⊢
  have hclosed : ∀ x < 1408, fin.1[x]! ≠ 1408 → ∀ y < 1408, (A[0]!)[y]! = true →
      (A[y]!)[v]! = true → (A[x]!)[y]! = true → fin.1[y]! ≠ 1408 := by
    intro x hx hvx y hy hy0 hyv hadj
    obtain ⟨p1, p2⟩ := hB.posOK x hx hvx
    exact hP (fin.1[x]!) p1 p1 y hy hy0 hyv (by rw [p2]; exact hadj)
  obtain ⟨c1, c2, c3, c4⟩ := hB.ptsC 0 hB.sizePos
  have hV1 : fin.1[fin.2.1[0]!]! ≠ 1408 := by rw [c4]; omega
  obtain ⟨i0, hi0, hEi0⟩ := (hC fin.2.1[0]!).1 ⟨c1, c2, c3⟩
  have hallV : ∀ i < m, fin.1[E i]! ≠ 1408 := by
    refine conn_all (V := fun x => fin.1[x]! ≠ 1408) (adjf := fun x y => (A[x]!)[y]! = true)
      (m := m) (E := E) (fun i hi j hj hadj hv => ?_) (fun i hi j hj hadj => ?_) hchain
      ⟨i0, hi0, by simpa [hEi0] using hV1⟩
    · obtain ⟨e1, e2, e3⟩ := (hC (E j)).2 ⟨j, hj, rfl⟩
      exact hclosed (E i) (hE i hi) hv (E j) e1 e2 e3 hadj
    · exact (hsym (E j) (hE j hj) (E i) (hE i hi)).trans hadj
  have hvis : ∀ x < 1408, (A[0]!)[x]! = true → (A[x]!)[v]! = true → fin.1[x]! ≠ 1408 := by
    intro x hx h0 hv
    obtain ⟨i, hi, rfl⟩ := (hC x).1 ⟨hx, h0, hv⟩
    exact hallV i hi
  unfold muTreeOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allIn_iff', Bool.or_eq_true,
    Bool.not_eq_true']
  refine ⟨⟨⟨hB.sizePos, hB.parsz⟩, fun i _ hi => ?_⟩, fun i _ hi => ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hB.ptsC i hi
    refine ⟨⟨⟨a1, a2⟩, a3⟩, ?_⟩
    by_cases hi0 : i = 0
    · exact Or.inl hi0
    · exact Or.inr (hB.parOK i hi (by omega))
  · by_cases hC' : (A[0]!)[i]! = true ∧ (A[i]!)[v]! = true
    · right
      exact hB.posOK i hi (hvis i hi hC'.1 hC'.2)
    · left
      cases h0 : (A[0]!)[i]! <;> cases h1 : (A[i]!)[v]! <;> simp_all

end CFSG.KC.Misc.Xi

end
