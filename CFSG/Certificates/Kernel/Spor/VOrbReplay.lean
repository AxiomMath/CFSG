module

public import Certificates.Data.Kernel.Spor.VOrb
public import CFSG.Certificates.Kernel.Spor.TBfsSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.VOR

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.VO CFSG.KS.TBfs

theorem vstep_spec {PA LA : Nat → Nat} {h g c a : Nat} (hv : vstep PA LA h g c a ≠ 0) :
    c ≠ 0 ∧ ((a < c ∧ vstep PA LA h g c a = c) ∨
      (a = c ∧ r32 PA c = h ∧ r32 LA c = g ∧ vstep PA LA h g c a = c + 1)) := by
  unfold vstep at hv ⊢
  simp only [Raw.Orb.nIf_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hv ⊢
  by_cases h0 : c = 0
  · simp [h0] at hv
  refine ⟨h0, ?_⟩
  by_cases h1 : a < c
  · left
    simp [h0, h1]
  · right
    by_cases h2 : a = c ∧ r32 PA c = h ∧ r32 LA c = g
    · obtain ⟨e1, e2, e3⟩ := h2
      simp [h0, e1, e2, e3]
    · simp [h0, h1, h2] at hv

theorem cnt_zero (AL BE PA LA : Nat → Nat) : vorbCnt 0 AL BE PA LA = 1 := rfl

theorem cnt_succ (h : Nat) (AL BE PA LA : Nat → Nat) : vorbCnt (h + 1) AL BE PA LA =
    if h < vorbCnt h AL BE PA LA then
      vstep PA LA h 2 (vstep PA LA h 1 (vorbCnt h AL BE PA LA) (r32 AL h)) (r32 BE h)
    else 0 := by
  have e : vorbCnt (h + 1) AL BE PA LA = strictN (vorbCnt h AL BE PA LA) (fun c' =>
      Bool.rec (motive := fun _ => Nat) 0 (strictN (vstep PA LA h 1 c' (r32 AL h)) (fun c2 =>
        vstep PA LA h 2 c2 (r32 BE h))) (Nat.blt h c')) := rfl
  rw [e, Raw.Orb.strictN_eq, Raw.Orb.nIf_eq, Raw.Orb.strictN_eq]
  by_cases hh : h < vorbCnt h AL BE PA LA
  · have : Nat.blt h (vorbCnt h AL BE PA LA) = true := by rw [Nat.blt_eq]; exact hh
    simp only [this, hh, ↓reduceIte]
  · have : Nat.blt h (vorbCnt h AL BE PA LA) = false :=
      Bool.eq_false_iff.2 fun e => hh (by rw [Nat.blt_eq] at e; exact e)
    simp only [this, hh, ↓reduceIte, Bool.false_eq_true]

theorem vstep_zero (PA LA : Nat → Nat) (h g a : Nat) : vstep PA LA h g 0 a = 0 := rfl

theorem vstep_ge {PA LA : Nat → Nat} {h g c a : Nat} (hv : vstep PA LA h g c a ≠ 0) :
    c ≤ vstep PA LA h g c a ∧ vstep PA LA h g c a ≤ c + 1 := by
  rcases (vstep_spec hv).2 with ⟨-, e⟩ | ⟨-, -, -, e⟩ <;> omega

theorem cnt_facts {N : Nat} {AL BE PA LA : Nat → Nat} (hN : 0 < N)
    (hc : vorbCnt N AL BE PA LA = N) :
    (∀ h ≤ N, vorbCnt h AL BE PA LA ≠ 0 ∧ vorbCnt h AL BE PA LA ≤ N) ∧
      ∀ h < N, h < vorbCnt h AL BE PA LA := by
  have hz : ∀ h, vorbCnt h AL BE PA LA = 0 → vorbCnt (h + 1) AL BE PA LA = 0 := by
    intro h e
    rw [cnt_succ, e]
    simp
  have hnz : ∀ h ≤ N, vorbCnt h AL BE PA LA ≠ 0 := by
    intro h hh e
    have : ∀ j, vorbCnt (h + j) AL BE PA LA = 0 := by
      intro j
      induction j with
      | zero => exact e
      | succ j ih => exact hz _ ih
    have := this (N - h)
    rw [Nat.add_sub_cancel' hh, hc] at this
    omega
  have hmono : ∀ h < N, vorbCnt h AL BE PA LA ≤ vorbCnt (h + 1) AL BE PA LA ∧
      h < vorbCnt h AL BE PA LA := by
    intro h hh
    have h1 := hnz (h + 1) (by omega)
    rw [cnt_succ] at h1
    by_cases hlt : h < vorbCnt h AL BE PA LA
    · refine ⟨?_, hlt⟩
      rw [cnt_succ]
      simp only [hlt, ↓reduceIte] at h1 ⊢
      have a2 := vstep_ge h1
      have a1 := vstep_ge (h := h) (g := 1) (c := vorbCnt h AL BE PA LA) (a := r32 AL h)
        (PA := PA) (LA := LA) (fun e => h1 (by rw [e]; exact vstep_zero _ _ _ _ _))
      omega
    · simp only [hlt, ↓reduceIte] at h1
      exact absurd rfl h1
  refine ⟨fun h hh => ⟨hnz h hh, ?_⟩, fun h hh => (hmono h hh).2⟩
  have : ∀ j, h + j ≤ N → vorbCnt h AL BE PA LA ≤ vorbCnt (h + j) AL BE PA LA := by
    intro j
    induction j with
    | zero => intro _; exact Nat.le_refl _
    | succ j ih =>
      intro hj
      exact Nat.le_trans (ih (by omega)) (hmono (h + j) (by omega)).1
  have := this (N - h) (by omega)
  rw [Nat.add_sub_cancel' hh, hc] at this
  exact this

theorem tree_facts {N : Nat} {AL BE PA LA : Nat → Nat} (hN : 0 < N)
    (hc : vorbCnt N AL BE PA LA = N) :
    ∀ i, 0 < i → i < N → r32 PA i < i ∧ ((r32 LA i = 1 ∧ r32 AL (r32 PA i) = i) ∨
      (r32 LA i = 2 ∧ r32 BE (r32 PA i) = i)) := by
  obtain ⟨hcn, hlt⟩ := cnt_facts hN hc
  have key : ∀ h ≤ N, ∀ i, 0 < i → i < vorbCnt h AL BE PA LA → r32 PA i < i ∧
      ((r32 LA i = 1 ∧ r32 AL (r32 PA i) = i) ∨ (r32 LA i = 2 ∧ r32 BE (r32 PA i) = i)) := by
    intro h
    induction h with
    | zero =>
      intro _ i hi hi'
      rw [cnt_zero] at hi'
      omega
    | succ h ih =>
      intro hh i hi hi'
      have hl := hlt h (by omega)
      have h1 := (hcn (h + 1) hh).1
      simp only [cnt_succ, hl, ↓reduceIte] at h1 hi'
      generalize hc0 : vorbCnt h AL BE PA LA = c at hl h1 hi'
      have hv1 : vstep PA LA h 1 c (r32 AL h) ≠ 0 :=
        fun e => h1 (by rw [e]; exact vstep_zero _ _ _ _ _)
      have s1 := (vstep_spec hv1).2
      have s2 := (vstep_spec h1).2
      generalize hc1 : vstep PA LA h 1 c (r32 AL h) = c1 at h1 hi' s1 s2
      rcases s1 with ⟨-, e1⟩ | ⟨ea, ep, el, e1⟩ <;>
        rcases s2 with ⟨-, e2⟩ | ⟨eb, eq, el2, e2⟩
      · rw [e2, e1] at hi'
        exact ih (by omega) i hi (by rw [hc0]; exact hi')
      · rw [e2] at hi'
        by_cases hic : i < c
        · exact ih (by omega) i hi (by rw [hc0]; exact hic)
        · have : i = c1 := by omega
          subst this
          refine ⟨by omega, Or.inr ⟨el2, by rw [eq, eb]⟩⟩
      · rw [e2, e1] at hi'
        by_cases hic : i < c
        · exact ih (by omega) i hi (by rw [hc0]; exact hic)
        · have : i = c := by omega
          subst this
          refine ⟨by omega, Or.inl ⟨el, by rw [ep, ea]⟩⟩
      · rw [e2] at hi'
        by_cases hic : i < c
        · exact ih (by omega) i hi (by rw [hc0]; exact hic)
        · by_cases hic' : i = c
          · subst hic'
            refine ⟨by omega, Or.inl ⟨el, by rw [ep, ea]⟩⟩
          · have : i = c1 := by omega
            subst this
            refine ⟨by omega, Or.inr ⟨el2, by rw [eq, eb]⟩⟩
  intro i hi hiN
  exact key N (Nat.le_refl _) i hi (by rw [hc]; exact hiN)

@[expose] def ArrEq {β : Type} [Inhabited β] (a : Array β) (n : Nat) (f : Nat → β) : Prop :=
  a.size = n ∧ ∀ i < n, a[i]! = f i

theorem ArrEq.push {β : Type} [Inhabited β] {a : Array β} {n : Nat} {f : Nat → β} {x : β}
    (h : ArrEq a n f) (hx : x = f n) : ArrEq (a.push x) (n + 1) f := by
  refine ⟨by rw [Array.size_push, h.1], fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
  · rw [push_lt (by rw [h.1]; exact hi), h.2 i hi]
  · rw [← h.1, push_eq, hx, h.1]

theorem ArrEq.eq_ofFn {β : Type} [Inhabited β] {a : Array β} {n : Nat} {f : Nat → β}
    (h : ArrEq a n f) : a = Array.ofFn (n := n) fun i => f i.val := by
  apply Array.ext (by simp [h.1])
  intro i h1 h2
  rw [Array.getElem_ofFn, ← getElem!_pos a i h1, h.2 i (by rw [← h.1]; exact h1)]

theorem arrEq_one {β : Type} [Inhabited β] {f : Nat → β} {x : β} (hx : x = f 0) :
    ArrEq #[x] 1 f := by
  refine ⟨rfl, fun i hi => ?_⟩
  have : i = 0 := by omega
  subst this
  exact hx

theorem arrEq_nil {β : Type} [Inhabited β] (f : Nat → β) : ArrEq (#[] : Array β) 0 f :=
  ⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

variable {α κ : Type} [Inhabited α] [BEq κ] [Hashable κ] [LawfulBEq κ]

structure HInv (T : Nat → α) (k : α → κ) (c : Nat) (idx : Std.HashMap κ Nat) (pts : Array α) :
    Prop where
  size : pts.size = c
  get : ∀ i < c, pts[i]! = T i
  found : ∀ j < c, idx[k (T j)]? = some j
  sound : ∀ x j, idx[x]? = some j → j < c ∧ k (T j) = x

theorem hinv_init (T : Nat → α) (k : α → κ) :
    HInv T k 1 ((∅ : Std.HashMap κ Nat).insert (k (T 0)) 0) #[T 0] := by
  refine ⟨rfl, fun i hi => ?_, fun j hj => ?_, fun x j hx => ?_⟩
  · have : i = 0 := by omega
    subst this
    rfl
  · have : j = 0 := by omega
    subst this
    simp
  · rw [Std.HashMap.getElem?_insert] at hx
    split at hx
    · next he =>
      cases hx
      exact ⟨by omega, eq_of_beq he⟩
    · simp at hx

theorem look_step {T : Nat → α} {k : α → κ} {N c a : Nat} {idx : Std.HashMap κ Nat}
    {pts : Array α} (hinj : ∀ i < N, ∀ j < N, k (T i) = k (T j) → i = j) (hcN : c ≤ N)
    (I : HInv T k c idx pts) (ha : a < N) :
    (a < c → idx[k (T a)]? = some a) ∧
      (a = c → idx[k (T a)]? = none ∧
        HInv T k (c + 1) (idx.insert (k (T a)) pts.size) (pts.push (T a))) := by
  refine ⟨fun h => I.found a h, fun h => ?_⟩
  subst h
  have hnone : idx[k (T a)]? = none := by
    cases e : idx[k (T a)]? with
    | none => rfl
    | some j =>
      obtain ⟨hj, hk⟩ := I.sound _ _ e
      have := hinj j (by omega) a ha hk
      omega
  refine ⟨hnone, ⟨by rw [Array.size_push, I.size], fun i hi => ?_, fun j hj => ?_,
    fun x j hx => ?_⟩⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [push_lt (by rw [I.size]; exact hi), I.get i hi]
    · rw [← I.size, push_eq]
  · rw [Std.HashMap.getElem?_insert, I.size]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · have hne : (k (T a) == k (T j)) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        have := hinj a ha j (by omega) e
        omega
      rw [hne]
      exact I.found j hj
    · simp
  · rw [Std.HashMap.getElem?_insert, I.size] at hx
    split at hx
    · next he =>
      cases hx
      exact ⟨by omega, eq_of_beq he⟩
    · obtain ⟨h1, h2⟩ := I.sound x j hx
      exact ⟨by omega, h2⟩

theorem vindex_get {pts : Array α} {k : α → κ}
    (hinj : ∀ i < pts.size, ∀ j < pts.size, k pts[i]! = k pts[j]! → i = j) :
    ∀ i < pts.size, ((List.range pts.size).foldl (fun m i => m.insert (k pts[i]!) i)
      (∅ : Std.HashMap κ Nat))[k pts[i]!]? = some i := by
  have step : ∀ m ≤ pts.size, ∀ i < m,
      ((List.range m).foldl (fun m i => m.insert (k pts[i]!) i)
        (∅ : Std.HashMap κ Nat))[k pts[i]!]? = some i := by
    intro m
    induction m with
    | zero => intro _ i hi; omega
    | succ m ih =>
      intro hm i hi
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Std.HashMap.getElem?_insert]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · have hne : (k pts[m]! == k pts[i]!) = false := by
          rw [beq_eq_false_iff_ne]
          intro e
          have := hinj m (by omega) i (by omega) e
          omega
        rw [hne]
        exact ih (by omega) i hi
      · simp
  exact fun i hi => step pts.size (Nat.le_refl _) i hi

end CFSG.KS.VOR

end
