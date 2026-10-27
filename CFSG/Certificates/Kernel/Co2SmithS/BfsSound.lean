module

public import Certificates.Data.Kernel.Co2SmithS.Replay
public import Certificates.Data.CFSGNative.Co2Smith.Check
public import CFSG.Certificates.Kernel.Spor.VOrbReplay

public section

namespace CFSG.KC.Co2SmithS

open CFSG.KS.TBfs CFSG.Sporadic.Co2Smith.Native

@[expose] def gbfs {α : Type} [Inhabited α] (key : α → Nat) (step : Nat → α → α) (ngen : Nat)
    (start : α) (cap : Nat) : Array α × Array Nat × Array Nat := Id.run do
  let mut seen : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert (key start) 0
  let mut pts : Array α := #[start]
  let mut par : Array Nat := #[0]
  let mut let_ : Array Nat := #[0]
  let mut i := 0
  for _ in [0:cap] do
    if i < pts.size then
      let x := pts[i]!
      for l in [0:ngen] do
        let y := step l x
        let e := key y
        if !seen.contains e then
          seen := seen.insert e pts.size
          pts := pts.push y
          par := par.push i
          let_ := let_.push l
      i := i + 1
  return (pts, par, let_)

theorem classBFS_eq (seeds : Array (Array Nat)) (X0 : Array Nat) (cap : Nat) :
    classBFS seeds X0 cap = gbfs encM (conjSeed seeds) 2 X0 cap := rfl

theorem orbitBFS_eq (step : Nat → Nat → Nat) (ngen start cap : Nat) :
    orbitBFS step ngen start cap = gbfs id step ngen start cap := rfl

abbrev ISt (α : Type) := Std.HashMap Nat Nat × Array α × Array Nat × Array Nat

abbrev OSt (α : Type) := Std.HashMap Nat Nat × Array α × Array Nat × Array Nat × Nat

@[expose] def ib {α : Type} (key : α → Nat) (step : Nat → α → α) (x : α) (i l : Nat)
    (s : ISt α) : Id (ForInStep (ISt α)) :=
  if (!s.1.contains (key (step l x))) = true then
    pure (ForInStep.yield (s.1.insert (key (step l x)) s.2.1.size, s.2.1.push (step l x),
      s.2.2.1.push i, s.2.2.2.push l))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def ob {α : Type} [Inhabited α] (key : α → Nat) (step : Nat → α → α) (ngen : Nat)
    (_j : Nat) (s : OSt α) : Id (ForInStep (OSt α)) :=
  if s.2.2.2.2 < s.2.1.size then
    pure (ForInStep.yield (
      (Id.run (forIn (List.range' 0 ngen) (s.1, s.2.1, s.2.2.1, s.2.2.2.1)
        (ib key step s.2.1[s.2.2.2.2]! s.2.2.2.2))).1,
      (Id.run (forIn (List.range' 0 ngen) (s.1, s.2.1, s.2.2.1, s.2.2.2.1)
        (ib key step s.2.1[s.2.2.2.2]! s.2.2.2.2))).2.1,
      (Id.run (forIn (List.range' 0 ngen) (s.1, s.2.1, s.2.2.1, s.2.2.2.1)
        (ib key step s.2.1[s.2.2.2.2]! s.2.2.2.2))).2.2.1,
      (Id.run (forIn (List.range' 0 ngen) (s.1, s.2.1, s.2.2.1, s.2.2.2.1)
        (ib key step s.2.1[s.2.2.2.2]! s.2.2.2.2))).2.2.2, s.2.2.2.2 + 1))
  else pure (ForInStep.yield s)

theorem gbfs_eq {α : Type} [Inhabited α] (key : α → Nat) (step : Nat → α → α) (ngen : Nat)
    (start : α) (cap : Nat) : gbfs key step ngen start cap =
      ((Id.run (forIn (List.range' 0 cap)
        (((∅ : Std.HashMap Nat Nat).insert (key start) 0, #[start], #[0], #[0], 0) : OSt α)
        (ob key step ngen))).2.1,
      (Id.run (forIn (List.range' 0 cap)
        (((∅ : Std.HashMap Nat Nat).insert (key start) 0, #[start], #[0], #[0], 0) : OSt α)
        (ob key step ngen))).2.2.1,
      (Id.run (forIn (List.range' 0 cap)
        (((∅ : Std.HashMap Nat Nat).insert (key start) 0, #[start], #[0], #[0], 0) : OSt α)
        (ob key step ngen))).2.2.2.1) := by
  unfold gbfs
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem stepC_spec {PA LA : Nat → Nat} {h l c a : Nat} (hv : stepC PA LA h l c a ≠ 0) :
    c ≠ 0 ∧ ((a < c ∧ stepC PA LA h l c a = c) ∨
      (a = c ∧ PA c = h ∧ LA c = l ∧ stepC PA LA h l c a = c + 1)) := by
  unfold stepC at hv ⊢
  by_cases h0 : c = 0
  · simp [h0] at hv
  refine ⟨h0, ?_⟩
  by_cases h1 : a < c
  · left
    simp [h0, h1]
  · right
    by_cases h2 : a = c ∧ PA c = h ∧ LA c = l
    · obtain ⟨e1, e2, e3⟩ := h2
      simp [h0, e1, e2, e3]
    · simp [h0, h1, h2] at hv

theorem stepC_zero (PA LA : Nat → Nat) (h l a : Nat) : stepC PA LA h l 0 a = 0 := by
  simp [stepC]

theorem stepC_ge {PA LA : Nat → Nat} {h l c a : Nat} (hv : stepC PA LA h l c a ≠ 0) :
    c ≤ stepC PA LA h l c a := by
  rcases (stepC_spec hv).2 with ⟨-, e⟩ | ⟨-, -, -, e⟩ <;> omega

@[expose] def pcC (PA LA : Nat → Nat) (TB : Nat → Nat → Nat) (h c j : Nat) : Nat :=
  (List.range j).foldl (fun c l => stepC PA LA h l c (TB h l)) c

theorem pcC_succ (PA LA : Nat → Nat) (TB : Nat → Nat → Nat) (h c j : Nat) :
    pcC PA LA TB h c (j + 1) = stepC PA LA h j (pcC PA LA TB h c j) (TB h j) := by
  simp [pcC, List.range_succ, List.foldl_append]

theorem pcC_le {PA LA : Nat → Nat} {TB : Nat → Nat → Nat} {h c : Nat} :
    ∀ k j, pcC PA LA TB h c (j + k) ≠ 0 →
      pcC PA LA TB h c j ≠ 0 ∧ pcC PA LA TB h c j ≤ pcC PA LA TB h c (j + k)
  | 0, j, hv => ⟨hv, Nat.le_refl _⟩
  | k + 1, j, hv => by
    rw [← Nat.add_assoc, pcC_succ] at hv
    have hz : pcC PA LA TB h c (j + k) ≠ 0 := fun e => hv (by rw [e, stepC_zero])
    obtain ⟨h1, h2⟩ := pcC_le k j hz
    refine ⟨h1, Nat.le_trans h2 ?_⟩
    rw [← Nat.add_assoc, pcC_succ]
    exact stepC_ge hv

theorem rowC_ge {PA LA : Nat → Nat} {TB : Nat → Nat → Nat} {ngen h c : Nat}
    (hv : rowC PA LA TB ngen h c ≠ 0) : c ≠ 0 ∧ c ≤ rowC PA LA TB ngen h c := by
  have e : rowC PA LA TB ngen h c = pcC PA LA TB h c (0 + ngen) := by
    rw [Nat.zero_add]
    rfl
  rw [e] at hv ⊢
  exact pcC_le ngen 0 hv

structure Counts (PA LA M : Nat → Nat) (TB : Nat → Nat → Nat) (ngen N : Nat) : Prop where
  pos : 0 < N
  zero : M 0 = 1
  succ : ∀ h < N, M (h + 1) = if h < M h then rowC PA LA TB ngen h (M h) else 0
  last : M N = N

theorem Counts.facts {PA LA M : Nat → Nat} {TB : Nat → Nat → Nat} {ngen N : Nat}
    (C : Counts PA LA M TB ngen N) :
    (∀ h ≤ N, M h ≠ 0 ∧ M h ≤ N) ∧ ∀ h < N, h < M h ∧ M (h + 1) = rowC PA LA TB ngen h (M h) := by
  have hz : ∀ h < N, M h = 0 → M (h + 1) = 0 := by
    intro h hh e
    rw [C.succ h hh, e]
    simp
  have hnz : ∀ h ≤ N, M h ≠ 0 := by
    intro h hh e
    have : ∀ j, h + j ≤ N → M (h + j) = 0 := by
      intro j
      induction j with
      | zero => intro _; exact e
      | succ j ih =>
        intro hj
        exact hz (h + j) (by omega) (ih (by omega))
    have := this (N - h) (by omega)
    rw [Nat.add_sub_cancel' hh, C.last] at this
    exact absurd this (by have := C.pos; omega)
  have hstep : ∀ h < N, h < M h ∧ M (h + 1) = rowC PA LA TB ngen h (M h) ∧ M h ≤ M (h + 1) := by
    intro h hh
    have h1 := hnz (h + 1) (by omega)
    rw [C.succ h hh] at h1
    by_cases hlt : h < M h
    · simp only [hlt, ↓reduceIte] at h1
      refine ⟨hlt, by rw [C.succ h hh]; simp [hlt], ?_⟩
      rw [C.succ h hh]
      simp only [hlt, ↓reduceIte]
      exact (rowC_ge h1).2
    · simp [hlt] at h1
  refine ⟨fun h hh => ⟨hnz h hh, ?_⟩, fun h hh => ⟨(hstep h hh).1, (hstep h hh).2.1⟩⟩
  have : ∀ j, h + j ≤ N → M h ≤ M (h + j) := by
    intro j
    induction j with
    | zero => intro _; exact Nat.le_refl _
    | succ j ih => intro hj; exact Nat.le_trans (ih (by omega)) (hstep (h + j) (by omega)).2.2
  have := this (N - h) (by omega)
  rw [Nat.add_sub_cancel' hh, C.last] at this
  exact this

variable {α : Type} [Inhabited α]

structure Inv (T : Nat → α) (key : α → Nat) (PA LA : Nat → Nat) (c : Nat) (s : ISt α) : Prop where
  idx : CFSG.KS.VOR.HInv T key c s.1 s.2.1
  par : CFSG.KS.VOR.ArrEq s.2.2.1 c PA
  lab : CFSG.KS.VOR.ArrEq s.2.2.2 c LA

theorem ib_step {key : α → Nat} {step : Nat → α → α} {T : Nat → α} {PA LA : Nat → Nat}
    {N h l c a : Nat} {s : ISt α} (hinj : ∀ i < N, ∀ j < N, key (T i) = key (T j) → i = j)
    (hcN : c ≤ N) (I : Inv T key PA LA c s) (haN : a < N) (hy : step l (T h) = T a)
    (hv : stepC PA LA h l c a ≠ 0) :
    ∃ s', ib key step (T h) h l s = pure (ForInStep.yield s') ∧
      Inv T key PA LA (stepC PA LA h l c a) s' := by
  have L := CFSG.KS.VOR.look_step hinj hcN I.idx haN
  unfold ib
  rw [hy]
  rcases (stepC_spec hv).2 with ⟨hlt, e⟩ | ⟨heq, hpa, hla, e⟩
  · have hc : s.1.contains (key (T a)) = true := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, L.1 hlt]
      rfl
    rw [e, hc]
    exact ⟨_, rfl, I⟩
  · obtain ⟨hn, I'⟩ := L.2 heq
    have hc : s.1.contains (key (T a)) = false := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, hn]
      rfl
    rw [e, hc]
    refine ⟨_, rfl, ⟨I', I.par.push hpa.symm, I.lab.push hla.symm⟩⟩

theorem inner_run {key : α → Nat} {step : Nat → α → α} {T : Nat → α} {PA LA : Nat → Nat}
    {TB : Nat → Nat → Nat} {ngen N h c : Nat} {s : ISt α}
    (hinj : ∀ i < N, ∀ j < N, key (T i) = key (T j) → i = j)
    (hpt : ∀ l < ngen, TB h l < N ∧ step l (T h) = T (TB h l))
    (hr : rowC PA LA TB ngen h c ≠ 0) (hrN : rowC PA LA TB ngen h c ≤ N)
    (I : Inv T key PA LA c s) :
    Inv T key PA LA (rowC PA LA TB ngen h c)
      (Id.run (forIn (List.range' 0 ngen) s (ib key step (T h) h))) := by
  have hre : rowC PA LA TB ngen h c = pcC PA LA TB h c ngen := rfl
  rw [hre] at hr hrN ⊢
  refine forIn_range'_done ngen 0 s _
    (fun j b => j ≤ ngen ∧ Inv T key PA LA (pcC PA LA TB h c j) b)
    (Inv T key PA LA (pcC PA LA TB h c ngen)) (fun j hj b hb => ?_) (fun b hb => hb.2)
    ⟨Nat.zero_le _, I⟩
  left
  obtain ⟨-, J⟩ := hb
  have hv : stepC PA LA h j (pcC PA LA TB h c j) (TB h j) ≠ 0 := by
    rw [← pcC_succ]
    have := pcC_le (PA := PA) (LA := LA) (TB := TB) (h := h) (c := c) (ngen - (j + 1)) (j + 1)
      (by rw [Nat.add_sub_cancel' (by omega)]; exact hr)
    exact this.1
  have hle : pcC PA LA TB h c j ≤ N := by
    have := pcC_le (PA := PA) (LA := LA) (TB := TB) (h := h) (c := c) (ngen - j) j
      (by rw [Nat.add_sub_cancel' (by omega)]; exact hr)
    rw [Nat.add_sub_cancel' (by omega)] at this
    omega
  obtain ⟨haN, hy⟩ := hpt j hj
  obtain ⟨s', e, J'⟩ := ib_step hinj hle J haN hy hv
  rw [Nat.zero_add]
  exact ⟨s', e, by omega, by rw [pcC_succ]; exact J'⟩

theorem gbfs_of {key : α → Nat} {step : Nat → α → α} {T : Nat → α} {PA LA M : Nat → Nat}
    {TB : Nat → Nat → Nat} {ngen N cap : Nat} (hcap : N ≤ cap)
    (hinj : ∀ i < N, ∀ j < N, key (T i) = key (T j) → i = j)
    (hpt : ∀ i < N, ∀ l < ngen, TB i l < N ∧ step l (T i) = T (TB i l))
    (C : Counts PA LA M TB ngen N) (hpa0 : PA 0 = 0) (hla0 : LA 0 = 0) :
    gbfs key step ngen (T 0) cap = (Array.ofFn (n := N) fun i => T i.val,
      Array.ofFn (n := N) fun i => PA i.val, Array.ofFn (n := N) fun i => LA i.val) := by
  obtain ⟨hcn, hlt⟩ := C.facts
  have hfin : (Id.run (forIn (List.range' 0 cap)
      (((∅ : Std.HashMap Nat Nat).insert (key (T 0)) 0, #[T 0], #[0], #[0], 0) : OSt α)
      (ob key step ngen))).2.2.2.2 = N ∧ Inv T key PA LA N
      ((Id.run (forIn (List.range' 0 cap)
        (((∅ : Std.HashMap Nat Nat).insert (key (T 0)) 0, #[T 0], #[0], #[0], 0) : OSt α)
        (ob key step ngen))).1,
      (Id.run (forIn (List.range' 0 cap)
        (((∅ : Std.HashMap Nat Nat).insert (key (T 0)) 0, #[T 0], #[0], #[0], 0) : OSt α)
        (ob key step ngen))).2.1,
      (Id.run (forIn (List.range' 0 cap)
        (((∅ : Std.HashMap Nat Nat).insert (key (T 0)) 0, #[T 0], #[0], #[0], 0) : OSt α)
        (ob key step ngen))).2.2.1,
      (Id.run (forIn (List.range' 0 cap)
        (((∅ : Std.HashMap Nat Nat).insert (key (T 0)) 0, #[T 0], #[0], #[0], 0) : OSt α)
        (ob key step ngen))).2.2.2.1) := by
    refine forIn_range'_done cap 0 _ _
      (fun j (b : OSt α) => b.2.2.2.2 = min j N ∧
        Inv T key PA LA (M (min j N)) (b.1, b.2.1, b.2.2.1, b.2.2.2.1))
      (fun (b : OSt α) => b.2.2.2.2 = N ∧ Inv T key PA LA N (b.1, b.2.1, b.2.2.1, b.2.2.2.1))
      (fun j _ b hb => ?_) (fun b hb => ?_) ⟨by simp, ?_⟩
    · left
      obtain ⟨hi, J⟩ := hb
      rw [Nat.zero_add]
      rcases Nat.lt_or_ge j N with hj | hj
      · have hm : min j N = j := Nat.min_eq_left (by omega)
        have hm1 : min (j + 1) N = j + 1 := Nat.min_eq_left (by omega)
        rw [hm] at hi J
        obtain ⟨hjM, hrow⟩ := hlt j hj
        have hsz : b.2.2.2.2 < b.2.1.size := by rw [hi, J.idx.size]; exact hjM
        have hx : b.2.1[b.2.2.2.2]! = T j := by rw [hi]; exact J.idx.get j hjM
        have hI := inner_run (step := step) hinj (hpt j hj)
          (by rw [← hrow]; exact (hcn (j + 1) (by omega)).1)
          (by rw [← hrow]; exact (hcn (j + 1) (by omega)).2) J
        refine ⟨((Id.run (forIn (List.range' 0 ngen) (b.1, b.2.1, b.2.2.1, b.2.2.2.1)
            (ib key step (T j) j))).1,
          (Id.run (forIn (List.range' 0 ngen) (b.1, b.2.1, b.2.2.1, b.2.2.2.1)
            (ib key step (T j) j))).2.1,
          (Id.run (forIn (List.range' 0 ngen) (b.1, b.2.1, b.2.2.1, b.2.2.2.1)
            (ib key step (T j) j))).2.2.1,
          (Id.run (forIn (List.range' 0 ngen) (b.1, b.2.1, b.2.2.1, b.2.2.2.1)
            (ib key step (T j) j))).2.2.2, j + 1), ?_, hm1.symm, ?_⟩
        · unfold ob
          rw [if_pos hsz, hx, hi]
        · rw [hm1, hrow]
          exact hI
      · have hm : min j N = N := Nat.min_eq_right hj
        have hm1 : min (j + 1) N = N := Nat.min_eq_right (by omega)
        rw [hm] at hi J
        rw [C.last] at J
        have hsz : ¬ b.2.2.2.2 < b.2.1.size := by rw [hi, J.idx.size]; omega
        refine ⟨b, ?_, ?_⟩
        · unfold ob
          rw [if_neg hsz]
        · rw [hm1, C.last]
          exact ⟨hi, J⟩
    · obtain ⟨hi, J⟩ := hb
      rw [Nat.min_eq_right hcap] at hi J
      rw [C.last] at J
      exact ⟨hi, J⟩
    · simp only [Nat.zero_min]
      rw [C.zero]
      exact ⟨CFSG.KS.VOR.hinv_init T key, CFSG.KS.VOR.arrEq_one (by rw [hpa0]),
        CFSG.KS.VOR.arrEq_one (by rw [hla0])⟩
  rw [gbfs_eq]
  obtain ⟨-, I, hpar, hlab⟩ := hfin
  dsimp only at I hpar hlab
  rw [CFSG.KS.VOR.ArrEq.eq_ofFn ⟨I.size, I.get⟩, hpar.eq_ofFn, hlab.eq_ofFn]

end CFSG.KC.Co2SmithS

end
