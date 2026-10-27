module

public import CFSG.Certificates.Kernel.SporSch.KeyBfsSound

public section

namespace CFSG.KS.KeyBfs

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

structure ClosedRec (n k : Nat) (st : Nat → Table → Table) (root : Table) (Good : Table → Prop)
    (E : Array Table) (par lab : Array Nat) : Prop where
  pos : 0 < E.size
  par_size : par.size = E.size
  lab_size : lab.size = E.size
  root_eq : E[0]! = root
  good : ∀ i < E.size, Good E[i]!
  inj : ∀ a < E.size, ∀ b < E.size, key n E[a]! = key n E[b]! → a = b
  tree : ∀ i, 0 < i → i < E.size → par[i]! < i ∧ lab[i]! < k ∧ E[i]! = st lab[i]! E[par[i]!]!
  close : ∀ i < E.size, ∀ l < k, ∃ q < E.size, key n (st l E[i]!) = key n E[q]!

@[expose] def CInv (n k : Nat) (st : Nat → Table → Table) (root : Table) (Good : Table → Prop)
    (h j : Nat) (s : St) : Prop :=
  0 < s.2.1.size ∧ s.2.2.1.size = s.2.1.size ∧ s.2.2.2.size = s.2.1.size ∧ s.2.1[0]! = root ∧
    (∀ i < s.2.1.size, Good s.2.1[i]!) ∧
    (∀ a < s.2.1.size, ∀ b < s.2.1.size, key n s.2.1[a]! = key n s.2.1[b]! → a = b) ∧
    (∀ x, s.1.contains x = true ↔ ∃ i < s.2.1.size, key n s.2.1[i]! = x) ∧
    (∀ i, 0 < i → i < s.2.1.size → s.2.2.1[i]! < i ∧ s.2.2.2[i]! < k ∧
      s.2.1[i]! = st s.2.2.2[i]! s.2.1[s.2.2.1[i]!]!) ∧
    (∀ i < s.2.1.size, ∀ l < k, (i < h ∨ (i = h ∧ l < j)) →
      ∃ q < s.2.1.size, key n (st l s.2.1[i]!) = key n s.2.1[q]!)

section

variable {n k : Nat} {st : Nat → Table → Table} {root : Table} {Good : Table → Prop}
  {K : Finset Nat}

theorem size_le_card (hK : ∀ T, Good T → key n T ∈ K) {E : Array Table}
    (hg : ∀ i < E.size, Good E[i]!)
    (hi : ∀ a < E.size, ∀ b < E.size, key n E[a]! = key n E[b]! → a = b) : E.size ≤ K.card := by
  have h := Finset.card_le_card_of_injOn (s := Finset.range E.size) (t := K)
    (fun i => key n E[i]!) (fun i hi' => hK _ (hg i (Finset.mem_range.1 hi')))
    (fun a ha b hb e => hi a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) e)
  simpa using h

theorem cinv_init (hroot : Good root) : CInv n k st root Good 0 0 (initSt n root) := by
  refine ⟨by simp [initSt], rfl, rfl, by simp [initSt], fun i hi => ?_, fun a ha b hb _ => ?_,
    fun x => ?_, fun i h0 hi => ?_, fun i hi l _ hor => ?_⟩
  · have : i = 0 := by simp [initSt] at hi; omega
    subst this
    simpa [initSt] using hroot
  · simp [initSt] at ha hb
    omega
  · simp only [initSt]
    rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
    constructor
    · intro e
      exact ⟨0, by simp, by simpa using beq_iff_eq.1 e⟩
    · rintro ⟨i, hi, e⟩
      have : i = 0 := by simp at hi; omega
      subst this
      rw [← e]
      simp
  · simp [initSt] at hi
    omega
  · omega

theorem cinv_inner_step (hstep : ∀ l < k, ∀ T, Good T → Good (st l T)) {h j : Nat} {s : St}
    (hj : j < k) (hI : CInv n k st root Good h j s) (hh : h < s.2.1.size) :
    ∃ s', innerBody n st s.2.1[h]! h j s = pure (ForInStep.yield s') ∧
      CInv n k st root Good h (j + 1) s' ∧ s.2.1.size ≤ s'.2.1.size ∧
      s'.2.1[h]! = s.2.1[h]! := by
  obtain ⟨hpos, hp, hl, hr, hg, hinj, hK, htr, hcl⟩ := hI
  by_cases hnew : s.1.contains (key n (st j s.2.1[h]!)) = true
  · refine ⟨(s.1, s.2.1, s.2.2.1, s.2.2.2), by simp [innerBody, hnew],
      ⟨hpos, hp, hl, hr, hg, hinj, hK, htr, fun i hi l hlk hor => ?_⟩, Nat.le_refl _, rfl⟩
    rcases hor with a | ⟨rfl, a⟩
    · exact hcl i hi l hlk (Or.inl a)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 a with a | rfl
      · exact hcl i hi l hlk (Or.inr ⟨rfl, a⟩)
      · obtain ⟨q, hq, e⟩ := (hK _).1 hnew
        exact ⟨q, hq, e.symm⟩
  · have hnc : s.1.contains (key n (st j s.2.1[h]!)) = false := Bool.eq_false_iff.2 hnew
    have hbody : innerBody n st s.2.1[h]! h j s = pure (ForInStep.yield
        (s.1.insert (key n (st j s.2.1[h]!)), s.2.1.push (st j s.2.1[h]!), s.2.2.1.push h,
          s.2.2.2.push j)) := by
      unfold innerBody
      rw [hnc]
      rfl
    have hTg : Good (st j s.2.1[h]!) := hstep j hj _ (hg h hh)
    generalize hT : st j s.2.1[h]! = T at hnc hbody hTg
    have g1 : ∀ i < s.2.1.size, (s.2.1.push T)[i]! = s.2.1[i]! := fun i hi => push_lt hi
    have g2 : (s.2.1.push T)[s.2.1.size]! = T := push_eq
    have p1 : ∀ i < s.2.1.size, (s.2.2.1.push h)[i]! = s.2.2.1[i]! := fun i hi =>
      push_lt (by rw [hp]; exact hi)
    have p2 : (s.2.2.1.push h)[s.2.1.size]! = h := by rw [← hp]; exact push_eq
    have l1 : ∀ i < s.2.1.size, (s.2.2.2.push j)[i]! = s.2.2.2[i]! := fun i hi =>
      push_lt (by rw [hl]; exact hi)
    have l2 : (s.2.2.2.push j)[s.2.1.size]! = j := by rw [← hl]; exact push_eq
    have hfresh : ∀ i < s.2.1.size, key n s.2.1[i]! ≠ key n T := fun i hi e => by
      rw [(hK _).2 ⟨i, hi, e⟩] at hnc
      exact Bool.noConfusion hnc
    refine ⟨(s.1.insert (key n T), s.2.1.push T, s.2.2.1.push h, s.2.2.2.push j),
      hbody, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp, g1 h hh⟩
    · simp
    · simp [hp]
    · simp [hl]
    · change (s.2.1.push T)[0]! = root
      rw [g1 0 hpos]
      exact hr
    · intro i hi
      change i < (s.2.1.push T).size at hi
      change Good (s.2.1.push T)[i]!
      rw [Array.size_push] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with a | rfl
      · rw [g1 i a]
        exact hg i a
      · rw [g2]
        exact hTg
    · intro a ha b hb e
      change a < (s.2.1.push T).size at ha
      change b < (s.2.1.push T).size at hb
      change key n (s.2.1.push T)[a]! = key n (s.2.1.push T)[b]! at e
      rw [Array.size_push] at ha hb
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with a' | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hb with b' | rfl
      · rw [g1 a a', g1 b b'] at e
        exact hinj a a' b b' e
      · rw [g1 a a', g2] at e
        exact absurd e (hfresh a a')
      · rw [g2, g1 b b'] at e
        exact absurd e.symm (hfresh b b')
      · rfl
    · intro x
      change (s.1.insert (key n T)).contains x = true ↔
        ∃ i < (s.2.1.push T).size, key n (s.2.1.push T)[i]! = x
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hK, Array.size_push]
      constructor
      · rintro (e | ⟨i, hi, e⟩)
        · exact ⟨s.2.1.size, by omega, by rw [g2, e]⟩
        · exact ⟨i, by omega, by rw [g1 i hi, e]⟩
      · rintro ⟨i, hi, e⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with a | rfl
        · rw [g1 i a] at e
          exact Or.inr ⟨i, a, e⟩
        · rw [g2] at e
          exact Or.inl e
    · intro i h0 hi
      change i < (s.2.1.push T).size at hi
      change (s.2.2.1.push h)[i]! < i ∧ (s.2.2.2.push j)[i]! < k ∧
        (s.2.1.push T)[i]! = st (s.2.2.2.push j)[i]! (s.2.1.push T)[(s.2.2.1.push h)[i]!]!
      rw [Array.size_push] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with a | rfl
      · obtain ⟨t1, t2, t3⟩ := htr i h0 a
        rw [p1 i a, l1 i a, g1 i a, g1 _ (t1.trans a)]
        exact ⟨t1, t2, t3⟩
      · rw [p2, l2, g2, g1 h hh]
        exact ⟨hh, hj, hT.symm⟩
    · intro i hi l hlk hor
      change i < (s.2.1.push T).size at hi
      change ∃ q < (s.2.1.push T).size, key n (st l (s.2.1.push T)[i]!) =
        key n (s.2.1.push T)[q]!
      rw [Array.size_push] at hi ⊢
      have hi' : i < s.2.1.size := by
        rcases hor with a | ⟨rfl, -⟩
        · omega
        · exact hh
      rw [g1 i hi']
      rcases hor with a | ⟨rfl, a⟩
      · obtain ⟨q, hq, e⟩ := hcl i hi' l hlk (Or.inl a)
        exact ⟨q, by omega, by rw [g1 q hq]; exact e⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 a with a | rfl
        · obtain ⟨q, hq, e⟩ := hcl i hi' l hlk (Or.inr ⟨rfl, a⟩)
          exact ⟨q, by omega, by rw [g1 q hq]; exact e⟩
        · exact ⟨s.2.1.size, by omega, by rw [g2, hT]⟩

theorem cinv_inner (hstep : ∀ l < k, ∀ T, Good T → Good (st l T)) {h : Nat} {s : St}
    (hI : CInv n k st root Good h 0 s) (hh : h < s.2.1.size) :
    let s' := Id.run (forIn (List.range' 0 k) (s.1, s.2.1, s.2.2.1, s.2.2.2)
      (innerBody n st s.2.1[h]! h))
    CInv n k st root Good (h + 1) 0 s' ∧ s.2.1.size ≤ s'.2.1.size := by
  have := forIn_range'_yield k 0 (s.1, s.2.1, s.2.2.1, s.2.2.2) (innerBody n st s.2.1[h]! h)
    (fun j s' => CInv n k st root Good h j s' ∧ s.2.1.size ≤ s'.2.1.size ∧
      s'.2.1[h]! = s.2.1[h]!)
    (fun j hj s' hP => by
      rw [Nat.zero_add]
      obtain ⟨hI', hle, he⟩ := hP
      obtain ⟨s'', e, hI'', hle', he'⟩ := cinv_inner_step hstep hj hI' (by omega)
      rw [he] at e
      exact ⟨s'', e, hI'', by omega, he'.trans he⟩)
    ⟨hI, Nat.le_refl _, rfl⟩
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, hle, -⟩ := this
  refine ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, fun i hi l hlk hor => a9 i hi l hlk ?_⟩, hle⟩
  rcases hor with a | ⟨-, a⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 a with a | rfl
    · exact Or.inl a
    · exact Or.inr ⟨rfl, hlk⟩
  · omega

theorem cinv_outer (hroot : Good root) (hstep : ∀ l < k, ∀ T, Good T → Good (st l T))
    (hK : ∀ T, Good T → key n T ∈ K) {cap : Nat} (hcap : K.card ≤ cap) :
    let s := Id.run (forIn (List.range' 0 cap) (initSt n root) (outerBody n st k))
    CInv n k st root Good s.2.1.size 0 s := by
  refine forIn_range'_done cap 0 (initSt n root) (outerBody n st k)
    (fun h s => h ≤ s.2.1.size ∧ CInv n k st root Good h 0 s)
    (fun s => CInv n k st root Good s.2.1.size 0 s)
    (fun h _ s hP => ?_) (fun s hP => ?_) ⟨Nat.zero_le _, cinv_init hroot⟩
  · obtain ⟨hhs, hI⟩ := hP
    rw [Nat.zero_add]
    rcases Nat.lt_or_ge h s.2.1.size with a | a
    · obtain ⟨hI', hle⟩ := cinv_inner hstep hI a
      exact Or.inl ⟨_, by simp [outerBody, a], by omega, hI'⟩
    · have e : h = s.2.1.size := by omega
      have hns : ¬ h < s.2.1.size := by omega
      refine Or.inr ⟨s, by simp [outerBody, hns], ?_⟩
      rw [← e]
      exact hI
  · obtain ⟨hhs, hI⟩ := hP
    have hle := size_le_card hK hI.2.2.2.2.1 hI.2.2.2.2.2.1
    have e : cap = s.2.1.size := by omega
    rw [← e]
    exact hI

theorem keyBfs_closed (hroot : Good root) (hstep : ∀ l < k, ∀ T, Good T → Good (st l T))
    (hK : ∀ T, Good T → key n T ∈ K) {cap : Nat} (hcap : K.card ≤ cap) :
    ClosedRec n k st root Good (keyBfs n st k root cap).1 (keyBfs n st k root cap).2.1
      (keyBfs n st k root cap).2.2 := by
  have hO := cinv_outer hroot hstep hK hcap (st := st)
  unfold keyBfs
  generalize Id.run (forIn (List.range' 0 cap) (initSt n root) (outerBody n st k)) = s at hO
  obtain ⟨a1, a2, a3, a4, a5, a6, -, a8, a9⟩ := hO
  exact ⟨a1, a2, a3, a4, a5, a6, a8, fun i hi l hl => a9 i hi l hl (Or.inl hi)⟩

end

end CFSG.KS.KeyBfs

end
