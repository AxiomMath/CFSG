module

public import Certificates.Data.CFSGNative.MonsterB.Orth8BFS
public import CFSG.Certificates.Kernel.Spor.BfsReplay
public import Mathlib.Data.Finset.Card

public section

namespace CFSG.KC.PairBfs

open CFSG.Monster.B.Sp8.Native CFSG.KS.BfsReplay

abbrev SP := Array Nat × Array Nat × Array Nat

abbrev SPh := Array Nat × Array Nat × Array Nat × Nat

@[expose] def innerP (tab : Array (Array Nat)) (p : Nat) (k : Nat) (s : SP) : Id (ForInStep SP) :=
  if (decide (pairImg tab k p < 65536) && s.2.1[pairImg tab k p]! == 100000) = true then
    pure (ForInStep.yield (s.1.set! (pairImg tab k p) (65536 * k + p),
      s.2.1.set! (pairImg tab k p) (s.2.1[p]! + 1), s.2.2.push (pairImg tab k p)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2))

@[expose] def runP (tab : Array (Array Nat)) (s : SPh) : SP :=
  Id.run (forIn (List.range' 0 tab.size) (s.1, s.2.1, s.2.2.1) (innerP tab s.2.2.1[s.2.2.2]!))

@[expose] def outerP (tab : Array (Array Nat)) (_t : Nat) (s : SPh) : Id (ForInStep SPh) :=
  if s.2.2.2 < s.2.2.1.size then
    pure (ForInStep.yield ((runP tab s).1, (runP tab s).2.1, (runP tab s).2.2, s.2.2.2 + 1))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def initP (root : Nat) : SPh :=
  (Array.replicate 65536 0, (Array.replicate 65536 100000).set! root 0, #[root], 0)

theorem pairBFS_eq (tab : Array (Array Nat)) (root : Nat) :
    pairBFS tab root =
      ((Id.run (forIn (List.range' 0 65536) (initP root) (outerP tab))).1,
        (Id.run (forIn (List.range' 0 65536) (initP root) (outerP tab))).2.1) := by
  unfold pairBFS
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem get_set {a : Array Nat} {i j v : Nat} (hi : i < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hj : j < a.size
  · rw [getElem!_pos (a.setIfInBounds i v) j (by simpa using hj), Array.getElem_setIfInBounds hj,
      getElem!_pos a j hj]
  · rw [getElem!_neg (a.setIfInBounds i v) j (by simpa using hj), getElem!_neg a j hj]
    split
    · omega
    · rfl

theorem size_set {a : Array Nat} {i v : Nat} : (a.set! i v).size = a.size := by
  simp

@[expose] def InQ (Q : Array Nat) (x : Nat) : Prop := ∃ j < Q.size, Q[j]! = x

theorem inQ_push {Q : Array Nat} {x y : Nat} : InQ (Q.push y) x ↔ InQ Q x ∨ y = x := by
  constructor
  · rintro ⟨j, hj, e⟩
    simp only [Array.size_push] at hj
    rcases Nat.lt_or_ge j Q.size with a | a
    · exact Or.inl ⟨j, a, by rw [← push_lt a]; exact e⟩
    · have : j = Q.size := by omega
      subst this
      exact Or.inr (by rw [← e, push_eq])
  · rintro (⟨j, hj, e⟩ | e)
    · exact ⟨j, by simp; omega, by rw [push_lt hj]; exact e⟩
    · exact ⟨Q.size, by simp, by rw [push_eq, e]⟩

theorem size_le_of_inj {Q : Array Nat} {N : Nat} (hlt : ∀ j < Q.size, Q[j]! < N)
    (hinj : ∀ a < Q.size, ∀ b < Q.size, Q[a]! = Q[b]! → a = b) : Q.size ≤ N := by
  have := Finset.card_le_card_of_injOn (s := Finset.range Q.size) (t := Finset.range N)
    (fun j => Q[j]!) (fun j hj => by simpa using hlt j (by simpa using hj))
    (fun a ha b hb e => hinj a (by simpa using ha) b (by simpa using hb) e)
  simpa using this

variable (tab : Array (Array Nat)) (root : Nat)

@[expose] def Inv (i kk : Nat) (s : SP) : Prop :=
  s.1.size = 65536 ∧ s.2.1.size = 65536 ∧
    (∀ j < s.2.2.size, s.2.2[j]! < 65536) ∧
    (∀ a < s.2.2.size, ∀ b < s.2.2.size, s.2.2[a]! = s.2.2[b]! → a = b) ∧
    (∀ x < 65536, s.2.1[x]! ≠ 100000 ↔ InQ s.2.2 x) ∧
    (∀ x, InQ s.2.2 x → s.2.1[x]! < s.2.2.size) ∧
    InQ s.2.2 root ∧ s.2.1[root]! = 0 ∧
    (∀ x, InQ s.2.2 x → x ≠ root → ∃ k < tab.size, ∃ q, InQ s.2.2 q ∧
      s.1[x]! = 65536 * k + q ∧ s.2.1[q]! + 1 = s.2.1[x]! ∧ pairImg tab k q = x) ∧
    (∀ j < s.2.2.size, ∀ k < tab.size, (j < i ∨ (j = i ∧ k < kk)) →
      pairImg tab k s.2.2[j]! < 65536 → s.2.1[pairImg tab k s.2.2[j]!]! ≠ 100000)

theorem inv_init (hr : root < 65536) :
    Inv tab root 0 0 ((initP root).1, (initP root).2.1, (initP root).2.2.1) := by
  have hd : ∀ x, ((Array.replicate 65536 100000).set! root 0)[x]! =
      if root = x then 0 else (if x < 65536 then 100000 else 0) := by
    intro x
    rw [get_set (by simpa using hr)]
    split
    · rfl
    · by_cases hx : x < 65536
      · rw [getElem!_pos _ _ (by simpa using hx)]
        simp [hx]
      · rw [getElem!_neg _ _ (by simpa using hx)]
        simp [hx]
  have hq : ∀ x, InQ #[root] x ↔ root = x := by
    intro x
    constructor
    · rintro ⟨j, hj, e⟩
      have : j = 0 := by simp at hj; omega
      subst this
      exact e
    · intro e
      exact ⟨0, by simp, e⟩
  simp only [initP]
  refine ⟨by simp, by simp, fun j hj => ?_, fun a ha b hb _ => ?_, fun x hx => ?_, fun x hx => ?_,
    (hq root).2 rfl, ?_, fun x hx hne => absurd ((hq x).1 hx).symm hne, fun j _ k _ h => ?_⟩
  · have : j = 0 := by simp at hj; omega
    subst this
    simpa using hr
  · simp at ha hb
    omega
  · rw [hq, hd]
    by_cases e : root = x
    · simp [e]
    · simp [e, hx]
  · obtain rfl := (hq x).1 hx
    rw [hd]
    simp
  · rw [hd]
    simp
  · omega

variable {tab root}

theorem inner_step {i kk : Nat} {s : SP} (hI : Inv tab root i kk s) (hi : i < s.2.2.size)
    (hk : kk < tab.size) :
    ∃ s', innerP tab s.2.2[i]! kk s = pure (ForInStep.yield s') ∧ Inv tab root i (kk + 1) s' ∧
      s.2.2.size ≤ s'.2.2.size ∧ (∀ j < s.2.2.size, s'.2.2[j]! = s.2.2[j]!) := by
  obtain ⟨hps, hds, hlt, hinj, hvis, hdlt, hroot, hdr, htree, hclos⟩ := hI
  generalize hp : s.2.2[i]! = p
  have hpQ : InQ s.2.2 p := ⟨i, hi, hp⟩
  generalize hq : pairImg tab kk p = q
  by_cases hnew : (decide (q < 65536) && s.2.1[q]! == 100000) = true
  · have hc := hnew
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨hq6, hqu⟩ := hc
    have hqn : ¬ InQ s.2.2 q := fun h => ((hvis q hq6).2 h) hqu
    have hsz := size_le_of_inj hlt hinj
    have hdp := hdlt p hpQ
    have hpq : p ≠ q := fun e => hqn (e ▸ hpQ)
    have hdep : ∀ x, (s.2.1.set! q (s.2.1[p]! + 1))[x]! =
        if q = x then s.2.1[p]! + 1 else s.2.1[x]! := fun x => get_set (by omega)
    have hpar : ∀ x, (s.1.set! q (65536 * kk + p))[x]! =
        if q = x then 65536 * kk + p else s.1[x]! := fun x => get_set (by omega)
    refine ⟨(s.1.set! q (65536 * kk + p), s.2.1.set! q (s.2.1[p]! + 1), s.2.2.push q),
      by rw [innerP, hq, if_pos hnew], ?_, by simp, fun j hj => push_lt hj⟩
    refine ⟨by simp [hps], by simp [hds], fun j hj => ?_, fun a ha b hb e => ?_, fun x hx => ?_,
      fun x hx => ?_, inQ_push.2 (Or.inl hroot), ?_, fun x hx hne => ?_, fun j hj k hk' hjk => ?_⟩
    · simp only [Array.size_push] at hj
      rcases Nat.lt_or_ge j s.2.2.size with a | a
      · rw [push_lt a]
        exact hlt j a
      · have : j = s.2.2.size := by omega
        subst this
        rw [push_eq]
        exact hq6
    · simp only [Array.size_push] at ha hb
      rcases Nat.lt_or_ge a s.2.2.size with a1 | a1 <;> rcases Nat.lt_or_ge b s.2.2.size with b1 | b1
      · rw [push_lt a1, push_lt b1] at e
        exact hinj a a1 b b1 e
      · have : b = s.2.2.size := by omega
        subst this
        rw [push_lt a1, push_eq] at e
        exact absurd ⟨a, a1, e⟩ hqn
      · have : a = s.2.2.size := by omega
        subst this
        rw [push_lt b1, push_eq] at e
        exact absurd ⟨b, b1, e.symm⟩ hqn
      · omega
    · simp only
      rw [hdep, inQ_push]
      by_cases e : q = x
      · subst e
        simp only [if_true, or_true, iff_true]
        omega
      · simp only [e, if_false, or_false]
        exact hvis x hx
    · simp only at hx ⊢
      rw [hdep]
      simp only [Array.size_push]
      rcases inQ_push.1 hx with h | h
      · have : q ≠ x := fun e => hqn (e ▸ h)
        simp only [this, if_false]
        have := hdlt x h
        omega
      · simp only [h, if_true]
        omega
    · simp only
      rw [hdep]
      have : q ≠ root := fun e => hqn (e ▸ hroot)
      simp only [this, if_false]
      exact hdr
    · simp only at hx ⊢
      rcases inQ_push.1 hx with h | h
      · have hxq : q ≠ x := fun e => hqn (e ▸ h)
        obtain ⟨k, hk, r, hr, e1, e2, e3⟩ := htree x h hne
        have hrq : q ≠ r := fun e => hqn (e ▸ hr)
        refine ⟨k, hk, r, inQ_push.2 (Or.inl hr), ?_, ?_, e3⟩
        · rw [hpar]
          simp only [hxq, if_false]
          exact e1
        · rw [hdep, hdep]
          simp only [hxq, hrq, if_false]
          exact e2
      · subst h
        refine ⟨kk, hk, p, inQ_push.2 (Or.inl hpQ), ?_, ?_, hq⟩
        · rw [hpar]
          simp
        · rw [hdep, hdep]
          simp [hpq, Ne.symm hpq]
    · simp only [Array.size_push] at hj ⊢
      intro him
      rw [hdep]
      rcases hjk with a | ⟨a1, a2⟩
      · rw [push_lt (by omega)] at him ⊢
        split
        · omega
        · exact hclos j (by omega) k hk' (Or.inl a) him
      · subst a1
        rw [push_lt hi] at him ⊢
        rw [hp] at him ⊢
        by_cases e : k = kk
        · subst e
          rw [hq]
          simp only [if_true]
          omega
        · split
          · omega
          · have := hclos j hi k hk' (Or.inr ⟨rfl, by omega⟩) (by rw [hp]; exact him)
            rw [hp] at this
            exact this
  · refine ⟨(s.1, s.2.1, s.2.2), by rw [innerP, hq, if_neg hnew], ?_, le_refl _, fun j _ => rfl⟩
    refine ⟨hps, hds, hlt, hinj, hvis, hdlt, hroot, hdr, htree, fun j hj k hk' hjk him => ?_⟩
    rcases hjk with a | ⟨a1, a2⟩
    · exact hclos j hj k hk' (Or.inl a) him
    · by_cases e : k = kk
      · rw [a1, hp, e, hq] at him ⊢
        intro h
        apply hnew
        simp [him, h]
      · exact hclos j hj k hk' (Or.inr ⟨a1, by omega⟩) him

theorem run_spec {s : SPh} (hI : Inv tab root s.2.2.2 0 (s.1, s.2.1, s.2.2.1))
    (hi : s.2.2.2 < s.2.2.1.size) :
    Inv tab root (s.2.2.2 + 1) 0 (runP tab s) ∧ s.2.2.1.size ≤ (runP tab s).2.2.size ∧
      (∀ j < s.2.2.1.size, (runP tab s).2.2[j]! = s.2.2.1[j]!) := by
  unfold runP
  have := forIn_range'_yield tab.size 0 (s.1, s.2.1, s.2.2.1) (innerP tab s.2.2.1[s.2.2.2]!)
    (fun kk s' => Inv tab root s.2.2.2 kk s' ∧ s.2.2.1.size ≤ s'.2.2.size ∧
      (∀ j < s.2.2.1.size, s'.2.2[j]! = s.2.2.1[j]!))
    (fun kk hk s' hP => by
      rw [Nat.zero_add]
      have hi' : s.2.2.2 < s'.2.2.size := by omega
      have e : s'.2.2[s.2.2.2]! = s.2.2.1[s.2.2.2]! := hP.2.2 _ hi
      obtain ⟨s'', h1, h2, h3, h4⟩ := inner_step hP.1 hi' hk
      rw [e] at h1
      exact ⟨s'', h1, h2, by omega, fun j hj => by rw [h4 j (by omega), hP.2.2 j hj]⟩)
    ⟨hI, le_refl _, fun j _ => rfl⟩
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, b1, b2⟩ := this
  refine ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, fun j hj k hk hjk => ?_⟩, b1, b2⟩
  refine a10 j hj k hk ?_
  omega

@[expose] def OInv (tab : Array (Array Nat)) (root t : Nat) (s : SPh) : Prop :=
  Inv tab root s.2.2.2 0 (s.1, s.2.1, s.2.2.1) ∧ s.2.2.2 ≤ s.2.2.1.size ∧ s.2.2.2 ≤ t ∧
    (s.2.2.2 < t → s.2.2.2 = s.2.2.1.size)

theorem outer_spec (hr : root < 65536) (n : Nat) :
    OInv tab root n (Id.run (forIn (List.range' 0 n) (initP root) (outerP tab))) := by
  refine forIn_range'_yield n 0 (initP root) (outerP tab) (OInv tab root)
    (fun t _ s hP => ?_) ⟨inv_init tab root hr, by simp [initP], by simp [initP], by simp [initP]⟩
  obtain ⟨hI, hle, ht, hend⟩ := hP
  by_cases hi : s.2.2.2 < s.2.2.1.size
  · obtain ⟨h1, h2, _⟩ := run_spec hI hi
    refine ⟨_, by simp only [outerP, hi, if_true]; rfl, h1, by simp only; omega,
      by simp only; omega, fun h => ?_⟩
    simp only at h
    omega
  · refine ⟨_, by simp only [outerP, hi, if_false], hI, hle, by omega, fun _ => by omega⟩

theorem pairBFS_spec (hr : root < 65536) :
    (pairBFS tab root).2[root]! = 0 ∧
    (∀ x < 65536, (pairBFS tab root).2[x]! ≠ 100000 → x ≠ root →
      (pairBFS tab root).1[x]! / 65536 < tab.size ∧ (pairBFS tab root).1[x]! % 65536 < 65536 ∧
      (pairBFS tab root).2[(pairBFS tab root).1[x]! % 65536]! < (pairBFS tab root).2[x]! ∧
      pairImg tab ((pairBFS tab root).1[x]! / 65536) ((pairBFS tab root).1[x]! % 65536) = x) ∧
    (∀ x < 65536, (pairBFS tab root).2[x]! ≠ 100000 → ∀ k < tab.size, pairImg tab k x < 65536 →
      (pairBFS tab root).2[pairImg tab k x]! ≠ 100000) := by
  rw [pairBFS_eq]
  have hO := outer_spec (tab := tab) hr 65536
  generalize Id.run (forIn (List.range' 0 65536) (initP root) (outerP tab)) = s at hO
  obtain ⟨⟨_, _, hlt, hinj, hvis, _, _, hdr, htree, hclos⟩, hle, ht, hend⟩ := hO
  dsimp only at hlt hinj hvis hdr htree hclos hle ht hend ⊢
  have hsz := size_le_of_inj hlt hinj
  have hall : s.2.2.2 = s.2.2.1.size := by
    rcases Nat.lt_or_ge s.2.2.2 65536 with a | a
    · exact hend a
    · omega
  refine ⟨hdr, fun x hx hv hne => ?_, fun x hx hv k hk him => ?_⟩
  · obtain ⟨k, hk, q, hq, e1, e2, e3⟩ := htree x ((hvis x hx).1 hv) hne
    obtain ⟨j, hj, rfl⟩ := hq
    have hq6 := hlt j hj
    rw [e1]
    have h1 : (65536 * k + s.2.2.1[j]!) / 65536 = k := by omega
    have h2 : (65536 * k + s.2.2.1[j]!) % 65536 = s.2.2.1[j]! := by omega
    rw [h1, h2]
    exact ⟨hk, hq6, by omega, e3⟩
  · obtain ⟨j, hj, rfl⟩ := (hvis x hx).1 hv
    exact hclos j hj k hk (Or.inl (by omega)) him

end CFSG.KC.PairBfs

end
