module

public import CFSG.Quasithin.Recognition.RuRank3TitsSylInputs
public import CFSG.Sporadic.FischerOddCore.ClosureSearchSpec
public import Certificates.Data.Kernel.SporSch.OrbRec
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.OrbLab

open CFSG.Quasithin.RuRank3 CFSG.Sporadic.FischerOddCore.SearchSpec

variable {n : ℕ} {gens : Array (Array ℕ)}

@[expose, reducible] def ga (gens : Array (Array ℕ)) (k x : ℕ) : ℕ := (gens[k]!)[x]!

@[expose] def kStep (n : ℕ) (gens : Array (Array ℕ)) (c x : ℕ) :
    ℕ → Array ℕ × Array ℕ → Id (ForInStep (Array ℕ × Array ℕ)) := fun k __s =>
  have lab := __s.1
  have queue := __s.2
  have y := (gens[k]!)[x]!
  if (decide (y < n) && lab[y]! == n) = true then
    have lab := lab.set! y c
    have queue := queue.push y
    pure (ForInStep.yield (lab, queue))
  else pure (ForInStep.yield (lab, queue))

@[expose] def qStep (n : ℕ) (gens : Array (Array ℕ)) (c : ℕ) :
    ℕ → Array ℕ × Array ℕ × ℕ → Id (ForInStep (Array ℕ × Array ℕ × ℕ)) := fun _ __s =>
  have lab := __s.1
  have __s := __s.2
  have queue := __s.1
  have head := __s.2
  if head < queue.size then
    have x := queue[head]!
    have head := head + 1
    do
    let __s ← forIn [:gens.size] (lab, queue) (kStep n gens c x)
    have lab : Array ℕ := __s.1
    have queue : Array ℕ := __s.2
    pure (ForInStep.yield (lab, queue, head))
  else pure (ForInStep.yield (lab, queue, head))

@[expose] def oStep (n : ℕ) (gens : Array (Array ℕ)) :
    ℕ → Array ℕ × Array ℕ → Id (ForInStep (Array ℕ × Array ℕ)) := fun s __s =>
  have lab := __s.1
  have roots := __s.2
  if (lab[s]! == n) = true then
    have c := roots.size
    have roots := roots.push s
    have lab := lab.set! s c
    have queue := #[s]
    have head := 0
    do
    let __s ← forIn [:n] (lab, queue, head) (qStep n gens c)
    have lab : Array ℕ := __s.1
    pure (ForInStep.yield (lab, roots))
  else pure (ForInStep.yield (lab, roots))

theorem orbLabels_eq (n : ℕ) (gens : Array (Array ℕ)) :
    (orbLabels n gens).1 =
      (forIn (m := Id) [:n] (Array.replicate n n, (#[] : Array ℕ)) (oStep n gens)).1 := rfl

theorem get_set (a : Array ℕ) {i j : ℕ} (v : ℕ) (hj : j < a.size) :
    (a.set! i v)[j]! = if j = i then v else a[j]! := by
  rw [getElem!_pos _ j (by rw [size_set!']; exact hj), getElem!_pos a j hj]
  simp only [Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds hj]
  by_cases h : j = i
  · simp [h]
  · simp [h, Ne.symm h]

theorem nodup_push {q : Array ℕ} {y : ℕ} (hq : q.toList.Nodup) (hy : y ∉ q) :
    (q.push y).toList.Nodup := by
  rw [Array.toList_push, List.nodup_append]
  refine ⟨hq, List.nodup_singleton y, ?_⟩
  intro a ha b hb
  rw [List.mem_singleton] at hb
  subst hb
  intro e
  subst e
  exact hy (Array.mem_def.2 ha)

theorem size_le_of_nodup {q : Array ℕ} (hq : q.toList.Nodup) (hlt : ∀ y ∈ q, y < n) :
    q.size ≤ n := by
  have hsub : q.toList.toFinset ⊆ Finset.range n := fun y hy => by
    rw [List.mem_toFinset] at hy
    exact Finset.mem_range.2 (hlt y (Array.mem_def.2 hy))
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hq, Finset.card_range] at this
  simpa using this

theorem kStep_yes {c x k : ℕ} {b : Array ℕ × Array ℕ}
    (hc : (decide (ga gens k x < n) && b.1[ga gens k x]! == n) = true) :
    kStep n gens c x k b = ForInStep.yield (b.1.set! (ga gens k x) c, b.2.push (ga gens k x)) := by
  simp only [kStep, ga] at hc ⊢
  rw [if_pos hc]
  rfl

theorem kStep_no {c x k : ℕ} {b : Array ℕ × Array ℕ}
    (hc : ¬ (decide (ga gens k x < n) && b.1[ga gens k x]! == n) = true) :
    kStep n gens c x k b = ForInStep.yield (b.1, b.2) := by
  simp only [kStep, ga] at hc ⊢
  rw [if_neg hc]
  rfl

theorem qStep_yes {c t : ℕ} {b : Array ℕ × Array ℕ × ℕ} (hb : b.2.2 < b.2.1.size) :
    qStep n gens c t b = ForInStep.yield
      ((forIn (m := Id) [:gens.size] (b.1, b.2.1) (kStep n gens c b.2.1[b.2.2]!)).1,
        (forIn (m := Id) [:gens.size] (b.1, b.2.1) (kStep n gens c b.2.1[b.2.2]!)).2,
        b.2.2 + 1) := by
  simp only [qStep]
  rw [if_pos hb]
  rfl

theorem qStep_no {c t : ℕ} {b : Array ℕ × Array ℕ × ℕ} (hb : ¬ b.2.2 < b.2.1.size) :
    qStep n gens c t b = ForInStep.yield (b.1, b.2.1, b.2.2) := by
  simp only [qStep]
  rw [if_neg hb]
  rfl

theorem oStep_yes {s : ℕ} {b : Array ℕ × Array ℕ} (hb : (b.1[s]! == n) = true) :
    oStep n gens s b = ForInStep.yield
      ((forIn (m := Id) [:n] (b.1.set! s b.2.size, #[s], 0) (qStep n gens b.2.size)).1,
        b.2.push s) := by
  simp only [oStep]
  rw [if_pos hb]
  rfl

theorem oStep_no {s : ℕ} {b : Array ℕ × Array ℕ} (hb : ¬ (b.1[s]! == n) = true) :
    oStep n gens s b = ForInStep.yield (b.1, b.2) := by
  simp only [oStep]
  rw [if_neg hb]
  rfl

section Spec

variable {L R P K D : ℕ → ℕ} {m : ℕ}

def KInv (n : ℕ) (gens : Array (Array ℕ)) (L : ℕ → ℕ) (c s x : ℕ) (lab0 : Array ℕ)
    (q0 : Array ℕ) (k : ℕ) (st : Array ℕ × Array ℕ) : Prop :=
  st.1.size = n ∧ (∀ y ∈ st.2, y < n ∧ L y = c) ∧ st.2.toList.Nodup ∧ s ∈ st.2 ∧
    (∀ z < n, st.1[z]! = if z ∈ st.2 then c else lab0[z]!) ∧
    q0.size ≤ st.2.size ∧ (∀ i < q0.size, st.2[i]! = q0[i]!) ∧
    ∀ k' < k, ga gens k' x < n → ga gens k' x ∈ st.2

theorem k_spec {c s x : ℕ} {lab0 : Array ℕ} (hcn : c ≠ n)
    (hcl : ∀ x < n, ∀ k < gens.size, ga gens k x < n → L (ga gens k x) = L x)
    (hx : x < n) (hLx : L x = c) (h0 : ∀ z < n, L z = c → lab0[z]! = n)
    {q0 : Array ℕ} {st : Array ℕ × Array ℕ} (hst : KInv n gens L c s x lab0 q0 0 st) :
    KInv n gens L c s x lab0 q0 gens.size (forIn (m := Id) [:gens.size] st (kStep n gens c x)) := by
  refine forIn_range_yield (KInv n gens L c s x lab0 q0) (kStep n gens c x) gens.size st
    (fun k b hk hI => ?_) hst
  obtain ⟨hsz, hcls, hnd, hs, hlab, hpre, hpreq, himg⟩ := hI
  by_cases hc : (decide (ga gens k x < n) && b.1[ga gens k x]! == n) = true
  · refine ⟨_, kStep_yes hc, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨hy, hyn⟩ := hc
    have hLy : L (ga gens k x) = c := (hcl x hx k hk hy).trans hLx
    have hyq : ga gens k x ∉ b.2 := fun hm => by
      rw [hlab _ hy, if_pos hm] at hyn
      exact hcn hyn
    refine ⟨by rw [size_set!', hsz], fun y hm => ?_, nodup_push hnd hyq,
      Array.mem_push.2 (Or.inl hs), fun z hz => ?_, by rw [Array.size_push]; omega,
      fun i hi => ?_, fun k' hk' hk'n => ?_⟩
    · rcases Array.mem_push.1 hm with hm | rfl
      · exact hcls y hm
      · exact ⟨hy, hLy⟩
    · rw [get_set _ _ (by rw [hsz]; exact hz), hlab z hz]
      by_cases hzy : z = ga gens k x
      · rw [if_pos hzy, if_pos (Array.mem_push.2 (Or.inr hzy))]
      · rw [if_neg hzy]
        by_cases hzq : z ∈ b.2
        · rw [if_pos hzq, if_pos (Array.mem_push.2 (Or.inl hzq))]
        · rw [if_neg hzq, if_neg (fun h => (Array.mem_push.1 h).elim hzq hzy)]
    · rw [get!_push_lt _ _ (by omega), hpreq i hi]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
      · exact Array.mem_push.2 (Or.inl (himg k' hk' hk'n))
      · exact Array.mem_push.2 (Or.inr rfl)
  · refine ⟨_, kStep_no hc, hsz, hcls, hnd, hs, hlab, hpre, hpreq, fun k' hk' hk'n => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
    · exact himg k' hk' hk'n
    · by_contra hm
      apply hc
      rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      refine ⟨hk'n, ?_⟩
      rw [hlab _ hk'n, if_neg hm]
      exact h0 _ hk'n ((hcl x hx k' hk hk'n).trans hLx)

def QInv (n : ℕ) (gens : Array (Array ℕ)) (L : ℕ → ℕ) (c s : ℕ) (lab0 : Array ℕ) (t : ℕ)
    (st : Array ℕ × Array ℕ × ℕ) : Prop :=
  st.1.size = n ∧ (∀ y ∈ st.2.1, y < n ∧ L y = c) ∧ st.2.1.toList.Nodup ∧ s ∈ st.2.1 ∧
    (∀ z < n, st.1[z]! = if z ∈ st.2.1 then c else lab0[z]!) ∧ st.2.2 ≤ st.2.1.size ∧
    (∀ i < st.2.2, ∀ k < gens.size, ga gens k (st.2.1[i]!) < n →
      ga gens k (st.2.1[i]!) ∈ st.2.1) ∧ (t ≤ st.2.2 ∨ st.2.2 = st.2.1.size)

theorem q_spec {c s : ℕ} {lab0 : Array ℕ} (hcn : c ≠ n)
    (hcl : ∀ x < n, ∀ k < gens.size, ga gens k x < n → L (ga gens k x) = L x)
    (h0 : ∀ z < n, L z = c → lab0[z]! = n) {st : Array ℕ × Array ℕ × ℕ}
    (hst : QInv n gens L c s lab0 0 st) :
    QInv n gens L c s lab0 n (forIn (m := Id) [:n] st (qStep n gens c)) := by
  refine forIn_range_yield (QInv n gens L c s lab0) (qStep n gens c) n st
    (fun t b ht hI => ?_) hst
  obtain ⟨hsz, hcls, hnd, hs, hlab, hh, hclo, hprog⟩ := hI
  by_cases hb : b.2.2 < b.2.1.size
  · refine ⟨_, qStep_yes hb, ?_⟩
    have hxm : b.2.1[b.2.2]! ∈ b.2.1 := by
      rw [getElem!_pos b.2.1 b.2.2 hb]
      exact Array.getElem_mem hb
    have hK := k_spec (x := b.2.1[b.2.2]!) (q0 := b.2.1) (st := (b.1, b.2.1)) hcn hcl
      (hcls _ hxm).1 (hcls _ hxm).2 h0
      ⟨hsz, hcls, hnd, hs, hlab, le_refl _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    generalize forIn (m := Id) [:gens.size] (b.1, b.2.1) (kStep n gens c b.2.1[b.2.2]!) = r at hK ⊢
    obtain ⟨hsz', hcls', hnd', hs', hlab', hpre', hpreq', himg'⟩ := hK
    refine ⟨hsz', hcls', hnd', hs', hlab', by dsimp only; omega, fun i hi k hk hkn => ?_,
      by dsimp only; omega⟩
    dsimp only at hi hkn ⊢
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [hpreq' i (by omega)] at hkn ⊢
      obtain ⟨j, hj, hjx⟩ := Array.mem_iff_getElem.1 (hclo i hi k hk hkn)
      rw [← hjx, ← getElem!_pos _ j hj, ← hpreq' j hj, getElem!_pos _ j (by omega)]
      exact Array.getElem_mem _
    · rw [hpreq' _ hb] at hkn ⊢
      exact himg' k hk hkn
  · exact ⟨_, qStep_no hb, hsz, hcls, hnd, hs, hlab, hh, hclo, Or.inr (by dsimp only; omega)⟩

theorem bfs_spec {c s : ℕ} {lab : Array ℕ} (hcn : c ≠ n) (hsn : s < n) (hLs : L s = c)
    (hsize : lab.size = n)
    (hcl : ∀ x < n, ∀ k < gens.size, ga gens k x < n → L (ga gens k x) = L x)
    (htree : ∀ x < n, x ≠ s → L x = c → P x < n ∧ K x < gens.size ∧
      ga gens (K x) (P x) = x ∧ D (P x) < D x)
    (h0 : ∀ z < n, L z = c → lab[z]! = n) :
    (forIn (m := Id) [:n] (lab.set! s c, #[s], 0) (qStep n gens c)).1.size = n ∧
      ∀ z < n, (forIn (m := Id) [:n] (lab.set! s c, #[s], 0) (qStep n gens c)).1[z]! =
        if L z = c then c else lab[z]! := by
  have hQ := q_spec (st := (lab.set! s c, #[s], 0)) (s := s) hcn hcl h0 ⟨by rw [size_set!', hsize],
    fun y hy => by
      rw [Array.mem_singleton] at hy
      subst hy
      exact ⟨hsn, hLs⟩,
    by simp, by simp, fun z hz => by
      rw [get_set _ _ (by rw [hsize]; exact hz)]
      by_cases hzs : z = s
      · rw [if_pos hzs, if_pos (by rw [hzs]; simp)]
      · rw [if_neg hzs, if_neg (by simpa using hzs)],
    by simp, fun i hi => absurd hi (Nat.not_lt_zero _), Or.inl le_rfl⟩
  generalize forIn (m := Id) [:n] (lab.set! s c, #[s], 0) (qStep n gens c) = r at hQ ⊢
  obtain ⟨hsz, hcls, hnd, hs, hlab, hh, hclo, hprog⟩ := hQ
  have hqn := size_le_of_nodup hnd (fun y hy => (hcls y hy).1)
  have hfull : r.2.2 = r.2.1.size := by rcases hprog with h | h <;> omega
  have hclosed : ∀ y ∈ r.2.1, ∀ k < gens.size, ga gens k y < n → ga gens k y ∈ r.2.1 := by
    intro y hy k hk hkn
    obtain ⟨j, hj, hjy⟩ := Array.mem_iff_getElem.1 hy
    have := hclo j (by omega) k hk
    rw [getElem!_pos _ j hj, hjy] at this
    exact this hkn
  have hall : ∀ d, ∀ z < n, D z < d → L z = c → z ∈ r.2.1 := by
    intro d
    induction d with
    | zero => intro z _ h; exact absurd h (Nat.not_lt_zero _)
    | succ d ih =>
      intro z hz hd hLz
      by_cases hzs : z = s
      · rw [hzs]
        exact hs
      · obtain ⟨hp, hk, he, hdp⟩ := htree z hz hzs hLz
        have hLp : L (P z) = c := by
          have := hcl (P z) hp (K z) hk (by rw [he]; exact hz)
          rw [he] at this
          rw [← this, hLz]
        have := hclosed (P z) (ih (P z) hp (by omega) hLp) (K z) hk (by rw [he]; exact hz)
        rwa [he] at this
  refine ⟨hsz, fun z hz => ?_⟩
  rw [hlab z hz]
  by_cases hLz : L z = c
  · rw [if_pos (hall _ z hz (Nat.lt_succ_self _) hLz), if_pos hLz]
  · rw [if_neg (fun hm => hLz (hcls z hm).2), if_neg hLz]

def OInv (n : ℕ) (L R : ℕ → ℕ) (m s : ℕ) (st : Array ℕ × Array ℕ) : Prop :=
  st.1.size = n ∧ st.2.size ≤ m ∧ (∀ c < m, R c < s ↔ c < st.2.size) ∧
    ∀ x < n, st.1[x]! = if R (L x) < s then L x else n

theorem orbLabels_eq_of (hm : m ≤ n) (hL : ∀ x < n, L x < m)
    (hR : ∀ c < m, R c < n ∧ L (R c) = c) (hRmin : ∀ x < n, R (L x) ≤ x)
    (hRmono : ∀ c c', c < c' → c' < m → R c < R c')
    (hcl : ∀ x < n, ∀ k < gens.size, ga gens k x < n → L (ga gens k x) = L x)
    (htree : ∀ x < n, x ≠ R (L x) → P x < n ∧ K x < gens.size ∧
      ga gens (K x) (P x) = x ∧ D (P x) < D x) :
    (orbLabels n gens).1.size = n ∧ ∀ x < n, (orbLabels n gens).1[x]! = L x := by
  rw [orbLabels_eq]
  have hRinj : ∀ c c', c < m → c' < m → R c = R c' → c = c' := fun c c' hc hc' e => by
    rcases Nat.lt_trichotomy c c' with h | h | h
    · exact absurd e (Nat.ne_of_lt (hRmono c c' h hc'))
    · exact h
    · exact absurd e.symm (Nat.ne_of_lt (hRmono c' c h hc))
  have hO := forIn_range_yield (OInv n L R m) (oStep n gens) n (Array.replicate n n, #[])
    (fun s b hs hI => ?_) ⟨by simp, by simp, fun c _ => by simp, fun x hx => by
      rw [if_neg (Nat.not_lt_zero _), getElem!_pos _ x (by simpa using hx)]
      simp⟩
  · obtain ⟨hsz, -, -, hlab⟩ := hO
    refine ⟨hsz, fun x hx => ?_⟩
    rw [hlab x hx, if_pos (lt_of_le_of_lt (hRmin x hx) hx)]
  · obtain ⟨hsz, hrm, hroots, hlab⟩ := hI
    have hLs := hL s hs
    have hLsn : L s ≠ n := Nat.ne_of_lt (lt_of_lt_of_le hLs hm)
    by_cases hb : (b.1[s]! == n) = true
    · refine ⟨_, oStep_yes hb, ?_⟩
      have hb' := hb
      rw [beq_iff_eq, hlab s hs] at hb'
      have hRs : R (L s) = s := by
        by_cases h : R (L s) < s
        · rw [if_pos h] at hb'
          exact absurd hb' hLsn
        · exact le_antisymm (hRmin s hs) (not_lt.1 h)
      have hc : b.2.size = L s := by
        rcases Nat.lt_trichotomy b.2.size (L s) with h | h | h
        · have h1 : ¬ R b.2.size < s := fun h' => lt_irrefl _ ((hroots _ (by omega)).1 h')
          have h2 := hRmono _ _ h hLs
          rw [hRs] at h2
          exact absurd h2 h1
        · exact h
        · have := (hroots (L s) hLs).2 h
          omega
      have hB := bfs_spec (c := L s) (s := s) (lab := b.1) (P := P) (K := K) (D := D) (L := L)
        hLsn hs rfl hsz hcl
        (fun x hx hxs hLx => htree x hx (by rw [hLx, hRs]; exact hxs))
        (fun z hz hLz => by rw [hlab z hz, hLz, hRs, if_neg (lt_irrefl _)])
      rw [← hc] at hB
      obtain ⟨hsz', hlab'⟩ := hB
      refine ⟨hsz', by rw [Array.size_push]; omega, fun c hcm => ?_, fun x hx => ?_⟩
      · rw [Array.size_push]
        constructor
        · intro h
          rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
          · exact Nat.lt_succ_of_lt ((hroots c hcm).1 h)
          · have := hRinj c (L s) hcm hLs (by rw [h, hRs])
            omega
        · intro h
          rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
          · exact Nat.lt_succ_of_lt ((hroots c hcm).2 h)
          · rw [h, hc, hRs]
            exact Nat.lt_succ_self s
      · rw [hlab' x hx, hlab x hx, hc]
        by_cases hLx : L x = L s
        · rw [if_pos hLx, if_pos (by rw [hLx, hRs]; exact Nat.lt_succ_self s), hLx]
        · rw [if_neg hLx]
          have hne : R (L x) ≠ s := fun e => hLx (hRinj _ _ (hL x hx) hLs (by rw [e, hRs]))
          by_cases h : R (L x) < s
          · rw [if_pos h, if_pos (Nat.lt_succ_of_lt h)]
          · rw [if_neg h, if_neg (by omega)]
    · refine ⟨_, oStep_no hb, hsz, hrm, fun c hcm => ?_, fun x hx => ?_⟩
      · have hne : R c ≠ s := fun e => by
          apply hb
          rw [beq_iff_eq, hlab s hs, ← e, (hR c hcm).2, if_neg (lt_irrefl _)]
        rw [← hroots c hcm]
        omega
      · rw [hlab x hx]
        have hne : R (L x) ≠ s := fun e => by
          apply hb
          have hRL := (hR (L x) (hL x hx)).2
          rw [e] at hRL
          rw [beq_iff_eq, hlab s hs, hRL, e, if_neg (lt_irrefl _)]
        by_cases h : R (L x) < s
        · rw [if_pos h, if_pos (Nat.lt_succ_of_lt h)]
        · rw [if_neg h, if_neg (by omega)]

end Spec

theorem orbLabels_of_K {m kG : ℕ} {g : ℕ → ℕ → ℕ} {L R P K D : ℕ → ℕ}
    (hs : gens.size = kG) (hg : ∀ k < kG, ∀ x < n, ga gens k x = g k x)
    (h : orbRecK n m kG g L R P K D = true) :
    (orbLabels n gens).1.size = n ∧ ∀ x < n, (orbLabels n gens).1[x]! = L x := by
  unfold orbRecK at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨hm, hpt⟩, hrt⟩ := h
  have hpt' : ∀ x < n, _ := fun x hx => by
    have := CFSG.KS.allN_spec hpt x hx
    unfold ptK at this
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq,
      Bool.not_eq_true'] at this
    exact this
  have hrt' : ∀ c < m, _ := fun c hc => by
    have := CFSG.KS.allN_spec hrt c hc
    unfold rootK at this
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq,
      Bool.not_eq_true'] at this
    exact this
  have hstep : ∀ c, c + 1 < m → R c < R (c + 1) := fun c hc => by
    have h3 := (hrt' c (by omega)).2
    rcases h3 with h3 | h3
    · exfalso
      have h4 : Nat.blt (c + 1) m = true := by simpa using hc
      simp_all
    · simpa using h3
  refine orbLabels_eq_of (m := m) (L := L) (R := R) (P := P) (K := K) (D := D) hm
    (fun x hx => (hpt' x hx).1.1.1) (fun c hc => ⟨(hrt' c hc).1.1, (hrt' c hc).1.2⟩)
    (fun x hx => (hpt' x hx).1.1.2) (fun c c' hcc hc' => ?_) (fun x hx k hk hkn => ?_)
    (fun x hx hxr => ?_)
  · induction c' with
    | zero => exact absurd hcc (Nat.not_lt_zero _)
    | succ c' ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hcc with h1 | rfl
      · exact lt_trans (ih h1 (by omega)) (hstep c' hc')
      · exact hstep c hc'
  · rw [hs] at hk
    have := (CFSG.KS.allN_spec (hpt' x hx).1.2 k hk)
    rw [hg k hk x hx] at hkn ⊢
    simp only [Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq] at this
    rcases this with h1 | h1
    · exfalso
      have h4 : Nat.blt (g k x) n = true := by simpa using hkn
      simp_all
    · exact h1
  · rcases (hpt' x hx).2 with h1 | h1
    · exact absurd h1 hxr
    · obtain ⟨⟨⟨hp, hk⟩, he⟩, hd⟩ := h1
      refine ⟨hp, by rw [hs]; exact hk, by rw [hg _ hk _ hp]; exact he, hd⟩

end CFSG.KS.OrbLab

end
