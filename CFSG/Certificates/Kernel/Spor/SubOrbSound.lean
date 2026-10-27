module

public import Certificates.Data.Kernel.Spor.SubOrb
public import CFSG.Sporadic.HNOddCore.SixCheckInputs
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.SubOrb

open CFSG.Sporadic.HNOddCore.Native

private def step (H : Array (Array Nat)) (s : Array Bool × Array (Array Nat)) (r : Nat) :
    Array Bool × Array (Array Nat) :=
  if s.1[r]! = false then
    (Array.foldl (fun b a => b.setIfInBounds a true) s.1 (bfsList 1100 H r),
      s.2.push (bfsList 1100 H r))
  else s

private theorem subOrbits_eq (H : Array (Array Nat)) : subOrbits H =
    ((List.range' 0 1100).foldl (step H) (Array.replicate 1100 false, #[])).2 := by
  simp only [subOrbits]
  simp
  generalize List.range' 0 1100 = l
  have : ∀ (init : Array Bool × Array (Array Nat)), l.foldl (step H) init =
      Id.run (forIn l init fun r s => pure (ForInStep.yield (step H s r))) := by
    intro init; simp
  rw [this]
  refine congrArg (fun f => (Id.run (forIn l ((Array.replicate 1100 false, #[]) :
    Array Bool × Array (Array Nat)) f)).2) ?_
  funext r s
  unfold step
  split <;> rfl

private theorem lfoldl_set {α : Type} [Inhabited α] (v : α) : ∀ (ps : List Nat) (s : Array α),
    (ps.foldl (fun b a => b.setIfInBounds a v) s).size = s.size ∧
      ∀ p < s.size, (ps.foldl (fun b a => b.setIfInBounds a v) s)[p]! =
        if p ∈ ps then v else s[p]! := by
  intro ps
  induction ps with
  | nil => intro s; simp
  | cons x xs ih =>
    intro s
    obtain ⟨h1, h2⟩ := ih (s.setIfInBounds x v)
    simp only [List.foldl_cons, Array.size_setIfInBounds] at h1 h2 ⊢
    refine ⟨h1, fun p hp => ?_⟩
    rw [h2 p hp]
    have hs : (s.setIfInBounds x v)[p]! = if x = p then v else s[p]! := by
      rw [getElem!_pos _ p (by simpa using hp), getElem!_pos s p hp, Array.getElem_setIfInBounds]
    rw [hs]
    by_cases hm : p ∈ xs
    · simp [hm]
    · by_cases hx : x = p
      · subst hx; simp
      · simp [hm, hx, Ne.symm hx]

private theorem afoldl_set {α : Type} [Inhabited α] (v : α) (ps : Array Nat) (s : Array α) :
    (ps.foldl (fun b a => b.setIfInBounds a v) s).size = s.size ∧
      ∀ p < s.size, (ps.foldl (fun b a => b.setIfInBounds a v) s)[p]! =
        if p ∈ ps then v else s[p]! := by
  rw [← Array.foldl_toList]
  simpa only [Array.mem_def] using lfoldl_set v ps.toList s

private theorem subLabels_of {k : Nat} {Lst : Nat → Array Nat} {LB : Nat → Nat}
    (hLB : ∀ p < 1100, LB p < k) (hmem : ∀ i < k, ∀ p < 1100, (p ∈ Lst i ↔ LB p = i))
    (Ls : Array (Array Nat)) (hs : Ls.size = k) (hg : ∀ i < k, Ls[i]! = Lst i) :
    subLabels Ls = Array.ofFn (n := 1100) fun p => LB p.val := by
  have inv : ∀ i ≤ k,
      ((List.range' 0 i).foldl (fun b a => Array.foldl (fun b a_1 => b.setIfInBounds a_1 a) b Ls[a]!)
        (Array.replicate 1100 5)).size = 1100 ∧
      ∀ p < 1100, ((List.range' 0 i).foldl
        (fun b a => Array.foldl (fun b a_1 => b.setIfInBounds a_1 a) b Ls[a]!)
        (Array.replicate 1100 5))[p]! = if LB p < i then LB p else 5 := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨by simp, fun p hp => ?_⟩
      simp only [List.range'_zero, List.foldl_nil, Nat.not_lt_zero, if_false]
      rw [getElem!_pos _ p (by simpa using hp), Array.getElem_replicate]
    | succ i ih =>
      intro hi
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
      rw [hg i (by omega)]
      obtain ⟨h3, h4⟩ := afoldl_set i (Lst i)
        ((List.range' 0 i).foldl (fun b a => Array.foldl (fun b a_1 => b.setIfInBounds a_1 a) b Ls[a]!)
          (Array.replicate 1100 5))
      refine ⟨by rw [h3, h1], fun p hp => ?_⟩
      rw [h4 p (by rw [h1]; exact hp), h2 p hp]
      by_cases hm : LB p = i
      · simp [(hmem i (by omega) p hp).2 hm, hm]
      · have : p ∉ Lst i := fun h => hm ((hmem i (by omega) p hp).1 h)
        simp only [this, if_false]
        by_cases hl : LB p < i
        · simp [hl, show LB p < i + 1 by omega]
        · simp [hl, show ¬ LB p < i + 1 by omega]
  obtain ⟨h1, h2⟩ := inv k (Nat.le_refl k)
  simp only [subLabels]
  subst hs
  simp only [Array.forIn_pure_yield_eq_foldl] at *
  simp
  apply Array.ext
  · simp [h1]
  · intro p hp1 hp2
    have hp : p < 1100 := by simpa using hp2
    rw [← getElem!_pos _ p hp1, h2 p hp, if_pos (hLB p hp), Array.getElem_ofFn]

private theorem subOrbits_of {k : Nat} {Lst : Nat → Array Nat} {LB F : Nat → Nat}
    (H : Array (Array Nat)) (hLB : ∀ p < 1100, LB p < k)
    (hmem : ∀ i < k, ∀ p < 1100, (p ∈ Lst i ↔ LB p = i))
    (hF : ∀ i < k, F i < 1100 ∧ LB (F i) = i ∧ ∀ p < F i, LB p < i)
    (hO : ∀ i < k, bfsList 1100 H (F i) = Lst i) :
    subOrbits H = Array.ofFn (n := k) fun i => Lst i.val := by
  have hmono : ∀ i j, i < j → j < k → F i < F j := by
    intro i j hij hj
    obtain ⟨_, hi2, hi3⟩ := hF i (by omega)
    obtain ⟨_, hj2, _⟩ := hF j hj
    rcases Nat.lt_or_ge (F i) (F j) with h | h
    · exact h
    · exfalso
      rcases Nat.lt_or_eq_of_le h with h | h
      · have := hi3 _ h
        omega
      · rw [h] at hj2
        omega
  have inv : ∀ R ≤ 1100, ∃ j ≤ k, (∀ i < j, F i < R) ∧ (j < k → R ≤ F j) ∧
      ((List.range' 0 R).foldl (step H) (Array.replicate 1100 false, #[])).1.size = 1100 ∧
      (∀ p < 1100, ((List.range' 0 R).foldl (step H) (Array.replicate 1100 false, #[])).1[p]! =
        decide (LB p < j)) ∧
      ((List.range' 0 R).foldl (step H) (Array.replicate 1100 false, #[])).2 =
        Array.ofFn (n := j) fun i => Lst i.val := by
    intro R
    induction R with
    | zero =>
      intro _
      refine ⟨0, Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ => Nat.zero_le _,
        by simp, fun p hp => ?_, by simp⟩
      simp only [List.range'_zero, List.foldl_nil]
      rw [getElem!_pos _ p (by simpa using hp), Array.getElem_replicate]
      simp
    | succ R ih =>
      intro hR
      obtain ⟨j, hjk, hj1, hj2, hs, hseen, hres⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
      generalize hst : (List.range' 0 R).foldl (step H) (Array.replicate 1100 false, #[]) = st at *
      by_cases hl : LB R < j
      · have hstep : step H st R = st := by
          unfold step
          rw [if_neg (by rw [hseen R (by omega)]; simp [hl])]
        rw [hstep]
        refine ⟨j, hjk, fun i hi => by have := hj1 i hi; omega, fun hj => ?_, hs, hseen, hres⟩
        rcases Nat.lt_or_eq_of_le (hj2 hj) with h | h
        · omega
        · have := (hF j hj).2.1
          rw [← h] at this
          omega
      · have hjk' : j < k := by have := hLB R (by omega); omega
        have hFj : F j = R := by
          rcases Nat.lt_or_eq_of_le (hj2 hjk') with h | h
          · have := (hF j hjk').2.2 R h
            omega
          · exact h.symm
        have hb : bfsList 1100 H R = Lst j := by rw [← hFj]; exact hO j hjk'
        have hstep : step H st R =
            (Array.foldl (fun b a => b.setIfInBounds a true) st.1 (Lst j), st.2.push (Lst j)) := by
          unfold step
          rw [if_pos (by rw [hseen R (by omega)]; simp [hl]), hb]
        rw [hstep]
        obtain ⟨h3, h4⟩ := afoldl_set true (Lst j) st.1
        refine ⟨j + 1, hjk', fun i hi => ?_, fun hj => ?_, by rw [h3, hs], fun p hp => ?_, ?_⟩
        · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
          · have := hj1 i h
            omega
          · rw [h, hFj]
            omega
        · have := hmono j (j + 1) (by omega) hj
          omega
        · rw [h4 p (by rw [hs]; exact hp), hseen p hp]
          by_cases hm : LB p = j
          · simp [(hmem j hjk' p hp).2 hm, hm]
          · have : p ∉ Lst j := fun h => hm ((hmem j hjk' p hp).1 h)
            simp only [this, if_false]
            by_cases hl' : LB p < j
            · simp [hl', show LB p < j + 1 by omega]
            · simp [hl', show ¬ LB p < j + 1 by omega]
        · rw [hres, Array.ofFn_succ]
          simp
  obtain ⟨j, hjk, hj1, hj2, _, _, hres⟩ := inv 1100 (Nat.le_refl _)
  have hj : j = k := by
    rcases Nat.lt_or_eq_of_le hjk with h | h
    · have := hj2 h
      have := (hF j h).1
      omega
    · exact h
  subst hj
  rw [subOrbits_eq, hres]

theorem subOrbK_sound {k : Nat} {CNT : Nat → Nat} {PT : Nat → Nat → Nat} {LB PSN : Nat → Nat}
    {H : Array (Array Nat)}
    (hO : ∀ i < k, bfsList 1100 H (PT i 0) = Array.ofFn (n := CNT i) fun q => PT i q.val)
    (h : subOrbK 1100 k CNT PT LB PSN = true) :
    subOrbits H = (Array.ofFn (n := k) fun i => Array.ofFn (n := CNT i.val) fun q => PT i q.val) ∧
      subLabels (Array.ofFn (n := k) fun i => Array.ofFn (n := CNT i.val) fun q => PT i q.val) =
        Array.ofFn (n := 1100) fun p => LB p.val := by
  have hA : ∀ p < 1100, LB p < k ∧ PSN p < CNT (LB p) ∧ PT (LB p) (PSN p) = p := by
    intro p hp
    have := allN_spec ((bAnd_iff _ _).1 h).1 p hp
    simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at this
    exact this
  have hB : ∀ i < k, 0 < CNT i ∧ (∀ q < CNT i, PT i q < 1100 ∧ LB (PT i q) = i) ∧
      ∀ p < PT i 0, LB p < i := by
    intro i hi
    have := allN_spec ((bAnd_iff _ _).1 h).2 i hi
    simp only [bAnd_iff, Nat.blt_eq] at this
    obtain ⟨h1, h2, h3⟩ := this
    refine ⟨h1, fun q hq => ?_, fun p hp => ?_⟩
    · have := allN_spec h2 q hq
      simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at this
      exact this
    · have := allN_spec h3 p hp
      simpa only [Nat.blt_eq] using this
  have hmem : ∀ i < k, ∀ p < 1100,
      (p ∈ (Array.ofFn (n := CNT i) fun q => PT i q.val) ↔ LB p = i) := by
    intro i hi p hp
    rw [Array.mem_ofFn]
    constructor
    · rintro ⟨q, rfl⟩
      exact ((hB i hi).2.1 q q.2).2
    · intro hl
      obtain ⟨_, h2, h3⟩ := hA p hp
      subst hl
      exact ⟨⟨PSN p, h2⟩, h3⟩
  have hLB : ∀ p < 1100, LB p < k := fun p hp => (hA p hp).1
  refine ⟨subOrbits_of (Lst := fun i => Array.ofFn (n := CNT i) fun q => PT i q.val)
    (F := fun i => PT i 0) H hLB hmem (fun i hi => ⟨((hB i hi).2.1 0 (hB i hi).1).1,
      ((hB i hi).2.1 0 (hB i hi).1).2, (hB i hi).2.2⟩) hO, ?_⟩
  exact subLabels_of (Lst := fun i => Array.ofFn (n := CNT i) fun q => PT i q.val) hLB hmem _
    (by simp) fun i hi => by rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

end CFSG.KS.SubOrb

end
