module

public import CFSG.Certificates.Kernel.SporSch.KeyBfsSound

public section

namespace CFSG.KS.KeyBfsG

open CFSG.KS.KeyBfs (forIn_range'_yield push_lt push_eq)

variable {α : Type} [Inhabited α]

@[expose] def keyBfsG (κ : α → Nat) (st : Nat → α → α) (k : Nat) (root : α) (key0 cap : Nat) :
    Array α × Array Nat × Array Nat := Id.run do
  let mut els : Array α := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut seen : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert key0
  for h in [0:cap] do
    if h < els.size then
      for s in [0:k] do
        let y := st s els[h]!
        if !seen.contains (κ y) then
          seen := seen.insert (κ y)
          els := els.push y
          par := par.push h
          lab := lab.push s
  return (els, par, lab)

abbrev GSt (α : Type) := Array α × Array Nat × Array Nat × Std.HashSet Nat

@[expose] def innerG (κ : α → Nat) (st : Nat → α → α) (h j : Nat) (s : GSt α) :
    Id (ForInStep (GSt α)) :=
  if (!s.2.2.2.contains (κ (st j s.1[h]!))) = true then
    pure (ForInStep.yield (s.1.push (st j s.1[h]!), s.2.1.push h, s.2.2.1.push j,
      s.2.2.2.insert (κ (st j s.1[h]!))))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def outerG (κ : α → Nat) (st : Nat → α → α) (k h : Nat) (s : GSt α) :
    Id (ForInStep (GSt α)) :=
  if h < s.1.size then
    pure (ForInStep.yield (Id.run (forIn (List.range' 0 k) (s.1, s.2.1, s.2.2.1, s.2.2.2)
      (innerG κ st h))))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def initG (root : α) (key0 : Nat) : GSt α :=
  (#[root], #[0], #[0], (∅ : Std.HashSet Nat).insert key0)

theorem keyBfsG_eq (κ : α → Nat) (st : Nat → α → α) (k : Nat) (root : α) (key0 cap : Nat) :
    keyBfsG κ st k root key0 cap =
      ((Id.run (forIn (List.range' 0 cap) (initG root key0) (outerG κ st k))).1,
        (Id.run (forIn (List.range' 0 cap) (initG root key0) (outerG κ st k))).2.1,
        (Id.run (forIn (List.range' 0 cap) (initG root key0) (outerG κ st k))).2.2.1) := by
  unfold keyBfsG
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

omit [Inhabited α] in
theorem forIn_sim {β γ : Type} (π : β → γ) (l : List Nat) (f : Nat → β → Id (ForInStep β))
    (g : Nat → γ → Id (ForInStep γ))
    (h : ∀ x b, ∃ b', f x b = pure (ForInStep.yield b') ∧
      g x (π b) = pure (ForInStep.yield (π b'))) (b : β) :
    Id.run (forIn l (π b) g) = π (Id.run (forIn l b f)) := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨b', hf, hg⟩ := h x b
    rw [List.forIn_cons, List.forIn_cons, hf, hg]
    exact ih b'

structure GRec (κ : α → Nat) (st : Nat → α → α) (k : Nat) (root : α) (key0 cnt Ec : Nat)
    (T : Nat → α) (P L POS : Nat → Nat) : Prop where
  k_pos : 0 < k
  cnt_pos : 0 < cnt
  root_eq : T 0 = root
  key0_eq : key0 = κ root
  par_zero : P 0 = 0
  lab_zero : L 0 = 0
  inj : ∀ a < cnt, ∀ b < cnt, κ (T a) = κ (T b) → a = b
  tree : ∀ i, 0 < i → i < cnt → P i < i ∧ L i < k ∧ T i = st (L i) (T (P i))
  order : ∀ i, 0 < i → i + 1 < cnt → k * P i + L i < k * P (i + 1) + L (i + 1)
  last : k * P (cnt - 1) + L (cnt - 1) < Ec
  close : ∀ e < Ec, POS e < cnt ∧ κ (st (e % k) (T (e / k))) = κ (T (POS e)) ∧
    (POS e = 0 ∨ k * P (POS e) + L (POS e) ≤ e)

@[expose] def AInv (κ : α → Nat) (k cnt Ec : Nat) (T : Nat → α) (P L : Nat → Nat) (e : Nat)
    (s : GSt α) : Prop :=
  s.2.1.size = s.1.size ∧ s.2.2.1.size = s.1.size ∧
    (∀ i < s.1.size, i < cnt → s.1[i]! = T i ∧ s.2.1[i]! = P i ∧ s.2.2.1[i]! = L i) ∧
    ((e ≤ Ec ∨ k * cnt ≤ Ec) →
      (∀ x, s.2.2.2.contains x = true ↔ ∃ i < s.1.size, κ (T i) = x) ∧ s.1.size ≤ cnt ∧
        ∀ i < cnt, (i < s.1.size ↔ (i = 0 ∨ k * P i + L i < e))) ∧
    (Ec ≤ e → cnt ≤ s.1.size)

theorem le_of_mul_le {k a b c : Nat} (hb : b < k) (h : k * c ≤ k * a + b) : c ≤ a := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hlt)
  rw [Nat.mul_succ] at this
  omega

theorem lt_of_mul_lt {k a b c : Nat} (h : k * a + b < k * c) : a < c := by
  refine Nat.lt_of_not_le fun hle => ?_
  have := Nat.mul_le_mul_left k hle
  omega

theorem step_eq {k a b c d : Nat} (hb : b < k) (hd : d < k) (h : k * a + b = k * c + d) :
    a = c ∧ b = d := by
  have h1 : c ≤ a := le_of_mul_le hb (by omega)
  have h2 : a ≤ c := le_of_mul_le hd (by omega)
  have e : a = c := Nat.le_antisymm h2 h1
  subst e
  exact ⟨rfl, by omega⟩

section

variable {κ : α → Nat} {st : Nat → α → α} {k : Nat} {root : α} {key0 cnt Ec : Nat}
  {T : Nat → α} {P L POS : Nat → Nat}

omit [Inhabited α] in
theorem order_lt (R : GRec κ st k root key0 cnt Ec T P L POS) {i i' : Nat} (h0 : 0 < i)
    (hi : i < i') (hi' : i' < cnt) : k * P i + L i < k * P i' + L i' := by
  induction i' with
  | zero => omega
  | succ i' ih =>
    rcases Nat.lt_or_ge i i' with a | a
    · exact Nat.lt_trans (ih a (by omega)) (R.order i' (by omega) hi')
    · have e : i = i' := by omega
      subst e
      exact R.order i h0 hi'

omit [Inhabited α] in
theorem lab_lt (R : GRec κ st k root key0 cnt Ec T P L POS) {i : Nat} (hi : i < cnt) : L i < k := by
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · rw [h0, R.lab_zero]
    exact R.k_pos
  · exact (R.tree i h0 hi).2.1

theorem ainv_init (R : GRec κ st k root key0 cnt Ec T P L POS) :
    AInv κ k cnt Ec T P L 0 (initG root key0) := by
  refine ⟨rfl, rfl, fun i hi _ => ?_, fun _ => ⟨fun x => ?_, ?_, fun i _ => ?_⟩, fun h => ?_⟩
  · have : i = 0 := by simp [initG] at hi; omega
    subst this
    simp [initG, R.root_eq, R.par_zero, R.lab_zero]
  · simp only [initG]
    rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
    constructor
    · intro e
      exact ⟨0, by simp, by rw [R.root_eq, ← R.key0_eq]; exact beq_iff_eq.1 e⟩
    · rintro ⟨i, hi, e⟩
      have : i = 0 := by simp at hi; omega
      subst this
      rw [← e, R.root_eq, ← R.key0_eq]
      exact beq_self_eq_true _
  · simp only [initG, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
    exact R.cnt_pos
  · simp only [initG, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
    omega
  · have := R.last
    omega

theorem ainv_inner (R : GRec κ st k root key0 cnt Ec T P L POS) {h j : Nat} {s : GSt α}
    (hj : j < k) (hh : h < s.1.size) (hI : AInv κ k cnt Ec T P L (k * h + j) s) :
    ∃ s', innerG κ st h j s = pure (ForInStep.yield s') ∧
      AInv κ k cnt Ec T P L (k * h + (j + 1)) s' ∧ s.1.size ≤ s'.1.size := by
  obtain ⟨hp, hl, hget, hC, hD⟩ := hI
  by_cases he : k * h + j < Ec
  · obtain ⟨hK, hle, hch⟩ := hC (Or.inl (Nat.le_of_lt he))
    have hhc : h < cnt := by omega
    have hTh : s.1[h]! = T h := (hget h hh hhc).1
    obtain ⟨hq, hx, hor⟩ := R.close _ he
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj, Nat.mul_add_div R.k_pos, Nat.div_eq_of_lt hj,
      Nat.add_zero] at hx
    generalize POS (k * h + j) = q at hq hx hor
    by_cases hnew : 0 < q ∧ k * P q + L q = k * h + j
    · obtain ⟨hq0, hSq⟩ := hnew
      obtain ⟨-, hLq, hTq⟩ := R.tree q hq0 hq
      obtain ⟨ePh, eLj⟩ := step_eq hLq hj hSq
      rw [ePh, eLj] at hTq
      have hqm : q = s.1.size := by
        refine Nat.le_antisymm ?_ (Nat.le_of_not_lt fun hlt => ?_)
        · have h1 : q - 1 < s.1.size := (hch (q - 1) (by omega)).2 (by
            rcases Nat.eq_zero_or_pos (q - 1) with h0 | h0
            · exact Or.inl h0
            · exact Or.inr (by have := order_lt R h0 (by omega : q - 1 < q) hq; omega))
          omega
        · rcases (hch q hq).1 hlt with e | e <;> omega
      have hnc : s.2.2.2.contains (κ (T q)) = false := by
        rw [Bool.eq_false_iff]
        intro hc
        obtain ⟨i, hi, e⟩ := (hK _).1 hc
        have := R.inj i (by omega) q hq e
        omega
      have hbody : innerG κ st h j s = pure (ForInStep.yield (s.1.push (T q), s.2.1.push h,
          s.2.2.1.push j, s.2.2.2.insert (κ (T q)))) := by
        unfold innerG
        rw [hTh, ← hTq, hnc]
        rfl
      have hchar : ∀ i < cnt, (i < s.1.size + 1 ↔ (i = 0 ∨ k * P i + L i < k * h + (j + 1))) := by
        intro i hi
        constructor
        · intro hlt
          rcases Nat.lt_or_ge i s.1.size with a | a
          · rcases (hch i hi).1 a with e | e
            · exact Or.inl e
            · exact Or.inr (by omega)
          · have e : i = q := by omega
            rw [e, hSq]
            exact Or.inr (by omega)
        · rintro (e | e)
          · omega
          · by_cases hlt : k * P i + L i < k * h + j
            · have := (hch i hi).2 (Or.inr hlt)
              omega
            · by_cases hi0 : i = 0
              · omega
              · have hiq : i = q := by
                  refine Classical.byContradiction fun hne => ?_
                  rcases Nat.lt_or_gt_of_ne hne with c | c
                  · have := order_lt R (by omega) c hq
                    omega
                  · have := order_lt R hq0 c hi
                    omega
                omega
      refine ⟨_, hbody, ⟨?_, ?_, ?_, fun _ => ⟨?_, ?_, ?_⟩, fun _ => ?_⟩, by simp⟩
      · simp [hp]
      · simp [hl]
      · intro i hi hic
        change i < (s.1.push (T q)).size at hi
        change (s.1.push (T q))[i]! = T i ∧ (s.2.1.push h)[i]! = P i ∧ (s.2.2.1.push j)[i]! = L i
        rw [Array.size_push] at hi
        rcases Nat.lt_or_ge i s.1.size with a | a
        · rw [push_lt a, push_lt (by omega : i < s.2.1.size), push_lt (by omega : i < s.2.2.1.size)]
          exact hget i a hic
        · have e : i = s.1.size := by omega
          have e1 : (s.2.1.push h)[s.1.size]! = h := by rw [← hp]; exact push_eq
          have e2 : (s.2.2.1.push j)[s.1.size]! = j := by rw [← hl]; exact push_eq
          rw [e, push_eq, e1, e2, ← hqm]
          exact ⟨rfl, ePh.symm, eLj.symm⟩
      · intro x
        change (s.2.2.2.insert (κ (T q))).contains x = true ↔
          ∃ i < (s.1.push (T q)).size, κ (T i) = x
        rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hK, Array.size_push]
        constructor
        · rintro (e | ⟨i, hi, e⟩)
          · exact ⟨q, by omega, e⟩
          · exact ⟨i, by omega, e⟩
        · rintro ⟨i, hi, e⟩
          rcases Nat.lt_or_ge i s.1.size with a | a
          · exact Or.inr ⟨i, a, e⟩
          · have e' : i = q := by omega
            rw [e'] at e
            exact Or.inl e
      · change (s.1.push (T q)).size ≤ cnt
        rw [Array.size_push]
        omega
      · intro i hi
        change i < (s.1.push (T q)).size ↔ _
        rw [Array.size_push]
        exact hchar i hi
      · change cnt ≤ (s.1.push (T q)).size
        rw [Array.size_push]
        have := (hchar (cnt - 1) (by have := R.cnt_pos; omega)).2 (Or.inr (by
          have := R.last
          omega))
        omega
    · have hqs : q < s.1.size := (hch q hq).2 (by
        rcases hor with e | e
        · exact Or.inl e
        · by_cases h0 : q = 0
          · exact Or.inl h0
          · right
            have : ¬ k * P q + L q = k * h + j := fun e' => hnew ⟨by omega, e'⟩
            omega)
      have hc : s.2.2.2.contains (κ (st j s.1[h]!)) = true := by
        rw [hTh]
        exact (hK _).2 ⟨q, hqs, hx.symm⟩
      have hchar : ∀ i < cnt, (i < s.1.size ↔ (i = 0 ∨ k * P i + L i < k * h + (j + 1))) := by
        intro i hi
        rw [hch i hi]
        constructor
        · rintro (a | a)
          · exact Or.inl a
          · exact Or.inr (by omega)
        · rintro (a | a)
          · exact Or.inl a
          · by_cases hlt : k * P i + L i < k * h + j
            · exact Or.inr hlt
            · by_cases hi0 : i = 0
              · exact Or.inl hi0
              · exfalso
                obtain ⟨-, hLi, hTi⟩ := R.tree i (by omega) hi
                obtain ⟨e1, e2⟩ := step_eq hLi hj (by omega : k * P i + L i = k * h + j)
                have ek : κ (T i) = κ (T q) := by rw [hTi, e1, e2, hx]
                have := R.inj i hi q hq ek
                subst this
                exact hnew ⟨by omega, by omega⟩
      refine ⟨(s.1, s.2.1, s.2.2.1, s.2.2.2), by unfold innerG; rw [hc]; rfl,
        ⟨hp, hl, hget, fun _ => ⟨hK, hle, hchar⟩, fun _ => ?_⟩, Nat.le_refl _⟩
      have := (hchar (cnt - 1) (by have := R.cnt_pos; omega)).2 (Or.inr (by
        have := R.last
        omega))
      change cnt ≤ s.1.size
      omega
  · have hnC : ¬ (k * h + (j + 1) ≤ Ec ∨ k * cnt ≤ Ec) := by
      rintro (a | a)
      · omega
      · obtain ⟨-, hle, -⟩ := hC (Or.inr a)
        have := Nat.mul_le_mul_left k (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hh hle))
        rw [Nat.mul_succ] at this
        omega
    have hcm : cnt ≤ s.1.size := hD (by omega)
    by_cases hc : s.2.2.2.contains (κ (st j s.1[h]!)) = true
    · exact ⟨(s.1, s.2.1, s.2.2.1, s.2.2.2), by unfold innerG; rw [hc]; rfl,
        ⟨hp, hl, hget, fun a => absurd a hnC, fun _ => hcm⟩, Nat.le_refl _⟩
    · have hnc : s.2.2.2.contains (κ (st j s.1[h]!)) = false := Bool.eq_false_iff.2 hc
      refine ⟨_, by unfold innerG; rw [hnc]; rfl, ⟨by simp [hp], by simp [hl], ?_,
        fun a => absurd a hnC, fun _ => by simp; omega⟩, by simp⟩
      intro i hi hic
      have a : i < s.1.size := by omega
      change (s.1.push _)[i]! = T i ∧ (s.2.1.push h)[i]! = P i ∧ (s.2.2.1.push j)[i]! = L i
      rw [push_lt a, push_lt (by omega : i < s.2.1.size), push_lt (by omega : i < s.2.2.1.size)]
      exact hget i a hic

theorem ainv_head (R : GRec κ st k root key0 cnt Ec T P L POS) {h : Nat} {s : GSt α}
    (hI : AInv κ k cnt Ec T P L (k * h) s) :
    ∃ s', outerG κ st k h s = pure (ForInStep.yield s') ∧
      AInv κ k cnt Ec T P L (k * (h + 1)) s' := by
  rw [Nat.mul_succ]
  by_cases hh : h < s.1.size
  · refine ⟨Id.run (forIn (List.range' 0 k) (s.1, s.2.1, s.2.2.1, s.2.2.2) (innerG κ st h)),
      by simp only [outerG, hh, ↓reduceIte], ?_⟩
    have := forIn_range'_yield k 0 (s.1, s.2.1, s.2.2.1, s.2.2.2) (innerG κ st h)
      (fun j s' => AInv κ k cnt Ec T P L (k * h + j) s' ∧ h < s'.1.size)
      (fun j hj s' hP => by
        rw [Nat.zero_add]
        obtain ⟨s'', e, hI', hle⟩ := ainv_inner R hj hP.2 hP.1
        exact ⟨s'', e, hI', by omega⟩)
      ⟨hI, hh⟩
    exact this.1
  · refine ⟨(s.1, s.2.1, s.2.2.1, s.2.2.2), by simp only [outerG, hh, ↓reduceIte], ?_⟩
    obtain ⟨hp, hl, hget, hC, hD⟩ := hI
    have hno : (k * h ≤ Ec ∨ k * cnt ≤ Ec) → ∀ i < cnt,
        ((i = 0 ∨ k * P i + L i < k * h) ↔ (i = 0 ∨ k * P i + L i < k * h + k)) := by
      intro hB i hi
      obtain ⟨-, -, hch⟩ := hC hB
      constructor
      · rintro (a | a)
        · exact Or.inl a
        · exact Or.inr (by omega)
      · rintro (a | a)
        · exact Or.inl a
        · by_cases hlt : k * P i + L i < k * h
          · exact Or.inr hlt
          · by_cases hi0 : i = 0
            · exact Or.inl hi0
            · exfalso
              obtain ⟨hPi, hLi, -⟩ := R.tree i (by omega) hi
              have e1 : h ≤ P i := le_of_mul_le hLi (by omega)
              have e2 : P i < h + 1 := lt_of_mul_lt (by rw [Nat.mul_succ]; omega)
              have ehp : P i = h := by omega
              have hns : ¬ (h = 0 ∨ k * P h + L h < k * h) := by
                rw [← hch h (by omega)]
                exact hh
              have hh0 : 0 < h := by omega
              have := le_of_mul_le (lab_lt R (by omega : h < cnt))
                (by omega : k * h ≤ k * P h + L h)
              have := (R.tree h hh0 (by omega)).1
              omega
    refine ⟨hp, hl, hget, fun hB => ?_, fun hE => ?_⟩
    · have hB' : k * h ≤ Ec ∨ k * cnt ≤ Ec := by omega
      obtain ⟨hK, hle, hch⟩ := hC hB'
      exact ⟨hK, hle, fun i hi => (hch i hi).trans (hno hB' i hi)⟩
    · by_cases hE' : Ec ≤ k * h
      · exact hD hE'
      · have hB' : k * h ≤ Ec ∨ k * cnt ≤ Ec := Or.inl (by omega)
        obtain ⟨-, -, hch⟩ := hC hB'
        have := (hch (cnt - 1) (by have := R.cnt_pos; omega)).2
          ((hno hB' (cnt - 1) (by have := R.cnt_pos; omega)).2 (Or.inr (by
            have := R.last
            omega)))
        change cnt ≤ s.1.size
        omega

theorem keyBfsG_rec (R : GRec κ st k root key0 cnt Ec T P L POS) {cap : Nat}
    (hcap : P (cnt - 1) < cap) :
    cnt ≤ (keyBfsG κ st k root key0 cap).1.size ∧
      (∀ i < cnt, (keyBfsG κ st k root key0 cap).1[i]! = T i ∧
        (keyBfsG κ st k root key0 cap).2.1[i]! = P i ∧
        (keyBfsG κ st k root key0 cap).2.2[i]! = L i) ∧
      (k * cnt ≤ Ec → (keyBfsG κ st k root key0 cap).1.size = cnt) ∧
      (keyBfsG κ st k root key0 cap).2.1.size = (keyBfsG κ st k root key0 cap).1.size ∧
      (keyBfsG κ st k root key0 cap).2.2.size = (keyBfsG κ st k root key0 cap).1.size := by
  have hO : AInv κ k cnt Ec T P L (k * cap)
      (Id.run (forIn (List.range' 0 cap) (initG root key0) (outerG κ st k))) :=
    forIn_range'_yield cap 0 (initG root key0) (outerG κ st k)
      (fun h s => AInv κ k cnt Ec T P L (k * h) s)
      (fun h _ s hP => by
        rw [Nat.zero_add]
        exact ainv_head R hP)
      (by rw [Nat.mul_zero]; exact ainv_init R)
  rw [keyBfsG_eq]
  generalize Id.run (forIn (List.range' 0 cap) (initG root key0) (outerG κ st k)) = s at hO
  obtain ⟨hps, hls, hget, hC, hD⟩ := hO
  dsimp only
  have hcnt : cnt ≤ s.1.size := by
    by_cases hE : Ec ≤ k * cap
    · exact hD hE
    · obtain ⟨-, -, hch⟩ := hC (Or.inl (by omega))
      have hc1 : cnt - 1 < cnt := by have := R.cnt_pos; omega
      have hlast : k * P (cnt - 1) + L (cnt - 1) < k * cap := by
        have := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hcap)
        have := lab_lt R hc1
        rw [Nat.mul_succ] at *
        omega
      have := (hch (cnt - 1) hc1).2 (Or.inr hlast)
      omega
  refine ⟨hcnt, fun i hi => hget i (by omega) hi, fun hk => ?_, hps, hls⟩
  obtain ⟨-, hle, -⟩ := hC (Or.inr hk)
  omega

end

@[expose] def keyTab (κ : α → Nat) (L : Array α) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := ∅
  for i in [0:L.size] do
    m := m.insert (κ L[i]!) i
  return m

theorem keyTab_getD {κ : α → Nat} {L : Array α}
    (hinj : ∀ a < L.size, ∀ b < L.size, κ L[a]! = κ L[b]! → a = b) {j : Nat} (hj : j < L.size)
    (d : Nat) : (keyTab κ L).getD (κ L[j]!) d = j := by
  have e : keyTab κ L =
      (List.range L.size).foldl (fun m i => m.insert (κ L[i]!) i) (∅ : Std.HashMap Nat Nat) := by
    unfold keyTab
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
      Std.Legacy.Range.size]
    simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
    rfl
  have key : ∀ n ≤ L.size, ∀ j < n,
      ((List.range n).foldl (fun m i => m.insert (κ L[i]!) i)
        (∅ : Std.HashMap Nat Nat)).getD (κ L[j]!) d = j := by
    intro n
    induction n with
    | zero => intro _ j hj; omega
    | succ n ih =>
      intro hn j hjn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Std.HashMap.getD_insert]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hjn with a | rfl
      · have hne : (κ L[n]! == κ L[j]!) = false := by
          rw [beq_eq_false_iff_ne]
          intro e'
          have := hinj n (by omega) j (by omega) e'
          omega
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        exact ih (by omega) j a
      · simp only [beq_self_eq_true, ↓reduceIte]
  rw [e]
  exact key L.size le_rfl j hj

section

variable {β : Type} [Inhabited β]

@[expose] def keyBfsT (sk : Nat → α → Nat) (st : Nat → α → α) (stB : Nat → β → β) (k : Nat)
    (root : α) (rootB : β) (key0 cap : Nat) : Array α × Array Nat × Array Nat × Array β :=
  Id.run do
  let mut pts : Array α := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut tr : Array β := #[rootB]
  let mut idx : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert key0
  for h in [0:cap] do
    if h < pts.size then
      for s in [0:k] do
        let f := sk s pts[h]!
        if !idx.contains f then
          idx := idx.insert f
          pts := pts.push (st s pts[h]!)
          par := par.push h
          lab := lab.push s
          tr := tr.push (stB s tr[h]!)
  return (pts, par, lab, tr)

abbrev TSt (α β : Type) := Array α × Array Nat × Array Nat × Array β × Std.HashSet Nat

@[expose] def innerT (sk : Nat → α → Nat) (st : Nat → α → α) (stB : Nat → β → β) (h j : Nat)
    (s : TSt α β) : Id (ForInStep (TSt α β)) :=
  if (!s.2.2.2.2.contains (sk j s.1[h]!)) = true then
    pure (ForInStep.yield (s.1.push (st j s.1[h]!), s.2.1.push h, s.2.2.1.push j,
      s.2.2.2.1.push (stB j s.2.2.2.1[h]!), s.2.2.2.2.insert (sk j s.1[h]!)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))

@[expose] def outerT (sk : Nat → α → Nat) (st : Nat → α → α) (stB : Nat → β → β) (k h : Nat)
    (s : TSt α β) : Id (ForInStep (TSt α β)) :=
  if h < s.1.size then
    pure (ForInStep.yield (Id.run (forIn (List.range' 0 k)
      (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2) (innerT sk st stB h))))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))

@[expose] def initT (root : α) (rootB : β) (key0 : Nat) : TSt α β :=
  (#[root], #[0], #[0], #[rootB], (∅ : Std.HashSet Nat).insert key0)

@[expose] def projT (s : TSt α β) : GSt α := (s.1, s.2.1, s.2.2.1, s.2.2.2.2)

theorem keyBfsT_eq (sk : Nat → α → Nat) (st : Nat → α → α) (stB : Nat → β → β) (k : Nat)
    (root : α) (rootB : β) (key0 cap : Nat) :
    (keyBfsT sk st stB k root rootB key0 cap).1 =
      (Id.run (forIn (List.range' 0 cap) (initT root rootB key0) (outerT sk st stB k))).1 := by
  unfold keyBfsT
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem keyBfsT_entries {κ : α → Nat} {sk : Nat → α → Nat} {st : Nat → α → α}
    {stB : Nat → β → β} {k : Nat} {root : α} {rootB : β} {key0 cap : Nat}
    (hsk : ∀ j x, sk j x = κ (st j x)) :
    (keyBfsT sk st stB k root rootB key0 cap).1 = (keyBfsG κ st k root key0 cap).1 := by
  have hin : ∀ h j (b : TSt α β), ∃ b', innerT sk st stB h j b = pure (ForInStep.yield b') ∧
      innerG κ st h j (projT b) = pure (ForInStep.yield (projT b')) := by
    intro h j b
    by_cases hc : b.2.2.2.2.contains (κ (st j b.1[h]!)) = true
    · refine ⟨(b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2), ?_, ?_⟩
      · simp only [innerT, hsk, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      · simp only [innerG, projT, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · have hnc : b.2.2.2.2.contains (κ (st j b.1[h]!)) = false := Bool.eq_false_iff.2 hc
      refine ⟨(b.1.push (st j b.1[h]!), b.2.1.push h, b.2.2.1.push j,
        b.2.2.2.1.push (stB j b.2.2.2.1[h]!), b.2.2.2.2.insert (κ (st j b.1[h]!))), ?_, ?_⟩
      · simp only [innerT, hsk, hnc, Bool.not_false, ↓reduceIte]
      · simp only [innerG, projT, hnc, Bool.not_false, ↓reduceIte]
  have hout : ∀ h (b : TSt α β), ∃ b', outerT sk st stB k h b = pure (ForInStep.yield b') ∧
      outerG κ st k h (projT b) = pure (ForInStep.yield (projT b')) := by
    intro h b
    by_cases hh : h < b.1.size
    · refine ⟨Id.run (forIn (List.range' 0 k) (b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2)
        (innerT sk st stB h)), by simp only [outerT, hh, ↓reduceIte], ?_⟩
      have e := forIn_sim projT (List.range' 0 k) (innerT sk st stB h) (innerG κ st h) (hin h) b
      simp only [outerG, projT, hh, ↓reduceIte] at e ⊢
      rw [e]
    · refine ⟨(b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2),
        by simp only [outerT, hh, ↓reduceIte], ?_⟩
      simp only [outerG, projT, hh, ↓reduceIte]
  have e := forIn_sim projT (List.range' 0 cap) (outerT sk st stB k) (outerG κ st k) hout
    (initT root rootB key0)
  rw [keyBfsT_eq, keyBfsG_eq]
  change _ = (Id.run (forIn (List.range' 0 cap) (projT (initT root rootB key0))
    (outerG κ st k))).1
  rw [e]
  rfl

end

end CFSG.KS.KeyBfsG

end
