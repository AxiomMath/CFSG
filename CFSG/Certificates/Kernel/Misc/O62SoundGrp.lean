module

public import CFSG.Certificates.Kernel.Misc.O62SoundBits

public section

namespace CFSG.KC.Misc.O62

open CFSG.LargeExtraspecial.O62

structure ElAb (E : List ℕ) : Prop where
  lt : ∀ a ∈ E, a < 2 ^ 36
  one_mem : Code.one ∈ E
  mul_mem : ∀ a ∈ E, ∀ b ∈ E, Code.mul a b ∈ E
  comm : ∀ a ∈ E, ∀ b ∈ E, Code.mul a b = Code.mul b a
  sq : ∀ a ∈ E, Code.mul a a = Code.one

structure SubG (E S : List ℕ) : Prop where
  elAb : ElAb S
  sub : ∀ a ∈ S, a ∈ E
  nodup : S.Nodup

theorem ElAb.congr {S T : List ℕ} (h : ∀ a, a ∈ S ↔ a ∈ T) (hS : ElAb S) : ElAb T where
  lt a ha := hS.lt a ((h a).2 ha)
  one_mem := (h _).1 hS.one_mem
  mul_mem a ha b hb := (h _).1 (hS.mul_mem a ((h a).2 ha) b ((h b).2 hb))
  comm a ha b hb := hS.comm a ((h a).2 ha) b ((h b).2 hb)
  sq a ha := hS.sq a ((h a).2 ha)

theorem mul_mul_self {s x : ℕ} (hs : s < 2 ^ 36) (hx : Code.mul x x = Code.one) :
    Code.mul (Code.mul s x) x = s := by
  rw [cmul_assoc, hx, cmul_one hs]

theorem mul_x_mul {s x : ℕ} (hs : s < 2 ^ 36) (hx : Code.mul x x = Code.one)
    (hc : Code.mul s x = Code.mul x s) : Code.mul x (Code.mul s x) = s := by
  rw [← cmul_assoc, ← hc, mul_mul_self hs hx]

theorem mul_trans_trans {s s' x : ℕ} (hs' : s' < 2 ^ 36)
    (hx : Code.mul x x = Code.one) (hc : Code.mul s' x = Code.mul x s') :
    Code.mul (Code.mul s x) (Code.mul s' x) = Code.mul s s' := by
  rw [cmul_assoc, mul_x_mul hs' hx hc]

theorem mul_trans_left {s s' x : ℕ} (hc : Code.mul s' x = Code.mul x s') :
    Code.mul (Code.mul s x) s' = Code.mul (Code.mul s s') x := by
  rw [cmul_assoc, ← hc, ← cmul_assoc]

theorem elAb_step {S : List ℕ} {x : ℕ} (hS : ElAb S)
    (hxx : Code.mul x x = Code.one) (hxc : ∀ s ∈ S, Code.mul s x = Code.mul x s) :
    ElAb (S ++ S.map fun s => Code.mul s x) where
  lt a ha := by
    rcases List.mem_append.1 ha with h | h
    · exact hS.lt a h
    · obtain ⟨s, _, rfl⟩ := List.mem_map.1 h
      exact Code.mul_lt _ _
  one_mem := List.mem_append_left _ hS.one_mem
  mul_mem a ha b hb := by
    rcases List.mem_append.1 ha with ha | ha <;> rcases List.mem_append.1 hb with hb | hb
    · exact List.mem_append_left _ (hS.mul_mem a ha b hb)
    · obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hb
      refine List.mem_append_right _ (List.mem_map.2 ⟨Code.mul a s', hS.mul_mem a ha s' hs', ?_⟩)
      show Code.mul (Code.mul a s') x = _
      rw [cmul_assoc]
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
      refine List.mem_append_right _ (List.mem_map.2 ⟨Code.mul s b, hS.mul_mem s hs b hb, ?_⟩)
      show Code.mul (Code.mul s b) x = _
      rw [mul_trans_left (hxc b hb)]
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
      obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hb
      exact List.mem_append_left _ (by
        rw [mul_trans_trans (hS.lt s' hs') hxx (hxc s' hs')]
        exact hS.mul_mem s hs s' hs')
  comm a ha b hb := by
    rcases List.mem_append.1 ha with ha | ha <;> rcases List.mem_append.1 hb with hb | hb
    · exact hS.comm a ha b hb
    · obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hb
      rw [mul_trans_left (hxc a ha), ← cmul_assoc, hS.comm a ha s' hs']
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
      rw [mul_trans_left (hxc b hb), ← cmul_assoc, hS.comm s hs b hb]
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
      obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hb
      rw [mul_trans_trans (hS.lt s' hs') hxx (hxc s' hs'),
        mul_trans_trans (hS.lt s hs) hxx (hxc s hs)]
      exact hS.comm s hs s' hs'
  sq a ha := by
    rcases List.mem_append.1 ha with ha | ha
    · exact hS.sq a ha
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
      rw [mul_trans_trans (hS.lt s hs) hxx (hxc s hs), hS.sq s hs]

theorem nodup_step {S : List ℕ} {x : ℕ} (hS : ElAb S) (hn : S.Nodup) (hxl : x < 2 ^ 36)
    (hxx : Code.mul x x = Code.one) (hx : x ∉ S) :
    (S ++ S.map fun s => Code.mul s x).Nodup := by
  rw [List.nodup_append]
  refine ⟨hn, hn.map_on ?_, ?_⟩
  · intro s hs s' hs' h
    have := congrArg (fun t => Code.mul t x) h
    simpa only [mul_mul_self (hS.lt s hs) hxx, mul_mul_self (hS.lt s' hs') hxx] using this
  · intro b hb a ha hba
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
    apply hx
    have hsx : x = Code.mul s (Code.mul s x) := by
      rw [← cmul_assoc, hS.sq s hs, one_cmul hxl]
    rw [hsx, ← hba]
    exact hS.mul_mem s hs b hb

theorem spanC_comm : ∀ (xs : List ℕ) (x : ℕ), x < 2 ^ 36 → (∀ y ∈ xs, y < 2 ^ 36) →
    (∀ y ∈ xs, Code.mul y x = Code.mul x y) →
    ∀ s ∈ Check.spanC xs, Code.mul s x = Code.mul x s
  | [], x, hx, _, _, s, hs => by
    have : s = Code.one := by simpa [Check.spanC] using hs
    subst this
    rw [one_cmul hx, cmul_one hx]
  | y :: xs, x, hx, hl, hc, s, hs => by
    have hy : Code.mul y x = Code.mul x y := hc y (List.mem_cons_self ..)
    have hyl : y < 2 ^ 36 := hl y (List.mem_cons_self ..)
    have ih := spanC_comm xs x hx (fun z hz => hl z (List.mem_cons_of_mem _ hz))
      (fun z hz => hc z (List.mem_cons_of_mem _ hz))
    rcases List.mem_append.1 (show s ∈ Check.spanC xs ++ (Check.spanC xs).map
        (fun c => Code.mul c y) from hs) with h | h
    · exact ih s h
    · obtain ⟨c, hcs, rfl⟩ := List.mem_map.1 h
      show Code.mul (Code.mul c y) x = Code.mul x (Code.mul c y)
      rw [cmul_assoc, hy, ← cmul_assoc, ih c hcs, cmul_assoc]

theorem spanC_elAb : ∀ (xs : List ℕ), (∀ x ∈ xs, x < 2 ^ 36) →
    (∀ x ∈ xs, Code.mul x x = Code.one) →
    xs.Pairwise (fun a b => Code.mul a b = Code.mul b a) → ElAb (Check.spanC xs)
  | [], _, _, _ => by
    refine ⟨?_, by simp [Check.spanC], ?_, ?_, ?_⟩ <;> simp only [Check.spanC, List.mem_singleton]
    · rintro a rfl; exact Code.one_lt
    · rintro a rfl b rfl; exact cmul_one Code.one_lt
    · rintro a rfl b rfl; rfl
    · rintro a rfl; exact cmul_one Code.one_lt
  | x :: xs, hl, hs, hp => by
    have ih := spanC_elAb xs (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      (fun y hy => hs y (List.mem_cons_of_mem _ hy)) (List.pairwise_cons.1 hp).2
    exact elAb_step ih (hs x (List.mem_cons_self ..))
      (spanC_comm xs x (hl x (List.mem_cons_self ..)) (fun y hy => hl y (List.mem_cons_of_mem _ hy))
        (fun y hy => ((List.pairwise_cons.1 hp).1 y hy).symm))

def Indep : List ℕ → Prop
  | [] => True
  | x :: xs => x ∉ Check.spanC xs ∧ Indep xs

theorem Indep.nil : Indep [] := trivial

theorem Indep.cons {x : ℕ} {xs : List ℕ} (h : x ∉ Check.spanC xs) (hi : Indep xs) :
    Indep (x :: xs) := ⟨h, hi⟩

theorem spanC_nodup : ∀ (xs : List ℕ), (∀ x ∈ xs, x < 2 ^ 36) →
    (∀ x ∈ xs, Code.mul x x = Code.one) →
    xs.Pairwise (fun a b => Code.mul a b = Code.mul b a) → Indep xs → (Check.spanC xs).Nodup
  | [], _, _, _, _ => by simp [Check.spanC]
  | x :: xs, hl, hs, hp, hi => by
    have hl' : ∀ y ∈ xs, y < 2 ^ 36 := fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hs' : ∀ y ∈ xs, Code.mul y y = Code.one := fun y hy => hs y (List.mem_cons_of_mem _ hy)
    have hp' := (List.pairwise_cons.1 hp).2
    exact nodup_step (spanC_elAb xs hl' hs' hp') (spanC_nodup xs hl' hs' hp' hi.2)
      (hl x (List.mem_cons_self ..)) (hs x (List.mem_cons_self ..)) hi.1

theorem length_spanC (xs : List ℕ) : (Check.spanC xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show (Check.spanC xs ++ (Check.spanC xs).map fun c => Code.mul c x).length = _
    rw [List.length_append, List.length_map, ih, List.length_cons, Nat.pow_succ]
    omega

theorem exists_not_mem {E S : List ℕ} (hE : E.Nodup)
    (hlen : S.length < E.length) : ∃ e ∈ E, e ∉ S := by
  by_contra h
  push Not at h
  have := (hE.subperm h).length_le
  omega

theorem spanC_sub {IL : List ℕ}
    (hlt : ∀ a ∈ IL, a < 2 ^ 36)
    (hcl : ∀ a ∈ IL, ∀ b ∈ IL, a ≠ b → Code.mul a b = Code.mul b a → Code.mul a b ∈ IL) :
    ∀ (xs : List ℕ), (∀ x ∈ xs, x ∈ IL) → (∀ x ∈ xs, Code.mul x x = Code.one) →
    xs.Pairwise (fun a b => Code.mul a b = Code.mul b a) → Indep xs →
    ∀ a ∈ Check.spanC xs, a ≠ Code.one → a ∈ IL
  | [], _, _, _, _, a, ha, hne => by
    exact absurd (by simpa [Check.spanC] using ha) hne
  | x :: xs, hx, hs, hp, hi, a, ha, hne => by
    have hxIL : x ∈ IL := hx x (List.mem_cons_self ..)
    have ih := spanC_sub hlt hcl xs (fun y hy => hx y (List.mem_cons_of_mem _ hy))
      (fun y hy => hs y (List.mem_cons_of_mem _ hy)) (List.pairwise_cons.1 hp).2 hi.2
    rcases List.mem_append.1 (show a ∈ Check.spanC xs ++ (Check.spanC xs).map
        (fun c => Code.mul c x) from ha) with h | h
    · exact ih a h hne
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
      by_cases hc1 : c = Code.one
      · subst hc1
        show Code.mul Code.one x ∈ IL
        rw [one_cmul (hlt x hxIL)]
        exact hxIL
      · have hcIL : c ∈ IL := ih c hc hc1
        have hcx : c ≠ x := fun h => hi.1 (h ▸ hc)
        have hcomm : Code.mul c x = Code.mul x c :=
          spanC_comm xs x (hlt x hxIL) (fun y hy => hlt y (hx y (List.mem_cons_of_mem _ hy)))
            (fun y hy => ((List.pairwise_cons.1 hp).1 y hy).symm) c hc
        exact hcl c hcIL x hxIL hcx hcomm

theorem subG_step {E S : List ℕ} {x : ℕ} (hE : ElAb E) (hS : SubG E S) (hx : x ∈ E)
    (hxS : x ∉ S) : SubG E ((S.map fun s => Code.mul s x).reverse ++ S) := by
  have hxc : ∀ s ∈ S, Code.mul s x = Code.mul x s := fun s hs => hE.comm s (hS.sub s hs) x hx
  have hmem : ∀ a, a ∈ S ++ S.map (fun s => Code.mul s x) ↔
      a ∈ (S.map fun s => Code.mul s x).reverse ++ S := by
    intro a; simp only [List.mem_append, List.mem_reverse]; tauto
  have hperm : ((S.map fun s => Code.mul s x).reverse ++ S).Perm
      (S ++ S.map fun s => Code.mul s x) :=
    ((List.reverse_perm _).append_right S).trans List.perm_append_comm
  refine ⟨(elAb_step hS.elAb (hE.sq x hx) hxc).congr hmem, ?_,
    hperm.nodup_iff.2 (nodup_step hS.elAb hS.nodup (hE.lt x hx) (hE.sq x hx) hxS)⟩
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 h)
    exact hE.mul_mem s (hS.sub s hs) x hx
  · exact hS.sub a h

theorem pairwise_five {α : Type} {R : α → α → Prop} {a b c d e : α}
    (hab : R a b) (hac : R a c) (had : R a d) (hae : R a e) (hbc : R b c) (hbd : R b d)
    (hbe : R b e) (hcd : R c d) (hce : R c e) (hde : R d e) : [a, b, c, d, e].Pairwise R := by
  simp [List.pairwise_cons, *]

end CFSG.KC.Misc.O62

end
