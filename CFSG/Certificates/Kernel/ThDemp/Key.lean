module

public import Certificates.Data.Kernel.ThDemp.Orb
public import CFSG.Certificates.Kernel.Th.Spec.Big
import Mathlib.Tactic.Abel
public import Mathlib.LinearAlgebra.Span.Defs

public section

namespace CFSG.Certificates.ThDemp.Key

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThDemp

theorem combsL_nil (base : ℕ) : combsL [] base = [base] := rfl

theorem combsL_cons (b : ℕ) (l : List ℕ) (base : ℕ) :
    combsL (b :: l) base = combsL l base ++ combsL l (base ^^^ b) := rfl

@[expose] noncomputable def xa (l : List ℕ) : ℕ := l.foldr (fun v acc => and5 v ^^^ acc) 0

theorem xa_append (l l' : List ℕ) : xa (l ++ l') = xa l ^^^ xa l' := by
  induction l with
  | nil => simp [xa]
  | cons a l ih =>
    simp only [xa, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, Nat.xor_assoc]

theorem subX_eq : ∀ (bs : List ℕ) (base : ℕ), subX bs base = xa (combsL bs base)
  | [], base => by simp [subX, combsL_nil, xa]
  | b :: l, base => by
    rw [combsL_cons, xa_append, ← subX_eq l base, ← subX_eq l (base ^^^ b)]
    rfl

theorem xa_perm {l l' : List ℕ} (h : l.Perm l') : xa l = xa l' := by
  unfold xa
  have : LeftCommutative (fun v acc : ℕ => and5 v ^^^ acc) :=
    ⟨fun a b c => by rw [← Nat.xor_assoc, ← Nat.xor_assoc, Nat.xor_comm (and5 a)]⟩
  exact List.Perm.foldr_eq h 0

@[expose] def spanL (l : List ℕ) : Submodule (ZMod 2) (Fin 248 → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ b ∈ l, v = pkVec b}

theorem spanL_nil : spanL [] = ⊥ := by
  rw [spanL, Submodule.span_eq_bot]
  rintro w ⟨c, hc, -⟩
  simp at hc

theorem spanL_cons (b : ℕ) (l : List ℕ) : spanL (b :: l) = (ZMod 2) ∙ pkVec b ⊔ spanL l := by
  rw [spanL, spanL, ← Submodule.span_insert]
  congr 1
  ext w
  simp only [List.mem_cons, Set.mem_setOf_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨c, hc | hc, rfl⟩
    · left
      rw [hc]
    · right
      exact ⟨c, hc, rfl⟩
  · rintro (rfl | ⟨c, hc, rfl⟩)
    · exact ⟨b, Or.inl rfl, rfl⟩
    · exact ⟨c, Or.inr hc, rfl⟩

theorem spanL_mono (b : ℕ) (l : List ℕ) : spanL l ≤ spanL (b :: l) := by
  rw [spanL_cons]
  exact le_sup_right

theorem mem_spanL_cons (b : ℕ) (l : List ℕ) : pkVec b ∈ spanL (b :: l) := by
  rw [spanL_cons]
  exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)

@[expose] def LIL : List ℕ → Prop
  | [] => True
  | b :: l => pkVec b ∉ spanL l ∧ LIL l

theorem mem_combs : ∀ (bs : List ℕ) (base : ℕ), base < 2 ^ 248 → (∀ b ∈ bs, b < 2 ^ 248) →
    ∀ x ∈ combsL bs base, x < 2 ^ 248 ∧ pkVec x - pkVec base ∈ spanL bs
  | [], base, hb, _, x, hx => by
    rw [combsL_nil, List.mem_singleton] at hx
    subst hx
    exact ⟨hb, by simp⟩
  | b :: l, base, hb, hl, x, hx => by
    have hbl : b < 2 ^ 248 := hl b (by simp)
    have hl' : ∀ c ∈ l, c < 2 ^ 248 := fun c hc => hl c (by simp [hc])
    rw [combsL_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨h1, h2⟩ := mem_combs l base hb hl' x hx
      exact ⟨h1, spanL_mono b l h2⟩
    · obtain ⟨h1, h2⟩ := mem_combs l (base ^^^ b) (Nat.xor_lt_two_pow hb hbl) hl' x hx
      refine ⟨h1, ?_⟩
      rw [pkVec_xor] at h2
      have e : pkVec x - pkVec base = (pkVec x - (pkVec base + pkVec b)) + pkVec b := by abel
      rw [e]
      exact Submodule.add_mem _ (spanL_mono b l h2) (mem_spanL_cons b l)

theorem exists_combs : ∀ (bs : List ℕ) (base : ℕ), ∀ v ∈ spanL bs,
    ∃ x ∈ combsL bs base, pkVec x = pkVec base + v
  | [], base, v, hv => by
    rw [spanL_nil, Submodule.mem_bot] at hv
    exact ⟨base, by simp [combsL_nil], by rw [hv, add_zero]⟩
  | b :: l, base, v, hv => by
    rw [spanL_cons, Submodule.mem_sup] at hv
    obtain ⟨u, hu, w, hw, rfl⟩ := hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have ht : t = 0 ∨ t = 1 := (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) t
    rcases ht with rfl | rfl
    · obtain ⟨x, hx, e⟩ := exists_combs l base w hw
      exact ⟨x, by rw [combsL_cons, List.mem_append]; exact Or.inl hx, by rw [e]; simp⟩
    · obtain ⟨x, hx, e⟩ := exists_combs l (base ^^^ b) w hw
      refine ⟨x, by rw [combsL_cons, List.mem_append]; exact Or.inr hx, ?_⟩
      rw [e, pkVec_xor, one_smul]
      abel

theorem nodup_combs : ∀ (bs : List ℕ) (base : ℕ),
    (∀ b ∈ bs, b < 2 ^ 248) → base < 2 ^ 248 → LIL bs → (combsL bs base).Nodup
  | [], _, _, _, _ => by simp [combsL_nil]
  | b :: l, base, hl, hb, hli => by
    have hbl : b < 2 ^ 248 := hl b (by simp)
    have hl' : ∀ c ∈ l, c < 2 ^ 248 := fun c hc => hl c (by simp [hc])
    obtain ⟨hbspan, hli'⟩ := hli
    rw [combsL_cons, List.nodup_append]
    refine ⟨nodup_combs l base hl' hb hli',
      nodup_combs l (base ^^^ b) hl' (Nat.xor_lt_two_pow hb hbl) hli', ?_⟩
    intro x hx y hy hxy
    subst hxy
    obtain ⟨-, h1⟩ := mem_combs l base hb hl' x hx
    obtain ⟨-, h2⟩ := mem_combs l (base ^^^ b) (Nat.xor_lt_two_pow hb hbl) hl' x hy
    rw [pkVec_xor] at h2
    apply hbspan
    have e : pkVec b = (pkVec x - pkVec base) - (pkVec x - (pkVec base + pkVec b)) := by abel
    rw [e]
    exact Submodule.sub_mem _ h1 h2

theorem lil_of_nodup : ∀ (bs : List ℕ), (∀ b ∈ bs, b < 2 ^ 248) → (combsL bs 0).Nodup → LIL bs
  | [], _, _ => trivial
  | b :: l, hl, hnd => by
    have hbl : b < 2 ^ 248 := hl b (by simp)
    have hl' : ∀ c ∈ l, c < 2 ^ 248 := fun c hc => hl c (by simp [hc])
    rw [combsL_cons, List.nodup_append] at hnd
    obtain ⟨hnd1, hnd2, hdis⟩ := hnd
    refine ⟨fun hmem => ?_, lil_of_nodup l hl' hnd1⟩
    obtain ⟨x, hx, e⟩ := exists_combs l 0 (pkVec b) hmem
    rw [pkVec_zero, zero_add] at e
    have hxb : x = b := pkVec_inj (mem_combs l 0 (Nat.two_pow_pos _) hl' x hx).1 hbl e
    have hb2 : b ∈ combsL l (0 ^^^ b) := by
      obtain ⟨y, hy, e2⟩ := exists_combs l (0 ^^^ b) 0 (Submodule.zero_mem _)
      rw [add_zero] at e2
      have : y = 0 ^^^ b := pkVec_inj (mem_combs l (0 ^^^ b)
        (Nat.xor_lt_two_pow (Nat.two_pow_pos _) hbl) hl' y hy).1
        (Nat.xor_lt_two_pow (Nat.two_pow_pos _) hbl) e2
      rw [this] at hy
      simpa using hy
    exact hdis x hx b (by simpa using hb2) hxb

theorem xa_combs_eq {bs bs' : List ℕ} (hb : ∀ b ∈ bs, b < 2 ^ 248) (hb' : ∀ b ∈ bs', b < 2 ^ 248)
    (hl : LIL bs) (hl' : LIL bs') (h : spanL bs = spanL bs') :
    xa (combsL bs 0) = xa (combsL bs' 0) := by
  classical
  apply xa_perm
  apply List.perm_of_nodup_nodup_toFinset_eq (nodup_combs bs 0 hb (Nat.two_pow_pos _) hl)
    (nodup_combs bs' 0 hb' (Nat.two_pow_pos _) hl')
  ext x
  simp only [List.mem_toFinset]
  constructor
  · intro hx
    obtain ⟨hxl, hxs⟩ := mem_combs bs 0 (Nat.two_pow_pos _) hb x hx
    rw [pkVec_zero, sub_zero, h] at hxs
    obtain ⟨y, hy, e⟩ := exists_combs bs' 0 _ hxs
    rw [pkVec_zero, zero_add] at e
    rw [pkVec_inj hxl (mem_combs bs' 0 (Nat.two_pow_pos _) hb' y hy).1 e.symm]
    exact hy
  · intro hx
    obtain ⟨hxl, hxs⟩ := mem_combs bs' 0 (Nat.two_pow_pos _) hb' x hx
    rw [pkVec_zero, sub_zero, ← h] at hxs
    obtain ⟨y, hy, e⟩ := exists_combs bs 0 _ hxs
    rw [pkVec_zero, zero_add] at e
    rw [pkVec_inj hxl (mem_combs bs 0 (Nat.two_pow_pos _) hb y hy).1 e.symm]
    exact hy

theorem rowsOf_lt (P : ℕ) : ∀ b ∈ rowsOf (2 ^ 248 - 1) P, b < 2 ^ 248 := by
  intro b hb
  simp only [rowsOf, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) (by omega))

theorem keyL_eq_of_span {P Q : ℕ} (hP : LIL (rowsOf (2 ^ 248 - 1) P))
    (hQ : LIL (rowsOf (2 ^ 248 - 1) Q))
    (h : spanL (rowsOf (2 ^ 248 - 1) P) = spanL (rowsOf (2 ^ 248 - 1) Q)) :
    keyL (2 ^ 248 - 1) P = keyL (2 ^ 248 - 1) Q := by
  unfold keyL
  rw [subX_eq, subX_eq, xa_combs_eq (rowsOf_lt P) (rowsOf_lt Q) hP hQ h]

end CFSG.Certificates.ThDemp.Key

end
