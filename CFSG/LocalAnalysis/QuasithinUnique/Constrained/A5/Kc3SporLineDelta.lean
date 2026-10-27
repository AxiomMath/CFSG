module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporLine

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

abbrev V5 : Type := ↥(evenWeight 5)

instance instDecMemV5 : DecidablePred (· ∈ evenWeight 5) := fun x =>
  decidable_of_iff (isEven x) (mem_evenWeight_iff x).symm

instance instFintypeV5 : Fintype V5 := Subtype.fintype _

@[expose] def wt (x : V5) : ℕ := (Finset.univ.filter fun i : Fin 5 => x.1 i = 1).card

@[expose] def pairs5 : Finset (V5 × V5) :=
  Finset.univ.filter fun p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2

@[expose] def lab5 (p : V5 × V5) : ℕ := wt p.1 + wt p.2 + wt (p.1 + p.2)

@[expose] def swp (p : V5 × V5) : V5 × V5 := (p.2, p.1)

@[expose] def shr (p : V5 × V5) : V5 × V5 := (p.1, p.1 + p.2)

@[expose] def actP (σ : Perm (Fin 5)) (p : V5 × V5) : V5 × V5 := (vact σ p.1, vact σ p.2)

@[expose] def tw : ℕ → V5 × V5 → V5 × V5
  | 0 => fun p => p
  | 1 => swp
  | 2 => shr
  | 3 => fun p => swp (shr p)
  | 4 => fun p => shr (swp p)
  | _ => fun p => swp (shr (swp p))

@[expose] def vOf (a : ℕ) : Fin 5 → ZMod 2 := fun i => if a.testBit i then 1 else 0

theorem vOf_even {a : ℕ} (h : isEven (vOf a)) : vOf a ∈ evenWeight 5 := (mem_evenWeight_iff _).2 h

@[expose] def base6 : V5 × V5 :=
  (⟨vOf 3, vOf_even (by decide)⟩, ⟨vOf 6, vOf_even (by decide)⟩)

@[expose] def base8 : V5 × V5 :=
  (⟨vOf 3, vOf_even (by decide)⟩, ⟨vOf 12, vOf_even (by decide)⟩)

@[expose] def base10 : V5 × V5 :=
  (⟨vOf 15, vOf_even (by decide)⟩, ⟨vOf 23, vOf_even (by decide)⟩)

@[expose] def baseOf (s : ℕ) : V5 × V5 := if s = 6 then base6 else if s = 8 then base8 else base10

theorem card_class6 : (pairs5.filter fun p => lab5 p = 6).card = 60 := by decide +kernel

theorem card_class8 : (pairs5.filter fun p => lab5 p = 8).card = 90 := by decide +kernel

theorem card_class10 : (pairs5.filter fun p => lab5 p = 10).card = 60 := by decide +kernel

theorem lab5_cases : ∀ p ∈ pairs5, lab5 p = 6 ∨ lab5 p = 8 ∨ lab5 p = 10 := by decide +kernel

@[expose] def Reach (p q : V5 × V5) : Prop :=
  ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ ∃ t, t < 6 ∧ tw t (actP σ p) = q

instance (p q : V5 × V5) : Decidable (Reach p q) := by unfold Reach; infer_instance

theorem reach_from_base : ∀ s ∈ ({6, 8, 10} : Finset ℕ), ∀ q ∈ pairs5, lab5 q = s →
    Reach (baseOf s) q := by
  decide +kernel

theorem reach_to_base : ∀ s ∈ ({6, 8, 10} : Finset ℕ), ∀ p ∈ pairs5, lab5 p = s →
    Reach p (baseOf s) := by
  decide +kernel

structure Closed5 (S : Finset (V5 × V5)) : Prop where
  sub : S ⊆ pairs5
  act : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∀ p ∈ S, actP σ p ∈ S
  swp : ∀ p ∈ S, swp p ∈ S
  shr : ∀ p ∈ S, shr p ∈ S

theorem Closed5.tw {S : Finset (V5 × V5)} (h : Closed5 S) {t : ℕ} (ht : t < 6) {p : V5 × V5}
    (hp : p ∈ S) : tw t p ∈ S := by
  interval_cases t
  · exact hp
  · exact h.swp p hp
  · exact h.shr p hp
  · exact h.swp _ (h.shr p hp)
  · exact h.shr _ (h.swp p hp)
  · exact h.swp _ (h.shr _ (h.swp p hp))

theorem Closed5.reach {S : Finset (V5 × V5)} (h : Closed5 S) {p q : V5 × V5} (hp : p ∈ S)
    (hr : Reach p q) : q ∈ S := by
  obtain ⟨σ, hσ, t, ht, rfl⟩ := hr
  exact h.tw ht (h.act σ hσ p hp)

theorem Closed5.class_subset {S : Finset (V5 × V5)} (h : Closed5 S) {s : ℕ}
    (hs : s ∈ ({6, 8, 10} : Finset ℕ)) {p : V5 × V5} (hp : p ∈ S) (hps : lab5 p = s) :
    ∀ q ∈ pairs5, lab5 q = s → q ∈ S := by
  intro q hq hqs
  have hbase : baseOf s ∈ S :=
    h.reach hp (reach_to_base s hs p (h.sub hp) hps)
  exact h.reach hbase (reach_from_base s hs q hq hqs)

theorem pairs5_fiber {S : Finset (V5 × V5)} (h : Closed5 S) :
    S.card = 0 ∨ S.card = 60 ∨ S.card = 90 ∨ S.card = 120 ∨ S.card = 150 ∨ S.card = 210 := by
  classical
  have hmap : ∀ p ∈ S, lab5 p ∈ ({6, 8, 10} : Finset ℕ) := by
    intro p hp
    have := lab5_cases p (h.sub hp)
    simpa using this
  have hsum := Finset.card_eq_sum_card_fiberwise hmap
  have hfib : ∀ s ∈ ({6, 8, 10} : Finset ℕ), ∀ c : ℕ,
      (pairs5.filter fun p => lab5 p = s).card = c →
      ((S.filter fun p => lab5 p = s).card = 0 ∨ (S.filter fun p => lab5 p = s).card = c) := by
    intro s hs c hc
    by_cases hne : ∃ p ∈ S, lab5 p = s
    · right
      obtain ⟨p, hp, hps⟩ := hne
      have : S.filter (fun p => lab5 p = s) = pairs5.filter fun p => lab5 p = s := by
        ext q
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hq, hqs⟩
          exact ⟨h.sub hq, hqs⟩
        · rintro ⟨hq, hqs⟩
          exact ⟨h.class_subset hs hp hps q hq hqs, hqs⟩
      rw [this, hc]
    · left
      push Not at hne
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q hq
      exact hne q hq
  rw [hsum]
  have h6 := hfib 6 (by decide) 60 card_class6
  have h8 := hfib 8 (by decide) 90 card_class8
  have h10 := hfib 10 (by decide) 60 card_class10
  rw [show ({6, 8, 10} : Finset ℕ) = insert 6 (insert 8 {10}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  omega

end CFSG.QuasithinUnique.A5.Kc3SporLine
