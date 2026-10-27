module

public import CFSG.Sporadic.Th.TableSpec
public import Certificates.Data.RouteP.Bridge
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.RouteP

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

variable {G : Type*} [Group G]

@[expose] def lineProd (π : ℕ → G) (l : List ℤ) : G :=
  ((pairsOf l).map fun p => π (p.1 - 1) ^ p.2).prod

theorem runSLPG_nil (regs : ℕ → G) : runSLPG [] regs = regs := rfl

theorem runSLPG_append (p q : List Instr) (regs : ℕ → G) :
    runSLPG (p ++ q) regs = runSLPG q (runSLPG p regs) := by
  unfold runSLPG
  rw [List.foldl_append]

theorem runSLPG_cons (ins : Instr) (p : List Instr) (regs : ℕ → G) :
    runSLPG (ins :: p) regs = runSLPG p (stepG regs ins) := rfl

theorem runSLPG_powInstrs (s i : ℕ) (e : ℤ) (regs : ℕ → G) :
    runSLPG (powInstrs s i e) regs = Function.update regs s (regs i ^ e) := by
  unfold powInstrs
  by_cases h1 : e = -1
  · subst h1
    rw [if_pos rfl]
    simp [runSLPG, stepG]
  · rw [if_neg h1]
    by_cases h2 : e < 0
    · rw [if_pos h2]
      simp only [runSLPG, List.foldl_cons, List.foldl_nil, stepG, Function.update_self,
        Function.update_idem]
      congr 1
      have e1 : ((-e).toNat : ℤ) = -e := Int.toNat_of_nonneg (by omega)
      rw [inv_pow, ← zpow_natCast, e1, ← zpow_neg, neg_neg]
    · rw [if_neg h2]
      simp only [runSLPG, List.foldl_cons, List.foldl_nil, stepG]
      congr 1
      have e1 : (e.toNat : ℤ) = e := Int.toNat_of_nonneg (by omega)
      rw [← zpow_natCast, e1]

theorem runSLPG_restInstrs (t sc : ℕ) (hts : t ≠ sc) (regs : ℕ → G) :
    ∀ (ps : List (ℕ × ℤ)) (S : ℕ → G) (acc : G), (∀ p ∈ ps, p.1 - 1 ≠ t ∧ p.1 - 1 ≠ sc) →
      S t = acc → (∀ r, r ≠ t → r ≠ sc → S r = regs r) →
      runSLPG (ps.flatMap fun p => if p.2 = 1 then [Instr.mu t (p.1 - 1) t]
          else powInstrs sc (p.1 - 1) p.2 ++ [Instr.mu t sc t]) S t =
          acc * (ps.map fun p => regs (p.1 - 1) ^ p.2).prod ∧
        ∀ r, r ≠ t → r ≠ sc →
          runSLPG (ps.flatMap fun p => if p.2 = 1 then [Instr.mu t (p.1 - 1) t]
            else powInstrs sc (p.1 - 1) p.2 ++ [Instr.mu t sc t]) S r = regs r
  | [], S, acc, _, h1, h2 => by
    simp only [List.flatMap_nil, List.map_nil, List.prod_nil, mul_one]
    exact ⟨h1, h2⟩
  | p :: ps, S, acc, hp, h1, h2 => by
    rw [List.flatMap_cons, runSLPG_append, List.map_cons, List.prod_cons, ← mul_assoc]
    have hp0 := hp p List.mem_cons_self
    have hps : ∀ q ∈ ps, q.1 - 1 ≠ t ∧ q.1 - 1 ≠ sc := fun q hq => hp q (List.mem_cons_of_mem _ hq)
    have hreg : S (p.1 - 1) = regs (p.1 - 1) := h2 _ hp0.1 hp0.2
    by_cases he : p.2 = 1
    · rw [if_pos he]
      apply runSLPG_restInstrs t sc hts regs ps _ _ hps
      · simp only [runSLPG, List.foldl_cons, List.foldl_nil, stepG, Function.update_self]
        rw [h1, hreg, he, zpow_one]
      · intro r hr1 hr2
        simp only [runSLPG, List.foldl_cons, List.foldl_nil, stepG]
        rw [Function.update_of_ne hr1]
        exact h2 r hr1 hr2
    · rw [if_neg he, runSLPG_append, runSLPG_powInstrs]
      apply runSLPG_restInstrs t sc hts regs ps _ _ hps
      · simp only [runSLPG, List.foldl_cons, List.foldl_nil, stepG, Function.update_self]
        rw [Function.update_of_ne hts, h1, hreg]
      · intro r hr1 hr2
        simp only [runSLPG, List.foldl_cons, List.foldl_nil, stepG]
        rw [Function.update_of_ne hr1, Function.update_of_ne hr2]
        exact h2 r hr1 hr2

theorem runSLPG_lineInstrs (t sc : ℕ) (hts : t ≠ sc) (ps : List (ℕ × ℤ)) (regs : ℕ → G)
    (hp : ∀ p ∈ ps, p.1 - 1 ≠ t ∧ p.1 - 1 ≠ sc) :
    runSLPG (lineInstrs t sc ps) regs t = (ps.map fun p => regs (p.1 - 1) ^ p.2).prod ∧
      ∀ r, r ≠ t → r ≠ sc → runSLPG (lineInstrs t sc ps) regs r = regs r := by
  cases ps with
  | nil =>
    refine ⟨?_, fun r hr _ => ?_⟩
    · simp [lineInstrs, runSLPG, stepG]
    · simp only [lineInstrs, runSLPG, List.foldl_cons, List.foldl_nil, stepG]
      exact Function.update_of_ne hr _ _
  | cons p ps =>
    have hp0 := hp p List.mem_cons_self
    have hps : ∀ q ∈ ps, q.1 - 1 ≠ t ∧ q.1 - 1 ≠ sc := fun q hq => hp q (List.mem_cons_of_mem _ hq)
    unfold lineInstrs
    rw [runSLPG_append, runSLPG_powInstrs, List.map_cons, List.prod_cons]
    exact runSLPG_restInstrs t sc hts regs ps _ _ hps (Function.update_self _ _ _)
      (fun r hr _ => Function.update_of_ne hr _ _)

@[expose] def LinesOK (g : ℕ) (ls : Array (List ℤ)) : Prop :=
  ∀ ℓ < ls.size, ∀ p ∈ pairsOf ls[ℓ]!, 1 ≤ p.1 ∧ p.1 ≤ g + ℓ

theorem compileSLP_eq (g : ℕ) (ls : Array (List ℤ)) :
    compileSLP g ls = (List.range ls.size).flatMap fun l =>
      lineInstrs (g + l) (g + ls.size) (pairsOf ls[l]!) := rfl

theorem runSLPG_flatMap (f : ℕ → List Instr) (regs : ℕ → G) (k : ℕ) :
    runSLPG ((List.range (k + 1)).flatMap f) regs =
      runSLPG (f k) (runSLPG ((List.range k).flatMap f) regs) := by
  rw [List.range_succ, List.flatMap_append, runSLPG_append, List.flatMap_singleton]

private theorem compile_prefix (g : ℕ) (ls : Array (List ℤ)) (hls : LinesOK g ls) (regs : ℕ → G) :
    ∀ k ≤ ls.size,
      (∀ r, (r < g ∨ (g + k ≤ r ∧ r ≠ g + ls.size)) →
        runSLPG ((List.range k).flatMap fun l =>
          lineInstrs (g + l) (g + ls.size) (pairsOf ls[l]!)) regs r = regs r) ∧
      ∀ ℓ < k, runSLPG ((List.range k).flatMap fun l =>
          lineInstrs (g + l) (g + ls.size) (pairsOf ls[l]!)) regs (g + ℓ) =
        lineProd (runSLPG ((List.range k).flatMap fun l =>
          lineInstrs (g + l) (g + ls.size) (pairsOf ls[l]!)) regs) ls[ℓ]! := by
  intro k
  induction k with
  | zero => intro _; exact ⟨fun r _ => rfl, fun ℓ hℓ => absurd hℓ (Nat.not_lt_zero ℓ)⟩
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    set S := runSLPG ((List.range k).flatMap fun l =>
      lineInstrs (g + l) (g + ls.size) (pairsOf ls[l]!)) regs with hS
    rw [runSLPG_flatMap]
    have hp : ∀ p ∈ pairsOf ls[k]!, p.1 - 1 ≠ g + k ∧ p.1 - 1 ≠ g + ls.size := by
      intro p hp
      have := hls k (by omega) p hp
      omega
    obtain ⟨hl1, hl2⟩ := runSLPG_lineInstrs (g + k) (g + ls.size) (by omega) _ S hp
    have hfac : ∀ ℓ ≤ k, ∀ p ∈ pairsOf ls[ℓ]!,
        runSLPG (lineInstrs (g + k) (g + ls.size) (pairsOf ls[k]!)) S (p.1 - 1) = S (p.1 - 1) := by
      intro ℓ hℓ p hp
      have := hls ℓ (by omega) p hp
      exact hl2 _ (by omega) (by omega)
    have hlp : ∀ ℓ ≤ k, lineProd (runSLPG (lineInstrs (g + k) (g + ls.size) (pairsOf ls[k]!)) S)
        ls[ℓ]! = lineProd S ls[ℓ]! := by
      intro ℓ hℓ
      unfold lineProd
      congr 1
      exact List.map_congr_left fun p hp => by rw [hfac ℓ hℓ p hp]
    refine ⟨fun r hr => ?_, fun ℓ hℓ => ?_⟩
    · rw [hl2 r (by omega) (by omega)]
      exact ih1 r (by omega)
    · rw [hlp ℓ (by omega)]
      by_cases e : ℓ = k
      · subst e
        rw [hl1]
        rfl
      · rw [hl2 _ (by omega) (by omega)]
        exact ih2 ℓ (by omega)

theorem runSLPG_compileSLP_lt (g : ℕ) (ls : Array (List ℤ)) (hls : LinesOK g ls)
    (regs : ℕ → G) {r : ℕ} (hr : r < g) : runSLPG (compileSLP g ls) regs r = regs r :=
  (compile_prefix g ls hls regs ls.size le_rfl).1 r (Or.inl hr)

theorem runSLPG_compileSLP_line (g : ℕ) (ls : Array (List ℤ)) (hls : LinesOK g ls)
    (regs : ℕ → G) {ℓ : ℕ} (hℓ : ℓ < ls.size) :
    runSLPG (compileSLP g ls) regs (g + ℓ) =
      lineProd (runSLPG (compileSLP g ls) regs) ls[ℓ]! :=
  (compile_prefix g ls hls regs ls.size le_rfl).2 ℓ hℓ

theorem instrRegsLt_of_progOK' {r : ℕ} {prog : List Instr} (h : progOK r prog = true) :
    ∀ ins ∈ prog, instrRegsLt r ins := by
  intro ins hins
  have := List.all_eq_true.1 h ins hins
  cases ins <;> simp_all [instrRegsLt]

end CFSG.KS.RouteP

end
