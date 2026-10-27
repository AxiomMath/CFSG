module

public import Certificates.Data.Kernel.SlpRel
public import Aesop.BuiltinRules
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.KS.SlpRel

open CFSG.KC.SlpRel

variable {α : Type} {G : Type*} [Monoid G]

@[expose] def slpG (prog : List (List Nat)) (R : List G) : List G :=
  prog.foldl (fun R w => R ++ [(w.map fun l => R.getD (l - 1) 1).prod]) R

@[expose] def wordV (mul : α → α → α) (one : α) (R : List α) (w : List Nat) (acc : α) : α :=
  w.foldl (fun a l => mul a (R.getD (l - 1) one)) acc

@[expose] def slpV (mul : α → α → α) (one : α) (prog : List (List Nat)) (R : List α) : List α :=
  prog.foldl (fun R w => R ++ [wordV mul one R w one]) R

@[expose] def RepL (Rep : α → G → Prop) (one : α) (R : List α) (RG : List G) : Prop :=
  R.length = RG.length ∧ ∀ i, Rep (R.getD i one) (RG.getD i 1)

theorem strictB_eq (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem getD_push {β : Type*} (L : List β) (y d : β) (n : ℕ) :
    (L ++ [y]).getD n d = if n < L.length then L.getD n d else if n = L.length then y else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

section Sound

variable {frc : α → (α → Bool) → Bool} {mul : α → α → α} {one : α} {Rep : α → G → Prop}

theorem wordS_eq (hfrc : ∀ x k, frc x k = k x) (R : List α) (w : List Nat) :
    ∀ (acc : α) (k : α → Bool), wordS frc mul one R w acc k = k (wordV mul one R w acc) := by
  induction w with
  | nil => intro acc k; rfl
  | cons l w ih =>
    intro acc k
    change frc (mul acc (List.getD R (l - 1) one)) (fun acc => wordS frc mul one R w acc k) = _
    rw [hfrc]
    exact ih _ k

theorem slpS_eq (hfrc : ∀ x k, frc x k = k x) (prog : List (List Nat)) :
    ∀ (R : List α) (K : List α → Bool), slpS frc mul one prog R K = K (slpV mul one prog R) := by
  induction prog with
  | nil => intro R K; rfl
  | cons w prog ih =>
    intro R K
    change wordS frc mul one R w one (fun x => slpS frc mul one prog (R ++ [x]) K) = _
    rw [wordS_eq hfrc]
    exact ih _ K

variable (hmul : ∀ X Y g h, Rep X g → Rep Y h → Rep (mul X Y) (g * h)) (hone : Rep one 1)
include hmul

theorem wordV_rep {R : List α} {RG : List G} (hR : RepL Rep one R RG) :
    ∀ (w : List Nat) (acc : α) (x : G), Rep acc x →
      Rep (wordV mul one R w acc) (x * (w.map fun l => RG.getD (l - 1) 1).prod)
  | [], acc, x, h => by
    rw [List.map_nil, List.prod_nil, mul_one]
    exact h
  | l :: w, acc, x, h => by
    have := wordV_rep hR w (mul acc (R.getD (l - 1) one)) (x * RG.getD (l - 1) 1)
      (hmul _ _ _ _ h (hR.2 (l - 1)))
    rw [List.map_cons, List.prod_cons, ← mul_assoc]
    exact this

include hone

theorem repL_push {R : List α} {RG : List G} (hR : RepL Rep one R RG) {x : α} {g : G}
    (hx : Rep x g) : RepL Rep one (R ++ [x]) (RG ++ [g]) := by
  refine ⟨by simp [hR.1], fun i => ?_⟩
  rw [getD_push, getD_push, hR.1]
  split_ifs
  · exact hR.2 i
  · exact hx
  · exact hone

theorem slpV_rep (prog : List (List Nat)) :
    ∀ (R : List α) (RG : List G), RepL Rep one R RG →
      RepL Rep one (slpV mul one prog R) (slpG prog RG) := by
  induction prog with
  | nil => intro R RG h; exact h
  | cons w prog ih =>
    intro R RG h
    have hw := wordV_rep hmul h w one 1 hone
    rw [one_mul] at hw
    exact ih _ _ (repL_push hmul hone h hw)

omit hmul hone in
theorem pairsS_spec (hfrc : ∀ x k, frc x k = k x) {eq : α → α → Bool} (R : List α) :
    ∀ ps : List (List Nat × List Nat), pairsS frc mul one eq R ps = true →
      ∀ p ∈ ps, eq (wordV mul one R p.1 one) (wordV mul one R p.2 one) = true
  | [], _, p, hp => absurd hp List.not_mem_nil
  | q :: ps, h, p, hp => by
    have h' : wordS frc mul one R q.1 one (fun a => wordS frc mul one R q.2 one fun b =>
        bAnd(eq a b, pairsS frc mul one eq R ps)) = true := h
    simp only [wordS_eq hfrc] at h'
    cases e : eq (wordV mul one R q.1 one) (wordV mul one R q.2 one)
    · rw [e] at h'
      exact absurd h' Bool.false_ne_true
    · rw [e] at h'
      rcases List.mem_cons.1 hp with rfl | hp
      · exact e
      · exact pairsS_spec hfrc R ps h' p hp

omit hmul hone in
theorem nesS_spec {nz : α → Bool} (R : List α) :
    ∀ ne : List Nat, nesS nz one R ne = true → ∀ l ∈ ne, nz (R.getD (l - 1) one) = true
  | [], _, l, hl => absurd hl List.not_mem_nil
  | m :: ne, h, l, hl => by
    have h' : bAnd(nz (List.getD R (m - 1) one), nesS nz one R ne) = true := h
    cases e : nz (R.getD (m - 1) one)
    · rw [e] at h'
      exact absurd h' Bool.false_ne_true
    · rw [e] at h'
      rcases List.mem_cons.1 hl with rfl | hl
      · exact e
      · exact nesS_spec R ne h' l hl

theorem slpRelK_sound (hfrc : ∀ x k, frc x k = k x) {eq : α → α → Bool} {nz : α → Bool}
    (heq : ∀ X Y g h, Rep X g → Rep Y h → eq X Y = true → g = h)
    (hnz : ∀ X g, Rep X g → nz X = true → g ≠ 1) {init : List α} {gens : List G}
    (hinit : RepL Rep one init gens) {prog : List (List Nat)} {ps : List (List Nat × List Nat)}
    {ne : List Nat} (h : slpRelK frc mul one eq nz init prog ps ne = true) :
    (∀ p ∈ ps, (p.1.map fun l => (slpG prog gens).getD (l - 1) 1).prod =
      (p.2.map fun l => (slpG prog gens).getD (l - 1) 1).prod) ∧
      ∀ l ∈ ne, (slpG prog gens).getD (l - 1) 1 ≠ 1 := by
  unfold slpRelK at h
  simp only [slpS_eq hfrc] at h
  have hS := slpV_rep hmul hone prog init gens hinit
  cases e : pairsS frc mul one eq (slpV mul one prog init) ps
  · rw [e] at h
    exact absurd h Bool.false_ne_true
  · rw [e] at h
    refine ⟨fun p hp => ?_, fun l hl => hnz _ _ (hS.2 (l - 1)) (nesS_spec _ ne h l hl)⟩
    have hu := wordV_rep hmul hS p.1 one 1 hone
    have hv := wordV_rep hmul hS p.2 one 1 hone
    rw [one_mul] at hu hv
    exact heq _ _ _ _ hu hv (pairsS_spec hfrc _ ps e p hp)

end Sound

end CFSG.KS.SlpRel

end
