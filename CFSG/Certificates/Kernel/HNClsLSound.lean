module

public import Certificates.Data.Kernel.HNClsL
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KS.HNClsL

open CFSG.KC.Ord CFSG.KC.SlpPc CFSG.KC.HNClsL

variable {G : Type*} [Group G]

@[expose] def lw (lt : ℕ → G) (cs : List ℕ) : G := (cs.map lt).prod

@[expose] noncomputable def pw (lt : ℕ → G) (pool : List (List ℕ)) (j : ℕ) : G :=
  lw lt (nthD [] pool j)

@[expose] noncomputable def sp (lt : ℕ → G) (pool : List (List ℕ)) (s : List (ℕ × ℕ)) : G :=
  (s.map fun p => pw lt pool p.1 ^ p.2).prod

@[expose] noncomputable def spI (lt : ℕ → G) (pool : List (List ℕ)) (s : List (ℕ × ℕ)) : G :=
  (s.reverse.map fun p => lw lt (invW (nthD [] pool p.1)) ^ p.2).prod

structure Model (mul : ℕ → ℕ → ℕ) (ONE : ℕ) (Can : ℕ → Prop) (ev : ℕ → G) : Prop where
  one : Can ONE ∧ ev ONE = 1
  mul : ∀ {a b : ℕ}, Can a → Can b → Can (mul a b) ∧ ev (mul a b) = ev a * ev b
  inj : ∀ {a b : ℕ}, Can a → Can b → ev a = ev b → a = b

structure Raw (lt : ℕ → G) (pool : List (List ℕ)) (gens : List ℕ) (nQ : ℕ)
    (lines wl : List (List (ℕ × ℕ))) : Prop where
  alph : (∀ j < 17, lt j * lt (17 + j) = 1) ∧ lt 35 * (lt 35 * lt 35) = 1 ∧ lt 36 * lt 36 = 1
  codes : ∀ w ∈ pool, ∀ c ∈ w, okC c = true
  gen : ∀ j ∈ gens, evC (nthD [] pool j) = true ∧
    pw lt pool j * pw lt pool 0 = pw lt pool 0 * pw lt pool j
  tree : ∃ ks : List G, ks.length = nQ ∧ ks.Nodup ∧ (1 : G) ∈ ks ∧
    (∀ k ∈ ks, ∀ j ∈ gens, pw lt pool j * k ∈ ks) ∧
    (∀ k ∈ ks, k ∈ Submonoid.closure {x : G | ∃ j ∈ gens, x = pw lt pool j}) ∧
    ∀ k ∈ ks, k = 1 ∨ ∃ n < lines.length, ∃ e : ℕ, 1 ≤ e ∧ e ≤ 4 ∧
      k = sp lt pool (lines.getD n []) ^ e
  line : ∀ s ∈ lines, evS pool s = true ∧ sp lt pool s ≠ 1 ∧ sp lt pool s ^ 5 = 1
  fus : ∀ n < lines.length, ∃ i < wl.length, ∃ (s : List (ℕ × ℕ)) (e : ℕ), evS pool s = true ∧
    1 ≤ e ∧ e ≤ 4 ∧ sp lt pool s * pw lt pool 0 = pw lt pool 0 * sp lt pool s ∧
    sp lt pool s * sp lt pool (wl.getD i []) = sp lt pool (lines.getD n []) ^ e * sp lt pool s
  wit : ∀ i < wl.length, evS pool (wl.getD i []) = true ∧
    ∃ (gs : List (List (ℕ × ℕ))) (ex : ℕ),
      (∀ s ∈ gs, evS pool s = true ∧
        sp lt pool s * sp lt pool (wl.getD i []) = sp lt pool (wl.getD i []) * sp lt pool s) ∧
      (pw lt pool 0 * (gs.map fun s => sp lt pool s * pw lt pool 0 * spI lt pool s).prod) ^ ex ≠ 1 ∧
      ((pw lt pool 0 * (gs.map fun s => sp lt pool s * pw lt pool 0 * spI lt pool s).prod) ^ ex) ^ 5
        = 1

theorem nthD_cases (pool : List (List ℕ)) :
    ∀ j, nthD [] pool j = [] ∨ nthD [] pool j ∈ pool := by
  induction pool with
  | nil => intro j; exact Or.inl rfl
  | cons w pool ih =>
    intro j
    cases j with
    | zero => exact Or.inr List.mem_cons_self
    | succ j =>
      rcases ih j with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem nthD_codes {pool : List (List ℕ)} (h : ∀ w ∈ pool, ∀ c ∈ w, okC c = true) (j : ℕ) :
    ∀ c ∈ nthD [] pool j, okC c = true := by
  rcases nthD_cases pool j with e | e
  · rw [e]
    intro c hc
    exact absurd hc List.not_mem_nil
  · exact h _ e

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := Nat.blt_eq.mpr h

theorem blt_f {a b : ℕ} (h : b ≤ a) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · have := Nat.blt_eq.mp e
    omega

theorem beq_f {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem okC_iff (c : ℕ) : okC c = true ↔ c < 37 ∧ c ≠ 34 := by
  unfold okC
  rcases Nat.lt_or_ge c 37 with h | h
  · rw [blt_t h]
    by_cases h34 : c = 34
    · subst h34
      exact ⟨fun e => absurd e (by decide), fun e => absurd rfl e.2⟩
    · rw [beq_f h34]
      exact ⟨fun _ => ⟨h, h34⟩, fun _ => rfl⟩
  · rw [blt_f h]
    exact ⟨fun e => absurd e Bool.false_ne_true, fun e => absurd e.1 (by omega)⟩

theorem lw_invC {lt : ℕ → G}
    (ha : (∀ j < 17, lt j * lt (17 + j) = 1) ∧ lt 35 * (lt 35 * lt 35) = 1 ∧ lt 36 * lt 36 = 1)
    {c : ℕ} (hc : okC c = true) : lw lt (invC c) = (lt c)⁻¹ := by
  obtain ⟨h37, h34⟩ := (okC_iff c).1 hc
  unfold invC
  rcases Nat.lt_or_ge c 17 with h | h
  · rw [blt_t h]
    change lt (c + 17) * 1 = _
    rw [mul_one, Nat.add_comm]
    exact (eq_inv_of_mul_eq_one_right (ha.1 c h))
  rw [blt_f h]
  rcases Nat.lt_or_ge c 34 with h' | h'
  · rw [blt_t h']
    change lt (c - 17) * 1 = _
    rw [mul_one]
    have e := ha.1 (c - 17) (by omega)
    have e17 : 17 + (c - 17) = c := by omega
    rw [e17] at e
    exact eq_inv_of_mul_eq_one_left e
  rw [blt_f h']
  rcases (by omega : c = 35 ∨ c = 36) with rfl | rfl
  · change lt 35 * (lt 35 * 1) = _
    rw [mul_one]
    exact (eq_inv_of_mul_eq_one_right ha.2.1)
  · change lt 36 * 1 = _
    rw [mul_one]
    exact (eq_inv_of_mul_eq_one_left ha.2.2)

theorem lw_invW {lt : ℕ → G}
    (ha : (∀ j < 17, lt j * lt (17 + j) = 1) ∧ lt 35 * (lt 35 * lt 35) = 1 ∧ lt 36 * lt 36 = 1) :
    ∀ cs : List ℕ, (∀ c ∈ cs, okC c = true) → lw lt (invW cs) = (lw lt cs)⁻¹
  | [], _ => by simp [lw, invW]
  | c :: cs, hcs => by
    change ((List.append (invW cs) (invC c)).map lt).prod = _
    have e1 : lw lt (invW cs) = (lw lt cs)⁻¹ :=
      lw_invW ha cs fun c' h' => hcs c' (List.mem_cons_of_mem _ h')
    have e2 := lw_invC ha (hcs c List.mem_cons_self)
    unfold lw at e1 e2 ⊢
    rw [List.append_eq, List.map_append, List.prod_append, e1, e2, List.map_cons, List.prod_cons,
      mul_inv_rev]

theorem spI_eq {lt : ℕ → G} {pool : List (List ℕ)}
    (ha : (∀ j < 17, lt j * lt (17 + j) = 1) ∧ lt 35 * (lt 35 * lt 35) = 1 ∧ lt 36 * lt 36 = 1)
    (hcodes : ∀ w ∈ pool, ∀ c ∈ w, okC c = true) (s : List (ℕ × ℕ)) :
    spI lt pool s = (sp lt pool s)⁻¹ := by
  unfold spI sp
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map]
  congr 2
  refine List.map_congr_left fun p _ => ?_
  rw [Function.comp_apply, lw_invW ha _ (nthD_codes hcodes p.1), inv_pow]
  rfl

section Check

variable {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {Can : ℕ → Prop} {ev : ℕ → G}

private theorem andB_t {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

private theorem orB_t {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

private theorem sB_eq' (y : ℕ) (k : ℕ → Bool) : sB y k = k y := by cases y <;> rfl

private theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem mapS_eq' {α : Type} (f : α → ℕ) :
    ∀ (l : List α) (k : List ℕ → Bool), mapS f l k = k (l.map f)
  | [], _ => rfl
  | a :: l, k => by
    change sB (f a) (fun x => mapS f l fun xs => k (x :: xs)) = _
    rw [sB_eq', mapS_eq' f l]
    rfl

private theorem allL_t {α : Type} {p : α → Bool} :
    ∀ {l : List α}, allL p l = true → ∀ a ∈ l, p a = true
  | [], _, _, ha => absurd ha List.not_mem_nil
  | _ :: _, h, a, ha => by
    obtain ⟨h1, h2⟩ := andB_t h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h1
    · exact allL_t h2 a ha

private theorem anyL_t {α : Type} {p : α → Bool} :
    ∀ {l : List α}, anyL p l = true → ∃ a ∈ l, p a = true
  | [], h => absurd h Bool.false_ne_true
  | b :: _, h => by
    rcases orB_t h with h | h
    · exact ⟨b, List.mem_cons_self, h⟩
    · obtain ⟨a, ha, h⟩ := anyL_t h
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

private theorem memN_t {x : ℕ} {l : List ℕ} (h : memN x l = true) : x ∈ l := by
  obtain ⟨y, hy, e⟩ := anyL_t h
  rw [Nat.eq_of_beq_eq_true e]
  exact hy

private theorem memN_of_mem {x : ℕ} : ∀ {l : List ℕ}, x ∈ l → memN x l = true
  | [], h => absurd h List.not_mem_nil
  | y :: ys, h => by
    change orB (Nat.beq x y) (memN x ys) = true
    rcases List.mem_cons.1 h with rfl | h
    · rw [Nat.beq_refl]
      rfl
    · rw [memN_of_mem h]
      cases Nat.beq x y <;> rfl

private theorem nodupN_t : ∀ {l : List ℕ}, nodupN l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    obtain ⟨h1, h2⟩ := andB_t h
    refine List.nodup_cons.2 ⟨fun hx => ?_, nodupN_t h2⟩
    rw [memN_of_mem hx] at h1
    exact absurd h1 Bool.false_ne_true

private theorem allBelow_t {f : ℕ → Bool} : ∀ {n : ℕ}, allBelow n f = true → ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := andB_t h
    by_cases e : i = n
    · rw [e]
      exact h1
    · exact allBelow_t h2 i (by omega)

private theorem lenL_eq {α : Type} : ∀ l : List α, lenL l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenL_eq l)

private theorem nthD_eq' {α : Type} (d : α) : ∀ (l : List α) (i : ℕ), nthD d l i = l.getD i d
  | [], i => by
    rw [List.getD_nil]
    rfl
  | a :: l, 0 => by
    rw [List.getD_cons_zero]
    rfl
  | a :: l, i + 1 => by
    rw [List.getD_cons_succ]
    exact nthD_eq' d l i

private theorem nthD_map' {α β : Type} (f : α → β) (d : α) :
    ∀ (l : List α) (i : ℕ), nthD (f d) (l.map f) i = f (nthD d l i)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => nthD_map' f d l i

private theorem nthD_mem' {α : Type} {d : α} {l : List α} {i : ℕ} (hi : i < l.length) :
    nthD d l i ∈ l := by
  rw [nthD_eq', List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

private theorem mem_nthD' {α : Type} {d : α} {l : List α} {a : α} (ha : a ∈ l) :
    ∃ i < l.length, nthD d l i = a := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
  exact ⟨i, hi, by rw [nthD_eq', List.getD_eq_getElem _ _ hi]⟩

private theorem nthD_map_get {F : ℕ → ℕ} {gens : List ℕ} {l : ℕ} (hl : l < gens.length) :
    nthD 0 (gens.map F) l = F gens[l] := by
  rw [nthD_eq', List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hl), List.getElem_map]

private theorem okC_invC {c : ℕ} (hc : okC c = true) : ∀ d ∈ invC c, okC d = true := by
  obtain ⟨h37, h34⟩ := (okC_iff c).1 hc
  intro d hd
  rw [okC_iff]
  unfold invC at hd
  rcases Nat.lt_or_ge c 17 with h | h
  · rw [blt_t h] at hd
    have e : d = c + 17 := List.mem_singleton.1 hd
    omega
  rw [blt_f h] at hd
  rcases Nat.lt_or_ge c 34 with h' | h'
  · rw [blt_t h'] at hd
    have e : d = c - 17 := List.mem_singleton.1 hd
    omega
  rw [blt_f h'] at hd
  rcases (by omega : c = 35 ∨ c = 36) with rfl | rfl
  · change d ∈ [35, 35] at hd
    have e : d = 35 := by simpa using hd
    omega
  · change d ∈ [36] at hd
    have e : d = 36 := List.mem_singleton.1 hd
    omega

private theorem okC_invW :
    ∀ cs : List ℕ, (∀ c ∈ cs, okC c = true) → ∀ d ∈ invW cs, okC d = true
  | [], _, _, hd => absurd hd List.not_mem_nil
  | c :: cs, hcs, d, hd => by
    change d ∈ invW cs ++ invC c at hd
    rcases List.mem_append.1 hd with hd | hd
    · exact okC_invW cs (fun c' h' => hcs c' (List.mem_cons_of_mem _ h')) d hd
    · exact okC_invC (hcs c List.mem_cons_self) d hd

private theorem ev_eq (hM : Model mul ONE Can ev) {a b c d : ℕ} (ha : Can a) (hb : Can b)
    (hc : Can c) (hd : Can d) (h : mul a b = mul c d) : ev a * ev b = ev c * ev d := by
  rw [← (hM.mul ha hb).2, h, (hM.mul hc hd).2]

private theorem ev_one (hM : Model mul ONE Can ev) {a b : ℕ} (ha : Can a) (hb : Can b)
    (h : mul a b = ONE) : ev a * ev b = 1 := by
  rw [← (hM.mul ha hb).2, h, hM.one.2]

private theorem ne_one_of (hM : Model mul ONE Can ev) {a : ℕ} (ha : Can a)
    (h : notB (Nat.beq a ONE) = true) : ev a ≠ 1 := by
  intro e
  have e' : a = ONE := hM.inj ha hM.one.1 (by rw [e, hM.one.2])
  rw [e', Nat.beq_refl] at h
  exact absurd h Bool.false_ne_true

private theorem wordGo_cons (R : ℕ → ℕ) (c : ℕ) (cs : List ℕ) (acc : ℕ) :
    wordGo mul R (c :: cs) acc = wordGo mul R cs (mul acc (R c)) :=
  strictN_eq' _ _

private theorem wordGo_ev (hM : Model mul ONE Can ev) {L : ℕ → ℕ}
    (hL : ∀ c, okC c = true → Can (L c)) :
    ∀ cs : List ℕ, (∀ c ∈ cs, okC c = true) → ∀ acc, Can acc →
      Can (wordGo mul L cs acc) ∧ ev (wordGo mul L cs acc) = ev acc * lw (fun c => ev (L c)) cs
  | [], _, _, h => ⟨h, by unfold lw; rw [List.map_nil, List.prod_nil, mul_one]; rfl⟩
  | c :: cs, hcs, acc, h => by
    obtain ⟨h1, h2⟩ := hM.mul h (hL c (hcs c List.mem_cons_self))
    obtain ⟨h3, h4⟩ := wordGo_ev hM hL cs (fun c' h' => hcs c' (List.mem_cons_of_mem _ h')) _ h1
    rw [wordGo_cons]
    refine ⟨h3, ?_⟩
    rw [h4, h2]
    unfold lw
    rw [List.map_cons, List.prod_cons, mul_assoc]

private theorem wordP_ev (hM : Model mul ONE Can ev) {L : ℕ → ℕ}
    (hL : ∀ c, okC c = true → Can (L c)) (cs : List ℕ) (hcs : ∀ c ∈ cs, okC c = true) :
    Can (wordP mul ONE L cs) ∧ ev (wordP mul ONE L cs) = lw (fun c => ev (L c)) cs := by
  obtain ⟨h1, h2⟩ := wordGo_ev hM hL cs hcs ONE hM.one.1
  refine ⟨h1, ?_⟩
  have e : wordP mul ONE L cs = wordGo mul L cs ONE := rfl
  rw [e, h2, hM.one.2, one_mul]

private theorem powM_ss (X e : ℕ) : powM mul ONE X (e + 2) = mul (powM mul ONE X (e + 1)) X :=
  rfl

private theorem powM_ev (hM : Model mul ONE Can ev) {X : ℕ} {x : G} (hX : Can X) (hx : ev X = x) :
    ∀ e, Can (powM mul ONE X e) ∧ ev (powM mul ONE X e) = x ^ e
  | 0 => ⟨hM.one.1, by rw [pow_zero]; exact hM.one.2⟩
  | 1 => ⟨hX, by rw [pow_one]; exact hx⟩
  | e + 2 => by
    obtain ⟨h1, h2⟩ := powM_ev hM hX hx (e + 1)
    obtain ⟨h3, h4⟩ := hM.mul h1 hX
    rw [powM_ss]
    exact ⟨h3, by rw [h4, h2, hx, ← pow_succ]⟩

private theorem sp_nil (lt : ℕ → G) (pool : List (List ℕ)) : sp lt pool [] = 1 := by
  unfold sp
  rw [List.map_nil, List.prod_nil]

private theorem sp_cons (lt : ℕ → G) (pool : List (List ℕ)) (p : ℕ × ℕ) (s : List (ℕ × ℕ)) :
    sp lt pool (p :: s) = pw lt pool p.1 ^ p.2 * sp lt pool s := by
  unfold sp
  rw [List.map_cons, List.prod_cons]

private theorem spI_nil (lt : ℕ → G) (pool : List (List ℕ)) : spI lt pool [] = 1 := by
  unfold spI
  rw [List.reverse_nil, List.map_nil, List.prod_nil]

private theorem spI_cons (lt : ℕ → G) (pool : List (List ℕ)) (p : ℕ × ℕ) (s : List (ℕ × ℕ)) :
    spI lt pool (p :: s) = spI lt pool s * lw lt (invW (nthD [] pool p.1)) ^ p.2 := by
  unfold spI
  rw [List.reverse_cons, List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]

private theorem specM_ev (hM : Model mul ONE Can ev) {lt : ℕ → G} {pool : List (List ℕ)}
    {F : ℕ → ℕ} (hF : ∀ j, Can (F j) ∧ ev (F j) = pw lt pool j) :
    ∀ s : List (ℕ × ℕ), Can (specM mul ONE F s) ∧ ev (specM mul ONE F s) = sp lt pool s
  | [] => ⟨hM.one.1, by rw [sp_nil]; exact hM.one.2⟩
  | [p] => by
    obtain ⟨c, e⟩ := powM_ev hM (hF p.1).1 (hF p.1).2 p.2
    exact ⟨c, by rw [sp_cons, sp_nil, mul_one]; exact e⟩
  | p :: q :: s => by
    obtain ⟨c, e⟩ := powM_ev hM (hF p.1).1 (hF p.1).2 p.2
    obtain ⟨c', e'⟩ := specM_ev hM hF (q :: s)
    obtain ⟨c'', e''⟩ := hM.mul c c'
    exact ⟨c'', by rw [sp_cons, ← e', ← e]; exact e''⟩

private theorem specI_ev (hM : Model mul ONE Can ev) {lt : ℕ → G} {pool : List (List ℕ)}
    {Gf : ℕ → ℕ} (hG : ∀ j, Can (Gf j) ∧ ev (Gf j) = lw lt (invW (nthD [] pool j))) :
    ∀ s : List (ℕ × ℕ), Can (specI mul ONE Gf s) ∧ ev (specI mul ONE Gf s) = spI lt pool s
  | [] => ⟨hM.one.1, by rw [spI_nil]; exact hM.one.2⟩
  | [p] => by
    obtain ⟨c, e⟩ := powM_ev hM (hG p.1).1 (hG p.1).2 p.2
    exact ⟨c, by rw [spI_cons, spI_nil, one_mul]; exact e⟩
  | p :: q :: s => by
    obtain ⟨c, e⟩ := powM_ev hM (hG p.1).1 (hG p.1).2 p.2
    obtain ⟨c', e'⟩ := specI_ev hM hG (q :: s)
    obtain ⟨c'', e''⟩ := hM.mul c' c
    exact ⟨c'', by rw [spI_cons, ← e', ← e]; exact e''⟩

private theorem WM_ev (hM : Model mul ONE Can ev) {lt : ℕ → G} {pool : List (List ℕ)}
    {F : ℕ → ℕ} (hF : ∀ j, Can (F j) ∧ ev (F j) = pw lt pool j) (wl : List (List (ℕ × ℕ)))
    (i : ℕ) : Can (nthD ONE (wl.map (specM mul ONE F)) i) ∧
      ev (nthD ONE (wl.map (specM mul ONE F)) i) = sp lt pool (wl.getD i []) := by
  have e : nthD ONE (wl.map (specM mul ONE F)) i = specM mul ONE F (nthD [] wl i) :=
    nthD_map' (specM mul ONE F) [] wl i
  rw [e, ← nthD_eq']
  exact specM_ev hM hF _

private def Proc (mul : ℕ → ℕ → ℕ) (GM : List ℕ) (ng : ℕ) (ks : List ℕ) (n h l : ℕ) : Prop :=
  ∀ h' < n, ∀ l' < ng, (h' < h ∨ (h' = h ∧ l' < l)) →
    mul (nthD 0 GM l') (nthD 0 ks (n - 1 - h')) ∈ ks

private theorem proc_init {GM : List ℕ} {ng : ℕ} : Proc mul GM ng [ONE] 1 0 0 := by
  intro h' _ l' _ hlt
  rcases hlt with h | ⟨_, h⟩
  · exact absurd h (Nat.not_lt_zero _)
  · exact absurd h (Nat.not_lt_zero _)

private theorem proc_step {GM : List ℕ} {ng : ℕ} {ks ks' : List ℕ} {n n' h l h2 l2 : ℕ}
    (hp : Proc mul GM ng ks n h l) (hhn : h < n) (hsub : ∀ a ∈ ks, a ∈ ks')
    (hidx : ∀ h' < n, nthD 0 ks' (n' - 1 - h') = nthD 0 ks (n - 1 - h'))
    (hx : mul (nthD 0 GM l) (nthD 0 ks (n - 1 - h)) ∈ ks')
    (hnext : (l + 1 = ng ∧ h2 = h + 1 ∧ l2 = 0) ∨ (l + 1 ≠ ng ∧ h2 = h ∧ l2 = l + 1)) :
    Proc mul GM ng ks' n' h2 l2 := by
  intro h' _ l' hl' hlt
  have h'n : h' < n := by omega
  rw [hidx h' h'n]
  by_cases e1 : h' = h
  · by_cases e2 : l' = l
    · rw [e1, e2]
      exact hx
    · exact hsub _ (hp h' h'n l' hl' (by omega))
  · exact hsub _ (hp h' h'n l' hl' (by omega))

private theorem proc_final {GM : List ℕ} {ng : ℕ} {ks : List ℕ} {n : ℕ} (hlen : ks.length = n)
    (hp : Proc mul GM ng ks n n 0) : ∀ a ∈ ks, ∀ l' < ng, mul (nthD 0 GM l') a ∈ ks := by
  intro a ha l' hl'
  obtain ⟨j, hj, rfl⟩ := mem_nthD' (d := 0) ha
  have hm := hp (n - 1 - j) (by omega) l' hl' (Or.inl (by omega))
  rwa [show n - 1 - (n - 1 - j) = j by omega] at hm

private theorem treeGo_sound {GM : List ℕ} {ng : ℕ} (Q : ℕ → Prop)
    (hQ : ∀ a l, Q a → l < ng → Q (mul (nthD 0 GM l) a)) :
    ∀ (tr ks : List ℕ) (n h l : ℕ) (k : List ℕ → ℕ → Bool),
      treeGo mul GM ng tr ks n h l k = true → ks.length = n → (∀ a ∈ ks, Q a) →
      Proc mul GM ng ks n h l →
      ∃ ks' : List ℕ, k ks' ks'.length = true ∧ (∀ a ∈ ks', Q a) ∧ (∀ a ∈ ks, a ∈ ks') ∧
        ∀ a ∈ ks', ∀ l' < ng, mul (nthD 0 GM l') a ∈ ks'
  | [], ks, n, h, l, k, hc, hlen, hQs, hp => by
    obtain ⟨h1, hc⟩ := andB_t hc
    obtain ⟨h2, hc⟩ := andB_t hc
    have e1 : h = n := Nat.eq_of_beq_eq_true h1
    have e2 : l = 0 := Nat.eq_of_beq_eq_true h2
    rw [e1, e2] at hp
    refine ⟨ks, by rw [hlen]; exact hc, hQs, fun a ha => ha, proc_final hlen hp⟩
  | t :: tr, ks, n, h, l, k, hc, hlen, hQs, hp => by
    obtain ⟨h1, hc⟩ := andB_t hc
    obtain ⟨h2, hc⟩ := andB_t hc
    have hhn : h < n := Nat.blt_eq.mp h1
    have hln : l < ng := Nat.blt_eq.mp h2
    rw [sB_eq'] at hc
    have hkm : nthD 0 ks (n - 1 - h) ∈ ks := nthD_mem' (by omega)
    have hQx : Q (mul (nthD 0 GM l) (nthD 0 ks (n - 1 - h))) := hQ _ _ (hQs _ hkm) hln
    have hnx : ∀ (ks' : List ℕ) (n' : ℕ),
        Bool.rec (motive := fun _ => Bool) (treeGo mul GM ng tr ks' n' h (Nat.succ l) k)
          (treeGo mul GM ng tr ks' n' (Nat.succ h) 0 k) (Nat.beq (Nat.succ l) ng) = true →
        ks'.length = n' → (∀ a ∈ ks', Q a) → (∀ a ∈ ks, a ∈ ks') →
        (∀ h' < n, nthD 0 ks' (n' - 1 - h') = nthD 0 ks (n - 1 - h')) →
        mul (nthD 0 GM l) (nthD 0 ks (n - 1 - h)) ∈ ks' →
        ∃ ks'' : List ℕ, k ks'' ks''.length = true ∧ (∀ a ∈ ks'', Q a) ∧
          (∀ a ∈ ks, a ∈ ks'') ∧ ∀ a ∈ ks'', ∀ l' < ng, mul (nthD 0 GM l') a ∈ ks'' := by
      intro ks' n' hb hlen' hQs' hsub hidx hx
      cases e : Nat.beq (Nat.succ l) ng
      · rw [e] at hb
        obtain ⟨ks'', r1, r2, r3, r4⟩ := treeGo_sound Q hQ tr ks' n' h (l + 1) k hb hlen' hQs'
          (proc_step hp hhn hsub hidx hx (Or.inr ⟨Nat.ne_of_beq_eq_false e, rfl, rfl⟩))
        exact ⟨ks'', r1, r2, fun a ha => r3 a (hsub a ha), r4⟩
      · rw [e] at hb
        obtain ⟨ks'', r1, r2, r3, r4⟩ := treeGo_sound Q hQ tr ks' n' (h + 1) 0 k hb hlen' hQs'
          (proc_step hp hhn hsub hidx hx (Or.inl ⟨Nat.eq_of_beq_eq_true e, rfl, rfl⟩))
        exact ⟨ks'', r1, r2, fun a ha => r3 a (hsub a ha), r4⟩
    rcases t with _ | t
    · refine hnx (mul (nthD 0 GM l) (nthD 0 ks (n - 1 - h)) :: ks) (n + 1) hc
        (by rw [List.length_cons, hlen]) ?_ (fun a ha => List.mem_cons_of_mem _ ha) ?_
        List.mem_cons_self
      · intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hQx
        · exact hQs a ha
      · intro h' hh'
        rw [show n + 1 - 1 - h' = (n - 1 - h') + 1 by omega]
        rfl
    · obtain ⟨h3, hc⟩ := andB_t hc
      obtain ⟨h4, hc⟩ := andB_t hc
      have ht : t + 1 ≤ n := Nat.le_of_ble_eq_true h3
      have hxe : mul (nthD 0 GM l) (nthD 0 ks (n - 1 - h)) = nthD 0 ks (n - (t + 1)) :=
        Nat.eq_of_beq_eq_true h4
      exact hnx ks n hc hlen hQs (fun a ha => ha) (fun _ _ => rfl)
        (by rw [hxe]; exact nthD_mem' (by omega))

private def LR (Can : ℕ → Prop) (ev : ℕ → G) (lt : ℕ → G) (pool : List (List ℕ))
    (s : List (ℕ × ℕ)) (p : List ℕ) : Prop :=
  evS pool s = true ∧ sp lt pool s ≠ 1 ∧ sp lt pool s ^ 5 = 1 ∧
    ∃ a1 a2 a3 a4 : ℕ, p = [a1, a2, a3, a4] ∧ (Can a1 ∧ ev a1 = sp lt pool s) ∧
      (Can a2 ∧ ev a2 = sp lt pool s ^ 2) ∧ (Can a3 ∧ ev a3 = sp lt pool s ^ 3) ∧
      (Can a4 ∧ ev a4 = sp lt pool s ^ 4)

private theorem linesGo_sound (hM : Model mul ONE Can ev) {lt : ℕ → G} {pool : List (List ℕ)}
    {F : ℕ → ℕ} (hF : ∀ j, Can (F j) ∧ ev (F j) = pw lt pool j) :
    ∀ (lines : List (List (ℕ × ℕ))) (k : List (List ℕ) → Bool),
      linesGo mul ONE pool F lines k = true →
      ∃ pks : List (List ℕ), pks.length = lines.length ∧
        (∀ n < lines.length, LR Can ev lt pool (lines.getD n []) (pks.getD n [])) ∧ k pks = true
  | [], _, hc => ⟨[], rfl, fun n hn => absurd hn (Nat.not_lt_zero n), hc⟩
  | s :: lines, k, hc => by
    obtain ⟨he, hc⟩ := andB_t hc
    rw [sB_eq'] at hc
    beta_reduce at hc
    rw [sB_eq'] at hc
    beta_reduce at hc
    rw [sB_eq'] at hc
    beta_reduce at hc
    rw [sB_eq'] at hc
    beta_reduce at hc
    obtain ⟨h5, hc⟩ := andB_t hc
    obtain ⟨h1, hc⟩ := andB_t hc
    obtain ⟨pks, hlen, hLR, hk⟩ := linesGo_sound hM hF lines _ hc
    obtain ⟨c1, e1⟩ := specM_ev hM hF s
    obtain ⟨c2, e2⟩ := hM.mul c1 c1
    obtain ⟨c3, e3⟩ := hM.mul c2 c1
    obtain ⟨c4, e4⟩ := hM.mul c3 c1
    have f2 : ev (mul (specM mul ONE F s) (specM mul ONE F s)) = sp lt pool s ^ 2 := by
      rw [e2, e1, pow_two]
    have f3 : ev (mul (mul (specM mul ONE F s) (specM mul ONE F s)) (specM mul ONE F s)) =
        sp lt pool s ^ 3 := by
      rw [e3, f2, e1, ← pow_succ]
    have f4 : ev (mul (mul (mul (specM mul ONE F s) (specM mul ONE F s)) (specM mul ONE F s))
        (specM mul ONE F s)) = sp lt pool s ^ 4 := by
      rw [e4, f3, e1, ← pow_succ]
    refine ⟨_ :: pks, by rw [List.length_cons, hlen, List.length_cons], ?_, hk⟩
    intro n hn
    cases n with
    | zero =>
      rw [List.getD_cons_zero, List.getD_cons_zero]
      refine ⟨he, ?_, ?_, _, _, _, _, rfl, ⟨c1, e1⟩, ⟨c2, f2⟩, ⟨c3, f3⟩, ⟨c4, f4⟩⟩
      · rw [← e1]
        exact ne_one_of hM c1 h1
      · have e := ev_one hM c4 c1 (Nat.eq_of_beq_eq_true h5)
        rw [f4, e1, ← pow_succ] at e
        exact e
    | succ n =>
      rw [List.getD_cons_succ, List.getD_cons_succ]
      exact hLR n (by rw [List.length_cons] at hn; omega)

private theorem quad {lt : ℕ → G} {pool : List (List ℕ)} {s : List (ℕ × ℕ)} {a1 a2 a3 a4 : ℕ}
    (q1 : Can a1 ∧ ev a1 = sp lt pool s) (q2 : Can a2 ∧ ev a2 = sp lt pool s ^ 2)
    (q3 : Can a3 ∧ ev a3 = sp lt pool s ^ 3) (q4 : Can a4 ∧ ev a4 = sp lt pool s ^ 4) :
    ∀ e, 1 ≤ e → e ≤ 4 → Can (nthD 0 [a1, a2, a3, a4] (e - 1)) ∧
      ev (nthD 0 [a1, a2, a3, a4] (e - 1)) = sp lt pool s ^ e := by
  intro e h1 h4
  interval_cases e
  · exact ⟨q1.1, by rw [pow_one]; exact q1.2⟩
  · exact q2
  · exact q3
  · exact q4

private theorem fuseOK_sound {pool : List (List ℕ)} {F : ℕ → ℕ} {nw : ℕ} {WM : List ℕ} {Y : ℕ} :
    ∀ (fuse : List (ℕ × (List (ℕ × ℕ) × ℕ))) (ps : List (List ℕ)),
      fuseOK mul ONE pool F nw WM Y fuse ps = true →
      ∀ n < ps.length, ∃ f : ℕ × (List (ℕ × ℕ) × ℕ), f.1 < nw ∧ 1 ≤ f.2.2 ∧ f.2.2 ≤ 4 ∧
        evS pool f.2.1 = true ∧
        mul (specM mul ONE F f.2.1) Y = mul Y (specM mul ONE F f.2.1) ∧
        mul (specM mul ONE F f.2.1) (nthD ONE WM f.1) =
          mul (nthD 0 (ps.getD n []) (f.2.2 - 1)) (specM mul ONE F f.2.1)
  | [], [], _, n, hn => absurd hn (Nat.not_lt_zero n)
  | [], _ :: _, hc, _, _ => absurd hc Bool.false_ne_true
  | _ :: _, [], hc, _, _ => absurd hc Bool.false_ne_true
  | f :: fuse, p :: ps, hc, n, hn => by
    obtain ⟨h1, hc⟩ := andB_t hc
    obtain ⟨h2, hc⟩ := andB_t hc
    obtain ⟨h3, hc⟩ := andB_t hc
    obtain ⟨h4, hc⟩ := andB_t hc
    rw [sB_eq'] at hc
    obtain ⟨h5, hc⟩ := andB_t hc
    obtain ⟨h6, hc⟩ := andB_t hc
    cases n with
    | zero =>
      rw [List.getD_cons_zero]
      exact ⟨f, Nat.blt_eq.mp h1, Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3, h4,
        Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6⟩
    | succ n =>
      rw [List.getD_cons_succ]
      exact fuseOK_sound fuse ps hc n (by rw [List.length_cons] at hn; omega)

private theorem conjGo_sound (hM : Model mul ONE Can ev) {lt : ℕ → G} {pool : List (List ℕ)}
    {F Gf : ℕ → ℕ} {Y W : ℕ} {y w : G} (hF : ∀ j, Can (F j) ∧ ev (F j) = pw lt pool j)
    (hG : ∀ j, Can (Gf j) ∧ ev (Gf j) = lw lt (invW (nthD [] pool j)))
    (hY : Can Y ∧ ev Y = y) (hW : Can W ∧ ev W = w) :
    ∀ (gs : List (List (ℕ × ℕ))) (acc : ℕ) (a : G) (k : ℕ → Bool), Can acc → ev acc = a →
      conjGo mul ONE pool F Gf Y W gs acc k = true →
      (∀ s ∈ gs, evS pool s = true ∧ sp lt pool s * w = w * sp lt pool s) ∧
      ∃ P, Can P ∧ ev P = a * (gs.map fun s => sp lt pool s * y * spI lt pool s).prod ∧
        k P = true
  | [], acc, _, _, hc, he, h =>
    ⟨fun _ hs => absurd hs List.not_mem_nil, acc, hc,
      by rw [List.map_nil, List.prod_nil, mul_one]; exact he, h⟩
  | s :: gs, acc, a, k, hc, he, h => by
    obtain ⟨hev, h⟩ := andB_t h
    rw [sB_eq'] at h
    obtain ⟨hcm, h⟩ := andB_t h
    rw [sB_eq'] at h
    obtain ⟨cg, eg⟩ := specM_ev hM hF s
    obtain ⟨ci, ei⟩ := specI_ev hM hG s
    obtain ⟨c1, e1⟩ := hM.mul cg hY.1
    obtain ⟨c2, e2⟩ := hM.mul c1 ci
    obtain ⟨c3, e3⟩ := hM.mul hc c2
    obtain ⟨hgs, P, cP, eP, hk⟩ := conjGo_sound hM hF hG hY hW gs _
      (a * (sp lt pool s * y * spI lt pool s)) k c3 (by rw [e3, e2, e1, eg, ei, he, hY.2]) h
    refine ⟨?_, P, cP, by rw [eP, List.map_cons, List.prod_cons, mul_assoc], hk⟩
    intro s' hs'
    rcases List.mem_cons.1 hs' with rfl | hs'
    · refine ⟨hev, ?_⟩
      have e := ev_eq hM cg hW.1 hW.1 cg (Nat.eq_of_beq_eq_true hcm)
      rwa [eg, hW.2] at e
    · exact hgs s' hs'

private theorem witsOK_sound (hM : Model mul ONE Can ev) {lt : ℕ → G} {pool : List (List ℕ)}
    {F Gf : ℕ → ℕ} (hF : ∀ j, Can (F j) ∧ ev (F j) = pw lt pool j)
    (hG : ∀ j, Can (Gf j) ∧ ev (Gf j) = lw lt (invW (nthD [] pool j))) :
    ∀ (wits : List (List (List (ℕ × ℕ)) × ℕ)) (wl : List (List (ℕ × ℕ))),
      witsOK mul ONE pool F Gf (F 0) wits wl (wl.map (specM mul ONE F)) = true →
      ∀ i < wl.length, evS pool (wl.getD i []) = true ∧
        ∃ (gs : List (List (ℕ × ℕ))) (ex : ℕ),
          (∀ s ∈ gs, evS pool s = true ∧
            sp lt pool s * sp lt pool (wl.getD i []) = sp lt pool (wl.getD i []) * sp lt pool s) ∧
          (pw lt pool 0 * (gs.map fun s => sp lt pool s * pw lt pool 0 * spI lt pool s).prod) ^ ex
            ≠ 1 ∧
          ((pw lt pool 0 * (gs.map fun s => sp lt pool s * pw lt pool 0 * spI lt pool s).prod) ^
            ex) ^ 5 = 1
  | [], [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | [], _ :: _, hc, _, _ => absurd hc Bool.false_ne_true
  | _ :: _, [], hc, _, _ => absurd hc Bool.false_ne_true
  | w :: wits, s :: wl, hc, i, hi => by
    obtain ⟨he, hc⟩ := andB_t hc
    have hW := specM_ev hM hF s
    obtain ⟨hgs, P, cP, eP, hk⟩ :=
      conjGo_sound hM hF hG (hF 0) hW w.1 (F 0) _ _ (hF 0).1 (hF 0).2 hc
    rw [sB_eq'] at hk
    obtain ⟨hq1, hk⟩ := andB_t hk
    obtain ⟨hq5, hk⟩ := andB_t hk
    cases i with
    | zero =>
      rw [List.getD_cons_zero]
      obtain ⟨cq, eq⟩ := powM_ev hM cP eP w.2
      obtain ⟨-, e5⟩ := powM_ev hM cq eq 5
      refine ⟨he, w.1, w.2, hgs, ?_, ?_⟩
      · rw [← eq]
        exact ne_one_of hM cq hq1
      · have e := congrArg ev (Nat.eq_of_beq_eq_true hq5)
        rw [e5, hM.one.2] at e
        exact e
    | succ i =>
      rw [List.getD_cons_succ]
      exact witsOK_sound hM hF hG wits wl hk i (by rw [List.length_cons] at hi; omega)

theorem chk_raw {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {Can : ℕ → Prop} {ev : ℕ → G}
    (hM : Model mul ONE Can ev) {L : ℕ → ℕ} (hL : ∀ c, okC c = true → Can (L c))
    {pool : List (List ℕ)} {gens : List ℕ} {nQ : ℕ} {lines : List (List (ℕ × ℕ))}
    {fuse : List (ℕ × (List (ℕ × ℕ) × ℕ))} {wl : List (List (ℕ × ℕ))}
    {wits : List (List (List (ℕ × ℕ)) × ℕ)} {tr : List ℕ}
    (h : chk mul ONE L pool gens nQ lines fuse wl wits tr = true) :
    Raw (fun c => ev (L c)) pool gens nQ lines wl := by
  unfold chk at h
  obtain ⟨hal, h⟩ := andB_t h
  obtain ⟨hcod, h⟩ := andB_t h
  simp only [mapS_eq', sB_eq'] at h
  set F := nthD ONE (List.map (wordP mul ONE L) pool) with hFd
  have hcodes : ∀ w ∈ pool, ∀ c ∈ w, okC c = true := fun w hw => allL_t (allL_t hcod w hw)
  have hF : ∀ j, Can (F j) ∧ ev (F j) = pw (fun c => ev (L c)) pool j := by
    intro j
    have e : F j = wordP mul ONE L (nthD [] pool j) := nthD_map' (wordP mul ONE L) [] pool j
    rw [e]
    exact wordP_ev hM hL _ (nthD_codes hcodes j)
  have hG : ∀ j, Can (wordP mul ONE L (invW (nthD [] pool j))) ∧
      ev (wordP mul ONE L (invW (nthD [] pool j))) =
        lw (fun c => ev (L c)) (invW (nthD [] pool j)) :=
    fun j => wordP_ev hM hL _ (okC_invW _ (nthD_codes hcodes j))
  obtain ⟨ha1, ha2⟩ := andB_t hal
  obtain ⟨ha2, ha3⟩ := andB_t ha2
  have hLc : ∀ c, c < 37 → c ≠ 34 → Can (L c) := fun c h1 h2 => hL c ((okC_iff c).2 ⟨h1, h2⟩)
  have alph : (∀ j < 17, ev (L j) * ev (L (17 + j)) = 1) ∧
      ev (L 35) * (ev (L 35) * ev (L 35)) = 1 ∧ ev (L 36) * ev (L 36) = 1 := by
    refine ⟨fun j hj => ?_, ?_, ?_⟩
    · exact ev_one hM (hLc j (by omega) (by omega)) (hLc (17 + j) (by omega) (by omega))
        (Nat.eq_of_beq_eq_true (allBelow_t ha1 j hj))
    · have c35 := hLc 35 (by omega) (by omega)
      obtain ⟨c, e⟩ := hM.mul c35 c35
      have e' := ev_one hM c35 c (Nat.eq_of_beq_eq_true ha2)
      rwa [e] at e'
    · exact ev_one hM (hLc 36 (by omega) (by omega)) (hLc 36 (by omega) (by omega))
        (Nat.eq_of_beq_eq_true ha3)
  obtain ⟨hgen, h⟩ := andB_t h
  set S : Set G := {x : G | ∃ j ∈ gens, x = pw (fun c => ev (L c)) pool j} with hS
  have hQ : ∀ a l, (Can a ∧ ev a ∈ Submonoid.closure S) → l < lenL gens →
      (Can (mul (nthD 0 (gens.map F) l) a) ∧
        ev (mul (nthD 0 (gens.map F) l) a) ∈ Submonoid.closure S) := by
    intro a l ha hl
    rw [lenL_eq] at hl
    rw [nthD_map_get hl]
    obtain ⟨c, e⟩ := hM.mul (hF gens[l]).1 ha.1
    refine ⟨c, ?_⟩
    rw [e, (hF gens[l]).2]
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨gens[l], List.getElem_mem hl, rfl⟩) ha.2
  obtain ⟨ks, hk, hQs, hsub, hcl⟩ :=
    treeGo_sound (fun a => Can a ∧ ev a ∈ Submonoid.closure S) hQ tr [ONE] 1 0 0 _ h rfl
      (fun a ha => by
        rw [List.mem_singleton.1 ha]
        exact ⟨hM.one.1, by rw [hM.one.2]; exact Submonoid.one_mem _⟩)
      proc_init
  obtain ⟨hn, hk⟩ := andB_t hk
  obtain ⟨hnd, hk⟩ := andB_t hk
  obtain ⟨pks, hplen, hLR, hk⟩ := linesGo_sound hM hF lines _ hk
  obtain ⟨hcov, hk⟩ := andB_t hk
  obtain ⟨hfu, hwi⟩ := andB_t hk
  refine ⟨alph, hcodes, ?_, ?_, ?_, ?_, witsOK_sound hM hF hG wits wl hwi⟩
  · intro j hj
    obtain ⟨h1, h2⟩ := andB_t (allL_t hgen j hj)
    refine ⟨h1, ?_⟩
    have e := ev_eq hM (hF j).1 (hF 0).1 (hF 0).1 (hF j).1 (Nat.eq_of_beq_eq_true h2)
    rwa [(hF j).2, (hF 0).2] at e
  · refine ⟨ks.map ev, by rw [List.length_map]; exact Nat.eq_of_beq_eq_true hn, ?_, ?_, ?_, ?_, ?_⟩
    · exact List.Nodup.map_on (fun x hx y hy e => hM.inj (hQs x hx).1 (hQs y hy).1 e)
        (nodupN_t hnd)
    · exact List.mem_map.2 ⟨ONE, hsub ONE List.mem_cons_self, hM.one.2⟩
    · intro g hg j hj
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
      obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hj
      have hm := hcl a ha l (by rw [lenL_eq]; exact hl)
      rw [nthD_map_get hl] at hm
      obtain ⟨-, e⟩ := hM.mul (hF gens[l]).1 (hQs a ha).1
      exact List.mem_map.2 ⟨_, hm, by rw [e, (hF gens[l]).2]⟩
    · intro g hg
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
      exact (hQs a ha).2
    · intro g hg
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
      rcases orB_t (allL_t hcov a ha) with h1 | h1
      · left
        rw [Nat.eq_of_beq_eq_true h1, hM.one.2]
      · right
        obtain ⟨p, hp, hap⟩ := anyL_t h1
        have hap := memN_t hap
        obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hp
        have hn' : n < lines.length := by rw [← hplen]; exact hn
        obtain ⟨-, -, -, a1, a2, a3, a4, hpe, q1, q2, q3, q4⟩ := hLR n hn'
        rw [List.getD_eq_getElem _ _ hn] at hpe
        rw [hpe] at hap
        refine ⟨n, hn', ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hap
        rcases hap with e | e | e | e
        · exact ⟨1, le_refl 1, by norm_num, by rw [e, q1.2, pow_one]⟩
        · exact ⟨2, by norm_num, by norm_num, by rw [e, q2.2]⟩
        · exact ⟨3, by norm_num, by norm_num, by rw [e, q3.2]⟩
        · exact ⟨4, by norm_num, le_refl 4, by rw [e, q4.2]⟩
  · intro s hs
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hs
    obtain ⟨h1, h2, h3, -⟩ := hLR n hn
    rw [List.getD_eq_getElem _ _ hn] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · intro n hn
    have hn' : n < pks.length := by rw [hplen]; exact hn
    obtain ⟨f, hf1, hf2, hf3, hf4, hf5, hf6⟩ := fuseOK_sound _ _ hfu n hn'
    obtain ⟨-, -, -, a1, a2, a3, a4, hpe, q1, q2, q3, q4⟩ := hLR n hn
    obtain ⟨cg, eg⟩ := specM_ev hM hF f.2.1
    have hWi := WM_ev hM hF wl f.1
    rw [lenL_eq] at hf1
    refine ⟨f.1, hf1, f.2.1, f.2.2, hf4, hf2, hf3, ?_, ?_⟩
    · have e := ev_eq hM cg (hF 0).1 (hF 0).1 cg hf5
      rwa [eg, (hF 0).2] at e
    · have hp : Can (nthD 0 (pks.getD n []) (f.2.2 - 1)) ∧
          ev (nthD 0 (pks.getD n []) (f.2.2 - 1)) =
            sp (fun c => ev (L c)) pool (lines.getD n []) ^ f.2.2 := by
        rw [hpe]
        exact quad q1 q2 q3 q4 f.2.2 hf2 hf3
      have e := ev_eq hM cg hWi.1 hp.1 cg hf6
      rwa [eg, hWi.2, hp.2] at e

end Check

section Parity

variable {lt : ℕ → G} (K : Subgroup G) [K.Normal]

theorem mk_lw (hK : ∀ c, okC c = true → c < 36 → lt c ∈ K) :
    ∀ cs : List ℕ, (∀ c ∈ cs, okC c = true) →
      (QuotientGroup.mk' K) (lw lt cs) = (QuotientGroup.mk' K (lt 36)) ^ cntC cs
  | [], _ => by simp [lw, cntC]
  | c :: cs, hcs => by
    have ih := mk_lw hK cs fun c' h' => hcs c' (List.mem_cons_of_mem _ h')
    have hc := hcs c List.mem_cons_self
    unfold lw at ih ⊢
    rw [List.map_cons, List.prod_cons, map_mul, ih]
    change _ = _ ^ Nat.add (cntC cs) (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.blt 35 c))
    obtain ⟨h37, -⟩ := (okC_iff c).1 hc
    rcases Nat.lt_or_ge c 36 with h | h
    · have e : QuotientGroup.mk' K (lt c) = 1 := (QuotientGroup.eq_one_iff (lt c)).2 (hK c hc h)
      rw [blt_f (by omega : c ≤ 35), e, one_mul]
      rfl
    · obtain rfl : c = 36 := by omega
      change _ = _ ^ (cntC cs + 1)
      rw [pow_succ']

theorem pow_even_eq_one {u : G ⧸ K} (hu : u * u = 1) {n : ℕ} (hn : n % 2 = 0) : u ^ n = 1 := by
  have e : n = 2 * (n / 2) := by omega
  rw [e, pow_mul, sq, hu, one_pow]

theorem lw_mem (hK : ∀ c, okC c = true → c < 36 → lt c ∈ K) (h36 : lt 36 * lt 36 = 1)
    {cs : List ℕ} (hcs : ∀ c ∈ cs, okC c = true) (he : evC cs = true) : lw lt cs ∈ K := by
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, mk_lw K hK cs hcs]
  refine pow_even_eq_one K (by rw [← map_mul, h36, map_one]) ?_
  exact Nat.eq_of_beq_eq_true he

theorem mk_sp (hK : ∀ c, okC c = true → c < 36 → lt c ∈ K) {pool : List (List ℕ)}
    (hcodes : ∀ w ∈ pool, ∀ c ∈ w, okC c = true) :
    ∀ s : List (ℕ × ℕ), (QuotientGroup.mk' K) (sp lt pool s) =
      (QuotientGroup.mk' K (lt 36)) ^ (List.rec (motive := fun _ => ℕ) 0
        (fun p _ ih => Nat.add ih (Nat.mul p.2 (cntC (nthD List.nil pool p.1)))) s)
  | [] => by simp [sp]
  | p :: s => by
    have ih := mk_sp hK hcodes s
    unfold sp at ih ⊢
    rw [List.map_cons, List.prod_cons, map_mul, ih, map_pow]
    change _ = _ ^ (_ + p.2 * cntC (nthD [] pool p.1))
    unfold pw
    rw [mk_lw K hK _ (nthD_codes hcodes p.1), ← pow_mul, ← pow_add, Nat.add_comm, Nat.mul_comm]

theorem sp_mem (hK : ∀ c, okC c = true → c < 36 → lt c ∈ K) (h36 : lt 36 * lt 36 = 1)
    {pool : List (List ℕ)} (hcodes : ∀ w ∈ pool, ∀ c ∈ w, okC c = true) {s : List (ℕ × ℕ)}
    (he : evS pool s = true) : sp lt pool s ∈ K := by
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, mk_sp K hK hcodes s]
  refine pow_even_eq_one K (by rw [← map_mul, h36, map_one]) ?_
  exact Nat.eq_of_beq_eq_true he

end Parity

theorem closure_left_closed' [Finite G] (S T : Set G) (h1 : (1 : G) ∈ T)
    (hT : ∀ s ∈ S, ∀ t ∈ T, s * t ∈ T) (hTS : T ⊆ Subgroup.closure S) :
    T = Subgroup.closure S := by
  apply Set.Subset.antisymm hTS
  intro g hg
  have hsub : ((Subgroup.closure S : Subgroup G) : Set G) = Submonoid.closure S := by
    have := congrArg (fun K : Submonoid G => (K : Set G))
      (Subgroup.closure_toSubmonoid_of_finite (s := S))
    simpa using this
  have hg' : g ∈ (Submonoid.closure S : Set G) := hsub ▸ hg
  clear hg
  induction hg' using Submonoid.closure_induction_left with
  | one => exact h1
  | mul_left s hs x _ ih => exact hT s hs x ih

theorem zpowers_eq_of_mem [Finite G] {a b : G} (h : a ∈ Subgroup.zpowers b)
    (ho : orderOf a = orderOf b) : Subgroup.zpowers a = Subgroup.zpowers b := by
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 h) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, ho]

theorem orderOf_five {x : G} (h5 : x ^ 5 = 1) (h1 : x ≠ 1) : orderOf x = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime h5 h1

theorem orderOf_pow_five [Finite G] {x : G} (h5 : x ^ 5 = 1) (h1 : x ≠ 1) {e : ℕ} (he1 : 1 ≤ e)
    (he4 : e ≤ 4) : orderOf (x ^ e) = 5 := by
  have hx := orderOf_five h5 h1
  have hcop : Nat.Coprime (orderOf x) e := by rw [hx]; interval_cases e <;> decide
  rw [Nat.Coprime.orderOf_pow hcop, hx]

theorem zpowers_pow [Finite G] {x : G} (h5 : x ^ 5 = 1) (h1 : x ≠ 1) {e : ℕ} (he1 : 1 ≤ e)
    (he4 : e ≤ 4) : Subgroup.zpowers (x ^ e) = Subgroup.zpowers x :=
  zpowers_eq_of_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) e)
    (by rw [orderOf_pow_five h5 h1 he1 he4, orderOf_five h5 h1])

theorem five_dvd_orderOf [Finite G] {P : G} {ex : ℕ} (h1 : P ^ ex ≠ 1) (h5 : (P ^ ex) ^ 5 = 1) :
    5 ∣ orderOf P := by
  have ho := orderOf_five h5 h1
  rw [← ho]
  apply orderOf_dvd_of_pow_eq_one
  rw [← pow_mul, Nat.mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]

theorem facts_of_raw [Finite G] {lt : ℕ → G} {pool : List (List ℕ)} {gens : List ℕ} {nQ : ℕ}
    {lines wl : List (List (ℕ × ℕ))} (K : Subgroup G) [K.Normal]
    (hK : ∀ c, okC c = true → c < 36 → lt c ∈ K) (hr : Raw lt pool gens nQ lines wl) :
    ∃ (Q : Subgroup G) (xs : ℕ → G), Q ≤ K ∧ (∀ i, xs i ∈ K) ∧
      (∀ q ∈ Q, q * pw lt pool 0 = pw lt pool 0 * q) ∧ Nat.card Q = nQ ∧
      (∀ z ∈ Q, orderOf z = 5 → ∃ i < wl.length, ∃ g ∈ K, g * pw lt pool 0 = pw lt pool 0 * g ∧
        Subgroup.zpowers z = Subgroup.zpowers (g * xs i * g⁻¹)) ∧
      (∀ i < wl.length, ∃ l : List G, (∀ k ∈ l, k ∈ K ∧ k * xs i = xs i * k) ∧
        5 ∣ orderOf ((l.map fun k => k * pw lt pool 0 * k⁻¹).prod)) := by
  classical
  have h36 := hr.alph.2.2
  set y := pw lt pool 0 with hy
  set S : Set G := {x : G | ∃ j ∈ gens, x = pw lt pool j} with hS
  obtain ⟨ks, hlen, hnd, h1, hcl, hmon, hcov⟩ := hr.tree
  have hTeq : {x : G | x ∈ ks} = Subgroup.closure S := by
    refine closure_left_closed' S _ h1 ?_ ?_
    · rintro s ⟨j, hj, rfl⟩ t ht
      exact hcl t ht j hj
    · intro k hk
      have hle : Submonoid.closure S ≤ (Subgroup.closure S).toSubmonoid :=
        Submonoid.closure_le.2 fun x hx => Subgroup.subset_closure hx
      exact hle (hmon k hk)
  have hmemQ : ∀ z, z ∈ Subgroup.closure S ↔ z ∈ ks := fun z => by
    rw [← SetLike.mem_coe, ← hTeq, Set.mem_setOf_eq]
  have hspK : ∀ s, evS pool s = true → sp lt pool s ∈ K := fun s hs =>
    sp_mem K hK h36 hr.codes hs
  set xs : ℕ → G := fun i => sp lt pool (wl.getD i []) with hxs
  have hxsK : ∀ i, xs i ∈ K := by
    intro i
    rcases Nat.lt_or_ge i wl.length with hi | hi
    · exact hspK _ (hr.wit i hi).1
    · change sp lt pool (wl.getD i []) ∈ K
      rw [List.getD_eq_default _ _ hi]
      exact K.one_mem
  refine ⟨Subgroup.closure S, xs, ?_, hxsK, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact lw_mem K hK h36 (nthD_codes hr.codes j) (hr.gen j hj).1
  · intro q hq
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hr.gen j hj).2
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hq)
  · have hset : ((Subgroup.closure S : Subgroup G) : Set G) = (ks.toFinset : Set G) := by
      ext z
      rw [SetLike.mem_coe, hmemQ, Finset.mem_coe, List.mem_toFinset]
    change Nat.card ((Subgroup.closure S : Subgroup G) : Set G) = nQ
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen]
  · intro z hz hzo
    rcases hcov z ((hmemQ z).1 hz) with rfl | ⟨n, hn, e, he1, he4, rfl⟩
    · rw [orderOf_one] at hzo
      omega
    have hxm : lines.getD n [] ∈ lines := by
      rw [List.getD_eq_getElem _ _ hn]
      exact List.getElem_mem hn
    obtain ⟨-, hx1, hx5⟩ := hr.line _ hxm
    obtain ⟨i, hi, s, e', hse, he1', he4', hcomm, hconj⟩ := hr.fus n hn
    refine ⟨i, hi, sp lt pool s, hspK s hse, hcomm, ?_⟩
    have hc : sp lt pool s * xs i * (sp lt pool s)⁻¹ = sp lt pool (lines.getD n []) ^ e' :=
      mul_inv_eq_iff_eq_mul.2 hconj
    rw [hc, zpowers_pow hx5 hx1 he1 he4, zpowers_pow hx5 hx1 he1' he4']
  · intro i hi
    obtain ⟨-, gs, ex, hgs, hq1, hq5⟩ := (hr.wit i hi)
    refine ⟨1 :: gs.map (sp lt pool), ?_, ?_⟩
    · intro k hk
      rcases List.mem_cons.1 hk with rfl | hk
      · exact ⟨K.one_mem, by rw [one_mul, mul_one]⟩
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hk
        exact ⟨hspK s (hgs s hs).1, (hgs s hs).2⟩
    · have e : ((1 :: gs.map (sp lt pool)).map fun k => k * y * k⁻¹).prod =
          y * (gs.map fun s => sp lt pool s * y * spI lt pool s).prod := by
        rw [List.map_cons, List.prod_cons, one_mul, inv_one, mul_one, List.map_map]
        congr 2
        refine List.map_congr_left fun s _ => ?_
        rw [Function.comp_apply, spI_eq hr.alph hr.codes]
      rw [e]
      exact five_dvd_orderOf hq1 hq5

end CFSG.KS.HNClsL

end
