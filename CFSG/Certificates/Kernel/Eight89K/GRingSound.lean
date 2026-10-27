module

public import Certificates.Data.Kernel.GRing
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.GRing

open CFSG.KC.PackPerm

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem lenL_eq {α : Type} (l : List α) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem bAnd_eq_true (a b : Bool) :
    Bool.rec (motive := fun _ => Bool) false b a = true ↔ a = true ∧ b = true := by
  cases a <;> simp

theorem allL_iff {α : Type} (l : List α) (f : α → Bool) : allL l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp [allL]
  | cons x l ih =>
    change Bool.rec (motive := fun _ => Bool) false (allL l f) (f x) = true ↔ _
    rw [bAnd_eq_true, ih]
    simp

theorem allLt_iff (n : Nat) (f : Nat → Bool) : allLt n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allLt]
  | succ n ih =>
    change Bool.rec (motive := fun _ => Bool) false (allLt n f) (f n) = true ↔ _
    rw [bAnd_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem mapPt_eq (f : Nat → Nat) (q : List Nat) : mapPt f q = q.map f := by
  induction q with
  | nil => rfl
  | cons x q ih => exact congrArg (f x :: ·) ih

theorem keyMap_eq (d : Nat) (f : Nat → Nat) (q : List Nat) : keyMap d f q = keyOf d (mapPt f q) := by
  induction q with
  | nil => rfl
  | cons x q ih =>
    change Nat.add (f x) (Nat.mul d (keyMap d f q)) = Nat.add (f x) (Nat.mul d (keyOf d (mapPt f q)))
    rw [ih]

theorem gKeys_eq (d P₀ P₁ : Nat) (bs : List Nat) (gm : List (List Nat × (Nat × Bool))) :
    gKeys d P₀ P₁ bs gm = gm.map fun g => (keyOf d (wTup P₀ P₁ bs g.1), g.2) := by
  induction gm with
  | nil => rfl
  | cons g gm ih => exact congrArg (_ :: ·) ih

@[expose] def sgn (c : Nat × Bool) : ℤ := if c.2 then -(c.1 : ℤ) else (c.1 : ℤ)

@[expose] def gVal (gk : List (Nat × (Nat × Bool))) (k : Nat) : ℤ :=
  (gk.map fun g => if g.1 = k then sgn g.2 else 0).sum

@[expose] noncomputable def treeTups (P₀ P₁ : Nat) (bs : List Nat) (tree : List (List Nat × Nat)) :
    List (List Nat) :=
  bs :: tree.map (childOf P₀ P₁)

theorem treeCheck_bs {d : Nat} {l₀ l₁ bs : List Nat} {tree : List (List Nat × Nat)} {N : Nat}
    (h : treeCheck d l₀ l₁ bs tree N = true) : tree.length + 1 = N := by
  unfold treeCheck treeCheckP at h
  simp only [bAnd_eq_true] at h
  have := Nat.eq_of_beq_eq_true h.2.2.2.2.1
  rw [lenL_eq] at this
  exact this

theorem entriesLt_iff (d : Nat) (l : List Nat) : entriesLt d l = true ↔ ∀ x ∈ l, x < d := by
  induction l with
  | nil => simp [entriesLt]
  | cons x l ih =>
    change Bool.rec (motive := fun _ => Bool) false (entriesLt d l) (Nat.blt x d) = true ↔ _
    rw [bAnd_eq_true, ih, Nat.blt_eq]
    simp

theorem elemRun_sound {d P₀ P₁ S : Nat} {ws : List (List Nat)} {k : Nat}
    (h : elemRun d P₀ P₁ S ws k = true) :
    ∀ j < ws.length, ∀ i < d, pget S ((k + j) * d + i) = wimg P₀ P₁ (ws.getD j []) i := by
  induction ws generalizing k with
  | nil =>
    intro j hj
    simp at hj
  | cons w ws ih =>
    change strictB k (fun k => bAnd(allLt d fun i =>
      Nat.beq (pget S (Nat.add (Nat.mul k d) i)) (wimg P₀ P₁ w i),
        elemRun d P₀ P₁ S ws (Nat.succ k))) = true at h
    rw [strictB_eq, bAnd_eq_true, allLt_iff] at h
    intro j hj i hi
    cases j with
    | zero =>
      have := Nat.eq_of_beq_eq_true (h.1 i hi)
      simpa using this
    | succ j =>
      have := ih h.2 j (by simpa using hj) i hi
      rw [List.getD_cons_succ]
      have e : k + (j + 1) = Nat.succ k + j := by omega
      rw [e]
      exact this

theorem tabsCheck_sound {d : Nat} {l₀ l₁ : List Nat} {ws : List (List Nat)} {S : Nat}
    {terms : List (List Nat × Nat)} (h : tabsCheck d l₀ l₁ ws S terms = true) :
    (∀ k < ws.length, ∀ i < d, pget S (k * d + i) = wimg (pack8 l₀) (pack8 l₁) (ws.getD k []) i) ∧
      ∀ t ∈ terms, (∀ f ∈ t.1, f < ws.length) ∧ ∀ i < d, pget t.2 (fimg d S t.1 i) = i := by
  unfold tabsCheck tabsCheckP at h
  simp only [bAnd_eq_true] at h
  obtain ⟨-, -, -, hE, hI⟩ := h
  refine ⟨fun k hk i hi => by simpa using elemRun_sound hE k hk i hi, fun t ht => ?_⟩
  unfold invRun at hI
  rw [allL_iff] at hI
  have := hI t ht
  rw [bAnd_eq_true, entriesLt_iff, allLt_iff, lenL_eq] at this
  exact ⟨this.1, fun i hi => Nat.eq_of_beq_eq_true (this.2 i hi)⟩

theorem bitOf_iff (m k : Nat) : bitOf m k = true ↔ Nat.testBit m k = true := by
  unfold bitOf
  change Nat.beq ((m >>> k) &&& 1) 1 = true ↔ _
  rw [Nat.and_one_is_mod]
  constructor
  · intro h
    have := Nat.eq_of_beq_eq_true h
    rw [Nat.mod_two_eq_one_iff_testBit_zero, Nat.testBit_shiftRight] at this
    simpa using this
  · intro h
    have : (m >>> k) % 2 = 1 := by
      rw [Nat.mod_two_eq_one_iff_testBit_zero, Nat.testBit_shiftRight]
      simpa using h
    rw [this]
    rfl

theorem testBit_or_one_shiftLeft (m k j : Nat) :
    Nat.testBit (Nat.lor m (Nat.shiftLeft 1 k)) j = true ↔ Nat.testBit m j = true ∨ k = j := by
  change Nat.testBit (m ||| (1 <<< k)) j = true ↔ _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_iff]

theorem laneIs_sound {V k : Nat} {c : Nat × Bool} (h : laneIs V k c = true) :
    (lane V k : ℤ) = 32768 + sgn c := by
  obtain ⟨m, s⟩ := c
  cases s
  · have := congrArg (Nat.cast : Nat → ℤ) (Nat.eq_of_beq_eq_true h)
    simp only [sgn, Bool.false_eq_true, ↓reduceIte]
    simp only [Nat.add_eq] at this
    push_cast at this
    linarith
  · have := congrArg (Nat.cast : Nat → ℤ) (Nat.eq_of_beq_eq_true h)
    simp only [sgn, ↓reduceIte]
    simp only [Nat.add_eq] at this
    push_cast at this
    linarith

theorem vRun_sound {d P₀ P₁ V : Nat} {bs : List Nat} {vt : List (List Nat × (Nat × Bool))}
    {k : Nat → Bool} {m : Nat} (h : vRun d P₀ P₁ V bs vt k m = true) :
    ∃ vm, k vm = true ∧
      (∀ j, Nat.testBit vm j = true ↔
        Nat.testBit m j = true ∨ j ∈ vt.map fun t => keyOf d (wTup P₀ P₁ bs t.1)) ∧
      (vt.map fun t => keyOf d (wTup P₀ P₁ bs t.1)).Nodup ∧
      (∀ t ∈ vt, Nat.testBit m (keyOf d (wTup P₀ P₁ bs t.1)) = false) ∧
      ∀ t ∈ vt, (lane V (keyOf d (wTup P₀ P₁ bs t.1)) : ℤ) = 32768 + sgn t.2 := by
  induction vt generalizing m with
  | nil => exact ⟨m, h, fun j => by simp, List.nodup_nil, by simp, by simp⟩
  | cons t vt ih =>
    change strictB m (fun m => strictB (keyOf d (wTup P₀ P₁ bs t.1)) fun kt =>
      bIf(bitOf m kt, false, bAnd(laneIs V kt t.2,
        vRun d P₀ P₁ V bs vt k (Nat.lor m (Nat.shiftLeft 1 kt))))) = true at h
    rw [strictB_eq, strictB_eq] at h
    set kt := keyOf d (wTup P₀ P₁ bs t.1)
    cases hb : bitOf m kt
    · rw [hb] at h
      change Bool.rec (motive := fun _ => Bool) false
        (vRun d P₀ P₁ V bs vt k (Nat.lor m (Nat.shiftLeft 1 kt))) (laneIs V kt t.2) = true at h
      rw [bAnd_eq_true] at h
      obtain ⟨vm, hk, hbits, hnd, hout, hlane⟩ := ih h.2
      have hm : Nat.testBit m kt = false := by
        cases h' : Nat.testBit m kt
        · rfl
        · exact absurd ((bitOf_iff m kt).mpr h') (by rw [hb]; exact Bool.false_ne_true)
      have hnot : ∀ t' ∈ vt, keyOf d (wTup P₀ P₁ bs t'.1) ≠ kt := by
        intro t' ht' he
        have := hout t' ht'
        rw [he] at this
        have h2 := (testBit_or_one_shiftLeft m kt kt).mpr (Or.inr rfl)
        rw [this] at h2
        exact Bool.false_ne_true h2
      refine ⟨vm, hk, fun j => ?_, ?_, ?_, ?_⟩
      · rw [hbits, testBit_or_one_shiftLeft, List.map_cons, List.mem_cons]
        constructor
        · rintro ((h1 | h1) | h1)
          · exact Or.inl h1
          · exact Or.inr (Or.inl h1.symm)
          · exact Or.inr (Or.inr h1)
        · rintro (h1 | h1 | h1)
          · exact Or.inl (Or.inl h1)
          · exact Or.inl (Or.inr h1.symm)
          · exact Or.inr h1
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hm' => ?_, hnd⟩
        rw [List.mem_map] at hm'
        obtain ⟨t', ht', he⟩ := hm'
        exact hnot t' ht' he
      · intro t' ht'
        rcases List.mem_cons.mp ht' with rfl | ht'
        · exact hm
        · have := hout t' ht'
          cases h' : Nat.testBit m (keyOf d (wTup P₀ P₁ bs t'.1))
          · rfl
          · have h2 := (testBit_or_one_shiftLeft m kt _).mpr (Or.inl h')
            rw [this] at h2
            exact absurd h2 Bool.false_ne_true
      · intro t' ht'
        rcases List.mem_cons.mp ht' with rfl | ht'
        · exact laneIs_sound h.1
        · exact hlane t' ht'
    · rw [hb] at h
      exact absurd h Bool.false_ne_true

theorem vCheck_sound {d : Nat} {l₀ l₁ bs : List Nat} {vt : List (List Nat × (Nat × Bool))} {V : Nat}
    {tree : List (List Nat × Nat)} (h : vCheck d l₀ l₁ bs vt V tree = true) :
    (vt.map fun t => keyOf d (wTup (pack8 l₀) (pack8 l₁) bs t.1)).Nodup ∧
      (∀ t ∈ vt, (lane V (keyOf d (wTup (pack8 l₀) (pack8 l₁) bs t.1)) : ℤ) = 32768 + sgn t.2) ∧
      ∀ q ∈ treeTups (pack8 l₀) (pack8 l₁) bs tree,
        keyOf d q ∉ vt.map (fun t => keyOf d (wTup (pack8 l₀) (pack8 l₁) bs t.1)) →
          lane V (keyOf d q) = 32768 := by
  unfold vCheck vCheckP at h
  simp only [bAnd_eq_true] at h
  obtain ⟨-, -, -, hR⟩ := h
  obtain ⟨vm, hk, hbits, hnd, -, hlane⟩ := vRun_sound hR
  rw [bAnd_eq_true, allL_iff] at hk
  refine ⟨hnd, hlane, fun q hq hnot => ?_⟩
  have hd : dflt d V vm q = true := by
    unfold treeTups at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hk.1
    · rw [List.mem_map] at hq
      obtain ⟨e, he, rfl⟩ := hq
      exact hk.2 e he
  unfold dflt at hd
  rw [strictB_eq] at hd
  have hv : bitOf vm (keyOf d q) = false := by
    cases h' : bitOf vm (keyOf d q)
    · rfl
    · have := (hbits _).mp ((bitOf_iff _ _).mp h')
      rw [Nat.zero_testBit] at this
      exact absurd (this.resolve_left Bool.false_ne_true) hnot
  rw [hv] at hd
  exact Nat.eq_of_beq_eq_true hd

theorem keyOf_inj {d : Nat} : ∀ {p q : List Nat}, p.length = q.length → (∀ x ∈ p, x < d) →
    (∀ x ∈ q, x < d) → keyOf d p = keyOf d q → p = q
  | [], [], _, _, _, _ => rfl
  | x :: p, y :: q, hl, hp, hq, hk => by
    change Nat.add x (Nat.mul d (keyOf d p)) = Nat.add y (Nat.mul d (keyOf d q)) at hk
    simp only [Nat.add_eq, Nat.mul_eq] at hk
    have hx := hp x List.mem_cons_self
    have hy := hq y List.mem_cons_self
    have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le x) hx
    have hxy : x = y := by
      have := congrArg (· % d) hk
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
      exact this
    have hpq : keyOf d p = keyOf d q := by
      have := congrArg (· / d) hk
      simp only [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy,
        Nat.zero_add] at this
      exact this
    rw [hxy, keyOf_inj (by simpa using hl) (fun z hz => hp z (List.mem_cons_of_mem _ hz))
      (fun z hz => hq z (List.mem_cons_of_mem _ hz)) hpq]
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl

theorem treeCheck_bsLt {d : Nat} {l₀ l₁ bs : List Nat} {tree : List (List Nat × Nat)} {N : Nat}
    (h : treeCheck d l₀ l₁ bs tree N = true) : ∀ b ∈ bs, b < d := by
  unfold treeCheck treeCheckP at h
  simp only [bAnd_eq_true] at h
  exact (entriesLt_iff d bs).mp h.2.2.2.1

theorem treeRun_sound {d r P₀ P₁ : Nat} {bs : List Nat}
    (hP₀ : ∀ x < d, pget P₀ x < d) (hP₁ : ∀ x < d, pget P₁ x < d) :
    ∀ (tree : List (List Nat × Nat)) (F : List (List Nat)) (m : Nat),
      treeRun d r P₀ P₁ tree m = true →
      (∀ j, Nat.testBit m j = true ↔ j ∈ F.map (keyOf d)) → (F.map (keyOf d)).Nodup →
      (∀ q ∈ F, q.length = r ∧ (∀ x ∈ q, x < d) ∧ ∃ w, q = mapPt (wimg P₀ P₁ w) bs) →
      ((F ++ tree.map (childOf P₀ P₁)).map (keyOf d)).Nodup ∧
        ∀ q ∈ tree.map (childOf P₀ P₁), ∃ w, q = mapPt (wimg P₀ P₁ w) bs
  | [], F, _, _, _, hnd, _ => by simpa using hnd
  | e :: tree, F, m, h, hbits, hnd, hF => by
    change strictB m (fun m => strictB (keyOf d (childOf P₀ P₁ e)) fun kc =>
      bAnd(Nat.beq (lenL e.1) r, bAnd(entriesLt d e.1, bAnd(bitOf m (keyOf d e.1),
        bIf(bitOf m kc, false, treeRun d r P₀ P₁ tree (Nat.lor m (Nat.shiftLeft 1 kc))))))) =
      true at h
    rw [strictB_eq, strictB_eq] at h
    simp only [bAnd_eq_true] at h
    obtain ⟨hlen, hent, hpar, hrest⟩ := h
    rw [lenL_eq] at hlen
    have hlen := Nat.eq_of_beq_eq_true hlen
    rw [entriesLt_iff] at hent
    obtain ⟨q, hqF, hqk⟩ := List.mem_map.mp ((hbits _).mp ((bitOf_iff _ _).mp hpar))
    obtain ⟨hql, hqd, w, hqw⟩ := hF q hqF
    have hpq : e.1 = q := keyOf_inj (by rw [hlen, hql]) hent hqd hqk.symm
    set c := childOf P₀ P₁ e
    have hPe : ∀ x < d, pget (nIf(Nat.beq e.2 0, P₀, P₁)) x < d := by
      intro x hx
      cases Nat.beq e.2 0
      · exact hP₁ x hx
      · exact hP₀ x hx
    have hcw : c = mapPt (wimg P₀ P₁ (e.2 :: w)) bs := by
      change mapPt (pget (nIf(Nat.beq e.2 0, P₀, P₁))) e.1 = _
      rw [hpq, hqw, mapPt_eq, mapPt_eq, mapPt_eq, List.map_map]
      rfl
    have hcl : c.length = r := by
      change (mapPt _ e.1).length = r
      rw [mapPt_eq, List.length_map, hlen]
    have hcd : ∀ x ∈ c, x < d := by
      intro x hx
      change x ∈ mapPt _ e.1 at hx
      rw [mapPt_eq, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hPe y (hent y hy)
    cases hb : bitOf m (keyOf d c)
    · rw [hb] at hrest
      have hcnot : keyOf d c ∉ F.map (keyOf d) := by
        intro hm
        have := (bitOf_iff _ _).mpr ((hbits _).mpr hm)
        rw [hb] at this
        exact Bool.false_ne_true this
      have ih := treeRun_sound hP₀ hP₁ tree (F ++ [c]) _ hrest
        (fun j => by
          rw [testBit_or_one_shiftLeft, hbits, List.map_append, List.mem_append]
          simp [eq_comm])
        (by
          rw [List.map_append, List.nodup_append]
          refine ⟨hnd, List.nodup_singleton _, ?_⟩
          simp only [List.map_cons, List.map_nil, List.mem_singleton]
          rintro a ha b rfl rfl
          exact hcnot ha)
        (fun q' hq' => by
          rcases List.mem_append.mp hq' with hq' | hq'
          · exact hF q' hq'
          · rw [List.mem_singleton] at hq'
            subst hq'
            exact ⟨hcl, hcd, _, hcw⟩)
      refine ⟨?_, ?_⟩
      · have := ih.1
        rwa [List.append_assoc, List.singleton_append] at this
      · intro q' hq'
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact ⟨_, hcw⟩
        · exact ih.2 q' hq'
    · rw [hb] at hrest
      exact absurd hrest Bool.false_ne_true

theorem treeCheck_sound {d : Nat} {l₀ l₁ bs : List Nat} {tree : List (List Nat × Nat)} {N : Nat}
    (hP₀ : ∀ x < d, pget (pack8 l₀) x < d) (hP₁ : ∀ x < d, pget (pack8 l₁) x < d)
    (h : treeCheck d l₀ l₁ bs tree N = true) :
    ((treeTups (pack8 l₀) (pack8 l₁) bs tree).map (keyOf d)).Nodup ∧
      ∀ q ∈ treeTups (pack8 l₀) (pack8 l₁) bs tree,
        ∃ w : List Nat, q = mapPt (wimg (pack8 l₀) (pack8 l₁) w) bs := by
  have hbs := treeCheck_bsLt h
  unfold treeCheck treeCheckP at h
  simp only [bAnd_eq_true] at h
  have hR := h.2.2.2.2.2
  rw [lenL_eq] at hR
  have hid : bs = mapPt (wimg (pack8 l₀) (pack8 l₁) []) bs := by
    rw [mapPt_eq]
    exact (List.map_id' bs).symm
  have := treeRun_sound hP₀ hP₁ tree [bs] _ hR
    (fun j => by
      change Nat.testBit (1 <<< keyOf d bs) j = true ↔ _
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff]
      simp [eq_comm])
    (List.nodup_singleton _)
    (fun q hq => by
      rw [List.mem_singleton] at hq
      subst hq
      exact ⟨rfl, hbs, [], hid⟩)
  refine ⟨this.1, fun q hq => ?_⟩
  unfold treeTups at hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨[], hid⟩
  · exact this.2 q hq

theorem xorRun_sound {d S : Nat} {bs : List Nat} {terms : List (List Nat)} {m : Nat}
    (h : xorRun d S bs terms m = true) (k : Nat) :
    Nat.testBit m k = true ↔ Odd ((terms.map fun fs => keyOf d (mapPt (fimg d S fs) bs)).count k) := by
  induction terms generalizing m with
  | nil =>
    change Nat.beq m 0 = true at h
    rw [Nat.eq_of_beq_eq_true h]
    simp
  | cons fs terms ih =>
    change strictB m (fun m => xorRun d S bs terms
      (Nat.xor m (Nat.shiftLeft 1 (keyOf d (mapPt (fimg d S fs) bs))))) = true at h
    rw [strictB_eq] at h
    have := ih h
    change Nat.testBit (m ^^^ (1 <<< keyOf d (mapPt (fimg d S fs) bs))) k = true ↔ _ at this
    rw [Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow] at this
    rw [List.map_cons, List.count_cons]
    by_cases hk : keyOf d (mapPt (fimg d S fs) bs) = k
    · rw [hk] at this ⊢
      simp only [decide_true, Bool.xor_true, beq_self_eq_true, if_true, Nat.odd_add_one] at this ⊢
      rw [← this]
      cases Nat.testBit m k <;> simp
    · simp only [hk, decide_false, Bool.xor_false, beq_iff_eq, if_false, add_zero] at this ⊢
      exact this

theorem xorCheck_sound {d : Nat} {l₀ l₁ : List Nat} {ws : List (List Nat)} {S : Nat} {bs : List Nat}
    {terms : List (List Nat)} (h : xorCheck d l₀ l₁ ws S bs terms = true) :
    (∀ k < ws.length, ∀ i < d, pget S (k * d + i) = wimg (pack8 l₀) (pack8 l₁) (ws.getD k []) i) ∧
      (∀ fs ∈ terms, ∀ f ∈ fs, f < ws.length) ∧
      ∀ k, Even ((terms.map fun fs => keyOf d (mapPt (fimg d S fs) bs)).count k) := by
  unfold xorCheck xorCheckP at h
  simp only [bAnd_eq_true] at h
  obtain ⟨-, -, -, hE, hA, hX⟩ := h
  refine ⟨fun k hk i hi => by simpa using elemRun_sound hE k hk i hi, fun fs hfs => ?_, fun k => ?_⟩
  · rw [allL_iff] at hA
    have := hA fs hfs
    rwa [entriesLt_iff, lenL_eq] at this
  · have := xorRun_sound hX k
    rw [Nat.zero_testBit] at this
    exact Nat.not_odd_iff_even.mp fun ho => Bool.false_ne_true (this.mpr ho)

theorem tSum_eq (d V : Nat) (terms : List (List Nat × Nat)) (q : List Nat) :
    tSum d V terms q = (terms.map fun t => lane V (keyMap d (pget t.2) q)).sum := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
    change Nat.add _ (tSum d V terms q) = _
    rw [ih, List.map_cons, List.sum_cons]
    rfl

theorem gSum_sub (gk : List (Nat × (Nat × Bool))) (k : Nat) :
    (gSum gk k false : ℤ) - gSum gk k true = gVal gk k := by
  induction gk with
  | nil => rfl
  | cons g gk ih =>
    unfold gVal at ih ⊢
    rw [List.map_cons, List.sum_cons, ← ih]
    change ((Nat.add (nIf(Nat.beq g.1 k, nIf(Bool.rec (motive := fun _ => Bool) (!false) false g.2.2,
      g.2.1, 0), 0)) (gSum gk k false) : Nat) : ℤ) -
      ((Nat.add (nIf(Nat.beq g.1 k, nIf(Bool.rec (motive := fun _ => Bool) (!true) true g.2.2,
        g.2.1, 0), 0)) (gSum gk k true) : Nat) : ℤ) = _
    obtain ⟨g1, g2, s⟩ := g
    dsimp only
    cases hb : Nat.beq g1 k
    · have hk : g1 ≠ k := Nat.ne_of_beq_eq_false hb
      dsimp only
      rw [if_neg hk, Nat.add_eq, Nat.add_eq]
      push_cast
      ring
    · have hk : g1 = k := Nat.eq_of_beq_eq_true hb
      rw [if_pos hk]
      cases s
      · simp only [Bool.not_false, Bool.not_true, Nat.add_eq, sgn, Bool.false_eq_true, if_false]
        push_cast
        ring
      · simp only [Bool.not_false, Bool.not_true, Nat.add_eq, sgn, if_true]
        push_cast
        ring

theorem sumAt_sound {d V : Nat} {terms : List (List Nat × Nat)} {gk : List (Nat × (Nat × Bool))}
    {q : List Nat} (h : sumAt d V terms gk q = true) :
    ((terms.map fun t => (lane V (keyMap d (pget t.2) q) : ℤ)).sum) =
      32768 * terms.length + gVal gk (keyOf d q) := by
  unfold sumAt at h
  rw [strictB_eq] at h
  have h := Nat.eq_of_beq_eq_true h
  rw [tSum_eq, lenL_eq] at h
  simp only [Nat.add_eq, Nat.mul_eq] at h
  rw [← gSum_sub]
  have h' := congrArg (fun n : Nat => (n : ℤ)) h
  push_cast at h'
  have : ((terms.map fun t => (lane V (keyMap d (pget t.2) q) : ℤ)).sum) =
      ((terms.map fun t => lane V (keyMap d (pget t.2) q)).map (Nat.cast : Nat → ℤ)).sum := by
    rw [List.map_map]
    rfl
  rw [this]
  linarith

section Group

variable {d : Nat} (σ₀ σ₁ : Equiv.Perm (Fin d))

@[expose] def genP (i : Nat) : Equiv.Perm (Fin d) := if i = 0 then σ₀ else σ₁

theorem genP_mem (i : Nat) :
    genP σ₀ σ₁ i ∈ Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))) := by
  unfold genP
  split_ifs
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

@[expose] def gen (i : Nat) : Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))) :=
  ⟨genP σ₀ σ₁ i, genP_mem σ₀ σ₁ i⟩

@[expose] def wordM (w : List Nat) : Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))) :=
  (w.map (gen σ₀ σ₁)).prod

@[expose] def act (g : Equiv.Perm (Fin d)) (x : Nat) : Nat := if h : x < d then (g ⟨x, h⟩ : Nat) else x

variable {σ₀ σ₁}

theorem act_lt {g : Equiv.Perm (Fin d)} {x : Nat} (hx : x < d) : act g x < d := by
  unfold act
  rw [dif_pos hx]
  exact (g _).isLt

theorem act_mul (g h : Equiv.Perm (Fin d)) (x : Nat) : act (g * h) x = act g (act h x) := by
  unfold act
  by_cases hx : x < d
  · simp only [dif_pos hx, dif_pos (h ⟨x, hx⟩).isLt]
    rfl
  · rw [dif_neg hx, dif_neg hx, dif_neg hx]

theorem act_one (x : Nat) : act (1 : Equiv.Perm (Fin d)) x = x := by
  unfold act
  split_ifs <;> rfl

theorem act_act_inv (g : Equiv.Perm (Fin d)) (x : Nat) : act g (act g⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem coe_wordM_cons (i : Nat) (w : List Nat) :
    ((wordM σ₀ σ₁ (i :: w) : _) : Equiv.Perm (Fin d)) = genP σ₀ σ₁ i * (wordM σ₀ σ₁ w : _) := by
  unfold wordM
  rw [List.map_cons, List.prod_cons, Subgroup.coe_mul]
  rfl

@[expose] noncomputable def keyM (bs : List Nat) (g : Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d)))) :
    Nat :=
  keyOf d (mapPt (act (g : Equiv.Perm (Fin d))) bs)

variable {P₀ P₁ : Nat}
variable (h₀ : ∀ x : Fin d, (σ₀ x : Nat) = pget P₀ x) (h₁ : ∀ x : Fin d, (σ₁ x : Nat) = pget P₁ x)
include h₀ h₁

theorem pget_gen (i : Nat) {x : Nat} (hx : x < d) :
    pget (nIf(Nat.beq i 0, P₀, P₁)) x = act (genP σ₀ σ₁ i) x := by
  unfold act genP
  rw [dif_pos hx]
  by_cases hi : i = 0
  · subst hi
    rw [if_pos rfl]
    exact (h₀ ⟨x, hx⟩).symm
  · have : Nat.beq i 0 = false := by
      cases h : Nat.beq i 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hi
    rw [this, if_neg hi]
    exact (h₁ ⟨x, hx⟩).symm

theorem wimg_eq (w : List Nat) {x : Nat} (hx : x < d) :
    wimg P₀ P₁ w x = act (wordM σ₀ σ₁ w : Equiv.Perm (Fin d)) x := by
  induction w with
  | nil => exact (act_one x).symm
  | cons i w ih =>
    change pget (nIf(Nat.beq i 0, P₀, P₁)) (wimg P₀ P₁ w x) = _
    rw [ih, pget_gen h₀ h₁ i (act_lt hx), coe_wordM_cons, act_mul]

theorem wTup_eq {bs : List Nat} (hbs : ∀ b ∈ bs, b < d) (w : List Nat) :
    wTup P₀ P₁ bs w = mapPt (act (wordM σ₀ σ₁ w : Equiv.Perm (Fin d))) bs := by
  unfold wTup
  rw [mapPt_eq, mapPt_eq]
  exact List.map_congr_left fun b hb => wimg_eq h₀ h₁ w (hbs b hb)

omit h₀ h₁ in
theorem keyM_injective {l₀ l₁ bs : List Nat} {tree : List (List Nat × Nat)} {N : Nat}
    (h₀ : ∀ x : Fin d, (σ₀ x : Nat) = pget (pack8 l₀) x)
    (h₁ : ∀ x : Fin d, (σ₁ x : Nat) = pget (pack8 l₁) x)
    (hT : treeCheck d l₀ l₁ bs tree N = true)
    (hM : Nat.card (Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d)))) ≤ N) :
    Function.Injective (keyM (σ₀ := σ₀) (σ₁ := σ₁) bs) ∧
      ∀ g : Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))),
        mapPt (act (g : Equiv.Perm (Fin d))) bs ∈ treeTups (pack8 l₀) (pack8 l₁) bs tree := by
  classical
  have : Fintype (Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d)))) := Fintype.ofFinite _
  have hP₀ : ∀ x < d, pget (pack8 l₀) x < d := fun x hx => by
    rw [← h₀ ⟨x, hx⟩]
    exact (σ₀ _).isLt
  have hP₁ : ∀ x < d, pget (pack8 l₁) x < d := fun x hx => by
    rw [← h₁ ⟨x, hx⟩]
    exact (σ₁ _).isLt
  obtain ⟨hnd, hw⟩ := treeCheck_sound hP₀ hP₁ hT
  have hbs := treeCheck_bsLt hT
  have hlen := treeCheck_bs hT
  set L := treeTups (pack8 l₀) (pack8 l₁) bs tree
  have hLlen : L.length = N := by simp [L, treeTups, hlen]
  have hel : ∀ q ∈ L, ∃ g : Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))),
      q = mapPt (act (g : Equiv.Perm (Fin d))) bs := by
    intro q hq
    obtain ⟨w, rfl⟩ := hw q hq
    exact ⟨wordM σ₀ σ₁ w, wTup_eq h₀ h₁ hbs w⟩
  let K := (Finset.univ : Finset (Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))))).image
    (keyM bs)
  have hsub : (L.map (keyOf d)).toFinset ⊆ K := by
    intro k hk
    rw [List.mem_toFinset, List.mem_map] at hk
    obtain ⟨q, hq, rfl⟩ := hk
    obtain ⟨g, rfl⟩ := hel q hq
    exact Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩
  have hcardL : (L.map (keyOf d)).toFinset.card = N := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map, hLlen]
  have hcardK : K.card ≤ (Finset.univ : Finset (Subgroup.closure
      ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))))).card := Finset.card_image_le
  have huniv : (Finset.univ : Finset (Subgroup.closure
      ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))))).card ≤ N := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hM
  have hKL := Finset.card_le_card hsub
  have hinj : Function.Injective (keyM (σ₀ := σ₀) (σ₁ := σ₁) bs) := by
    have hc : K.card = (Finset.univ : Finset (Subgroup.closure
        ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))))).card := by omega
    have := Finset.card_image_iff.mp hc
    exact fun a b hab => this (Finset.mem_coe.mpr (Finset.mem_univ a))
      (Finset.mem_coe.mpr (Finset.mem_univ b)) hab
  have hKeq : (L.map (keyOf d)).toFinset = K := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨hinj, fun g => ?_⟩
  have hk : keyM bs g ∈ (L.map (keyOf d)).toFinset := by
    rw [hKeq]
    exact Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩
  rw [List.mem_toFinset, List.mem_map] at hk
  obtain ⟨q, hq, hqk⟩ := hk
  obtain ⟨g', rfl⟩ := hel q hq
  have : g' = g := hinj hqk
  rwa [this] at hq

end Group

section Sums

variable {G A : Type*} [Fintype G] [DecidableEq G] [AddCommGroup A]

theorem sum_expand (f : G → A) (l : List (ℤ × G)) :
    (l.map fun x => x.1 • f x.2).sum =
      ∑ g, (l.map fun x => if x.2 = g then x.1 else 0).sum • f g := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, add_smul, Finset.sum_add_distrib, ← ih, ite_smul,
      zero_smul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem sum_count (f : G → A) (l : List G) : (l.map f).sum = ∑ g, l.count g • f g := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.count_cons, add_smul, Finset.sum_add_distrib,
      ← ih, beq_iff_eq, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    abel

omit [Fintype G] [DecidableEq G] [AddCommGroup A] in
theorem prod_flat {R : Type*} [Ring R] [Monoid G] (ρ : G →* R) (hs : List G) (vl : List (ℤ × G)) :
    (hs.map ρ).sum * (vl.map fun x => x.1 • ρ x.2).sum =
      ((hs.flatMap fun h => vl.map fun x => (x.1, h * x.2)).map fun x => x.1 • ρ x.2).sum := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
    rw [List.map_cons, List.sum_cons, add_mul, ih, List.flatMap_cons, List.map_append,
      List.sum_append, ← List.sum_map_mul_left, List.map_map]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
    simp only [Function.comp, map_mul, mul_smul_comm]

omit [Fintype G] [AddCommGroup A] in
theorem sum_const_add {β : Type*} (l : List β) (c : ℤ) (f : β → ℤ) :
    (l.map fun t => c + f t).sum = c * l.length + (l.map f).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    push_cast
    ring

@[expose] def coef {G : Type*} [DecidableEq G] (vl : List (ℤ × G)) (g : G) : ℤ :=
  (vl.map fun x => if x.2 = g then x.1 else 0).sum

omit [Fintype G] in
theorem coef_flat [Group G] (hs : List G) (vl : List (ℤ × G)) (g : G) :
    coef (hs.flatMap fun h => vl.map fun x => (x.1, h * x.2)) g =
      (hs.map fun h => coef vl (h⁻¹ * g)).sum := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih]
    unfold coef
    rw [List.map_append, List.sum_append, List.map_map]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
    simp only [Function.comp]
    by_cases hx : x.2 = h⁻¹ * g
    · rw [if_pos hx, if_pos (by rw [hx, mul_inv_cancel_left])]
    · rw [if_neg hx, if_neg (fun h' => hx (by rw [← h', inv_mul_cancel_left]))]

end Sums

section Ident

variable {d : Nat} {σ₀ σ₁ : Equiv.Perm (Fin d)}

@[expose] def fprod (σ₀ σ₁ : Equiv.Perm (Fin d)) (ws : List (List Nat)) (fs : List Nat) :
    Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))) :=
  (fs.map fun f => wordM σ₀ σ₁ (ws.getD f [])).prod

theorem fimg_eq {l₀ l₁ : List Nat} (h₀ : ∀ x : Fin d, (σ₀ x : Nat) = pget (pack8 l₀) x)
    (h₁ : ∀ x : Fin d, (σ₁ x : Nat) = pget (pack8 l₁) x) {ws : List (List Nat)} {S : Nat}
    (hS : ∀ k < ws.length, ∀ i < d, pget S (k * d + i) = wimg (pack8 l₀) (pack8 l₁) (ws.getD k []) i)
    (fs : List Nat) (hfs : ∀ f ∈ fs, f < ws.length) {x : Nat} (hx : x < d) :
    fimg d S fs x = act (fprod σ₀ σ₁ ws fs : Equiv.Perm (Fin d)) x := by
  induction fs with
  | nil => exact (act_one x).symm
  | cons f fs ih =>
    have ih := ih fun g hg => hfs g (List.mem_cons_of_mem _ hg)
    change pget S (Nat.add (Nat.mul f d) (fimg d S fs x)) = _
    rw [ih]
    unfold fprod
    rw [List.map_cons, List.prod_cons, Subgroup.coe_mul, act_mul]
    change pget S (f * d + _) = _
    rw [hS f (hfs f List.mem_cons_self) _ (act_lt hx), wimg_eq h₀ h₁ _ (act_lt hx)]

theorem sum_eq_zero_of_xor {l₀ l₁ : List Nat} (h₀ : ∀ x : Fin d, (σ₀ x : Nat) = pget (pack8 l₀) x)
    (h₁ : ∀ x : Fin d, (σ₁ x : Nat) = pget (pack8 l₁) x) {ws : List (List Nat)} {S : Nat}
    {bs : List Nat} {terms : List (List Nat)} (hX : xorCheck d l₀ l₁ ws S bs terms = true)
    (hbs : ∀ b ∈ bs, b < d) (hinj : Function.Injective (keyM (σ₀ := σ₀) (σ₁ := σ₁) bs))
    (A : Type*) [Ring A] (h2 : (2 : A) = 0)
    (f : Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))) → A) :
    (terms.map fun fs => f (fprod σ₀ σ₁ ws fs)).sum = 0 := by
  classical
  obtain ⟨hS, hf, hev⟩ := xorCheck_sound hX
  have hkeys : (terms.map fun fs => keyOf d (mapPt (fimg d S fs) bs)) =
      (terms.map (fprod σ₀ σ₁ ws)).map (keyM bs) := by
    rw [List.map_map]
    refine List.map_congr_left fun fs hfs => ?_
    unfold keyM
    simp only [Function.comp]
    congr 1
    rw [mapPt_eq, mapPt_eq]
    exact List.map_congr_left fun b hb => fimg_eq h₀ h₁ hS fs (hf fs hfs) (hbs b hb)
  have hmap : (terms.map fun fs => f (fprod σ₀ σ₁ ws fs)) = (terms.map (fprod σ₀ σ₁ ws)).map f := by
    rw [List.map_map]
    rfl
  rw [hmap, sum_count]
  refine Finset.sum_eq_zero fun g _ => ?_
  have hc := hev (keyM bs g)
  rw [hkeys, List.count_map_of_injective _ _ hinj] at hc
  have key : ∀ n : Nat, Even n → n • f g = 0 := by
    rintro n ⟨k, rfl⟩
    rw [add_nsmul, ← nsmul_add, ← two_mul, h2, zero_mul, nsmul_zero]
  apply key
  convert hc

theorem coef_nodup {G : Type*} [DecidableEq G] {β : Type*} (vl : List β) (val : β → ℤ)
    (el : β → G) (hnd : (vl.map el).Nodup) :
    ∀ t ∈ vl, ((vl.map fun x => (val x, el x)).map fun x => if x.2 = el t then x.1 else 0).sum =
      val t := by
  induction vl with
  | nil => simp
  | cons a vl ih =>
    intro t ht
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.map_cons, List.map_map, List.sum_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · rw [if_pos rfl]
      have : (vl.map ((fun x => if x.2 = el t then x.1 else 0) ∘ fun x => (val x, el x))).sum = 0 := by
        refine List.sum_eq_zero fun y hy => ?_
        rw [List.mem_map] at hy
        obtain ⟨b, hb, rfl⟩ := hy
        have hne : el b ≠ el t := fun h => hnd.1 (by rw [← h]; exact List.mem_map_of_mem hb)
        simp only [Function.comp, if_neg hne]
      rw [this, add_zero]
    · have hne : el a ≠ el t := fun h => hnd.1 (by rw [h]; exact List.mem_map_of_mem ht)
      simp only [Function.comp, if_neg hne, zero_add]
      have := ih hnd.2 t ht
      rwa [List.map_map] at this

theorem coef_not_mem {G : Type*} [DecidableEq G] {β : Type*} (vl : List β) (val : β → ℤ)
    (el : β → G) (g : G) (hg : g ∉ vl.map el) :
    ((vl.map fun x => (val x, el x)).map fun x => if x.2 = g then x.1 else 0).sum = 0 := by
  rw [List.map_map]
  refine List.sum_eq_zero fun y hy => ?_
  rw [List.mem_map] at hy
  obtain ⟨b, hb, rfl⟩ := hy
  have hne : el b ≠ g := fun h => hg (by rw [← h]; exact List.mem_map_of_mem hb)
  simp only [Function.comp, if_neg hne]

theorem prod_eq_of_checks {l₀ l₁ : List Nat} (h₀ : ∀ x : Fin d, (σ₀ x : Nat) = pget (pack8 l₀) x)
    (h₁ : ∀ x : Fin d, (σ₁ x : Nat) = pget (pack8 l₁) x) {bs : List Nat}
    {tree : List (List Nat × Nat)} {N : Nat} (hT : treeCheck d l₀ l₁ bs tree N = true)
    (hM : Nat.card (Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d)))) ≤ N)
    {ws : List (List Nat)} {S : Nat} {terms : List (List Nat × Nat)}
    {vt gm : List (List Nat × (Nat × Bool))} {V : Nat}
    (hH : tabsCheck d l₀ l₁ ws S terms = true) (hV : vCheck d l₀ l₁ bs vt V tree = true)
    (hR : sumRoot d l₀ l₁ V terms gm bs = true)
    (hC : ∀ e ∈ tree, ∃ es, e ∈ es ∧ sumChunk d l₀ l₁ V terms gm bs es = true)
    (A : Type*) [Ring A] (ρ : Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))) →* A) :
    (terms.map fun t => ρ (fprod σ₀ σ₁ ws t.1)).sum *
        (vt.map fun t => sgn t.2 • ρ (wordM σ₀ σ₁ t.1)).sum =
      (gm.map fun g => sgn g.2 • ρ (wordM σ₀ σ₁ g.1)).sum := by
  classical
  obtain ⟨hinj, hcov⟩ := keyM_injective h₀ h₁ hT hM
  have hbs := treeCheck_bsLt hT
  obtain ⟨hS, hterm⟩ := tabsCheck_sound hH
  obtain ⟨hvnd, hvlane, hvdflt⟩ := vCheck_sound hV
  set P₀ := pack8 l₀
  set P₁ := pack8 l₁
  let hs := terms.map fun t => fprod σ₀ σ₁ ws t.1
  let vl := vt.map fun t => (sgn t.2, wordM σ₀ σ₁ t.1)
  let gl := gm.map fun g => (sgn g.2, wordM σ₀ σ₁ g.1)
  have hkw : ∀ w, keyOf d (wTup P₀ P₁ bs w) = keyM bs (wordM σ₀ σ₁ w) := fun w => by
    unfold keyM
    rw [wTup_eq h₀ h₁ hbs]
  have hlane : ∀ x : Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))),(lane V (keyM bs x) : ℤ) = 32768 + coef vl x := by
    intro x
    have hvnd' : (vt.map fun t => wordM σ₀ σ₁ t.1).Nodup := by
      refine List.Nodup.of_map (keyM bs) ?_
      rw [List.map_map]
      have := hvnd
      simp only [hkw] at this
      exact this
    by_cases hx : x ∈ vt.map fun t => wordM σ₀ σ₁ t.1
    · rw [List.mem_map] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      rw [← hkw, hvlane t ht]
      unfold coef
      rw [coef_nodup vt (fun t => sgn t.2) (fun t => wordM σ₀ σ₁ t.1) hvnd' t ht]
    · unfold coef
      rw [coef_not_mem vt (fun t => sgn t.2) (fun t => wordM σ₀ σ₁ t.1) x hx, add_zero]
      have hq := hcov x
      have hnot : keyOf d (mapPt (act (x : Equiv.Perm (Fin d))) bs) ∉
          vt.map fun t => keyOf d (wTup P₀ P₁ bs t.1) := by
        intro hm
        rw [List.mem_map] at hm
        obtain ⟨t, ht, htk⟩ := hm
        rw [hkw] at htk
        exact hx (List.mem_map.mpr ⟨t, ht, hinj htk⟩)
      unfold keyM
      rw [hvdflt _ hq hnot]
      norm_num
  have hgam : ∀ g : Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))),gVal (gKeys d P₀ P₁ bs gm) (keyM bs g) = coef gl g := by
    intro g
    unfold gVal coef
    rw [gKeys_eq, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp, hkw]
    by_cases hxg : wordM σ₀ σ₁ x.1 = g
    · rw [if_pos hxg, if_pos (congrArg _ hxg)]
    · rw [if_neg hxg, if_neg (fun h => hxg (hinj h))]
  have hsum : ∀ g : Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))),
      (terms.map fun t => coef vl ((fprod σ₀ σ₁ ws t.1)⁻¹ * g)).sum = coef gl g := by
    intro g
    have hq := hcov g
    have hchk : sumAt d V terms (gKeys d P₀ P₁ bs gm)
        (mapPt (act (g : Equiv.Perm (Fin d))) bs) = true := by
      unfold treeTups at hq
      rcases List.mem_cons.mp hq with hq | hq
      · rw [hq]
        exact hR
      · rw [List.mem_map] at hq
        obtain ⟨e, he, hce⟩ := hq
        obtain ⟨es, hes, hck⟩ := hC e he
        unfold sumChunk sumChunkP at hck
        rw [allL_iff] at hck
        rw [← hce]
        exact hck e hes
    have h := sumAt_sound hchk
    have hk : ∀ t ∈ terms, keyMap d (pget t.2) (mapPt (act (g : Equiv.Perm (Fin d))) bs) =
        keyM bs ((fprod σ₀ σ₁ ws t.1)⁻¹ * g) := by
      intro t ht
      obtain ⟨hf, hinv⟩ := hterm t ht
      rw [keyMap_eq]
      unfold keyM
      congr 1
      rw [mapPt_eq, mapPt_eq, mapPt_eq, List.map_map]
      refine List.map_congr_left fun b hb => ?_
      simp only [Function.comp, Subgroup.coe_mul, Subgroup.coe_inv, act_mul]
      set h := (fprod σ₀ σ₁ ws t.1 : Equiv.Perm (Fin d))
      have hy : act (g : Equiv.Perm (Fin d)) b < d := act_lt (hbs b hb)
      have := hinv _ (act_lt (g := h⁻¹) hy)
      rw [fimg_eq h₀ h₁ hS t.1 hf (act_lt hy), act_act_inv] at this
      exact this
    rw [List.map_congr_left (fun t ht => by rw [hk t ht])] at h
    simp only [hlane] at h
    have hkg : keyOf d (mapPt (act (g : Equiv.Perm (Fin d))) bs) = keyM bs g := rfl
    rw [hkg, hgam] at h
    rw [sum_const_add] at h
    linarith
  have hprod := prod_flat ρ hs vl
  have hl : (terms.map fun t => ρ (fprod σ₀ σ₁ ws t.1)).sum = (hs.map ρ).sum := by
    simp only [hs, List.map_map]
    rfl
  have hv : (vt.map fun t => sgn t.2 • ρ (wordM σ₀ σ₁ t.1)).sum =
      (vl.map fun x => x.1 • ρ x.2).sum := by
    simp only [vl, List.map_map]
    rfl
  have hg : (gm.map fun g => sgn g.2 • ρ (wordM σ₀ σ₁ g.1)).sum =
      (gl.map fun x => x.1 • ρ x.2).sum := by
    simp only [gl, List.map_map]
    rfl
  rw [hl, hv, hg, hprod, sum_expand, sum_expand]
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1
  change coef _ g = coef gl g
  rw [← hsum g, coef_flat]
  simp only [hs, List.map_map]
  rfl

@[expose] def expand (e : Nat) (ps : List (Nat × Nat)) : List (List Nat) :=
  ps.flatMap fun p => (List.range 5).map fun m => p.1 :: (List.replicate m e ++ [p.2])

theorem sum_expand_pairs (ws : List (List Nat)) (e : Nat) (ps : List (Nat × Nat)) (A : Type*)
    [Ring A] (ρ : Subgroup.closure ({σ₀, σ₁} : Set (Equiv.Perm (Fin d))) →* A) :
    ((expand e ps).map fun fs => ρ (fprod σ₀ σ₁ ws fs)).sum =
      ((ps.map fun p => (wordM σ₀ σ₁ (ws.getD p.1 []), wordM σ₀ σ₁ (ws.getD p.2 []))).map
        fun x => ρ x.1 * (∑ m ∈ Finset.range 5, ρ (wordM σ₀ σ₁ (ws.getD e [])) ^ m) * ρ x.2).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [expand, List.flatMap_cons, List.map_append, List.sum_append, ← expand, ih, List.map_cons,
      List.map_cons, List.sum_cons]
    congr 1
    simp only [List.map_map, Function.comp, fprod, List.map_cons, List.map_append,
      List.map_replicate, List.prod_cons, List.prod_append, List.prod_replicate, List.prod_singleton,
      map_mul, map_pow, Finset.mul_sum, Finset.sum_mul]
    simp [List.range_succ, Finset.sum_range_succ, mul_assoc, pow_succ, mul_add, add_mul, add_assoc]

end Ident

end CFSG.KC.GRing

end
