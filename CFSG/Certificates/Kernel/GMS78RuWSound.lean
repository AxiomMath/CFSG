module

public import Certificates.Data.Kernel.GMS78RuW
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Order.Interval.Finset.Box
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Bool
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.GMSW

open CFSG.KC.Ord

theorem andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem blt_false {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · rw [Nat.blt_eq] at e
    exact absurd e h

theorem letEq_eq : ∀ {x y : Nat × Bool}, letEq x y = true → x = y
  | (g, s), (h, t), e => by
    have e' : andB (Nat.beq g h) (Bool.rec (motive := fun _ => Bool) (notB t) t s) = true := e
    obtain ⟨h1, h2⟩ := andB_eq_true.1 e'
    rw [Nat.eq_of_beq_eq_true h1]
    cases s <;> cases t <;> first | rfl | exact absurd h2 (by decide)

theorem wordEq_eq : ∀ {u v : List (Nat × Bool)}, wordEq u v = true → u = v
  | [], [], _ => rfl
  | [], _ :: _, e => by simp [wordEq] at e
  | _ :: _, [], e => by simp [wordEq] at e
  | x :: u, y :: v, e => by
    have e' : andB (letEq x y) (wordEq u v) = true := e
    obtain ⟨h1, h2⟩ := andB_eq_true.1 e'
    rw [letEq_eq h1, wordEq_eq h2]

theorem relsEqK_eq : ∀ {a b : List (List (Nat × Bool))}, relsEqK a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, e => by simp [relsEqK] at e
  | _ :: _, [], e => by simp [relsEqK] at e
  | u :: a, v :: b, e => by
    have e' : andB (wordEq u v) (relsEqK a b) = true := e
    obtain ⟨h1, h2⟩ := andB_eq_true.1 e'
    rw [wordEq_eq h1, relsEqK_eq h2]

theorem relsAll_spec {RB : Nat → Nat} {mul : Nat → Nat → Nat} {rels : List (List (Nat × Bool))}
    {L ONE lo : Nat} : ∀ {k : Nat}, relsAll RB mul rels L ONE lo k = true →
      ∀ i < k, relOK RB mul rels L ONE (lo + i) = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, h, i, hi => by
    have h' : andB (relsAll RB mul rels L ONE lo k) (relOK RB mul rels L ONE (Nat.add lo k)) =
      true := h
    obtain ⟨h1, h2⟩ := andB_eq_true.1 h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact relsAll_spec h1 i hi
    · exact h2

theorem relsAll_add {RB : Nat → Nat} {mul : Nat → Nat → Nat} {rels : List (List (Nat × Bool))}
    {L ONE lo a : Nat} (ha : relsAll RB mul rels L ONE lo a = true) :
    ∀ {b : Nat}, relsAll RB mul rels L ONE (lo + a) b = true →
      relsAll RB mul rels L ONE lo (a + b) = true
  | 0, _ => ha
  | b + 1, h => by
    have h' : andB (relsAll RB mul rels L ONE (lo + a) b)
        (relOK RB mul rels L ONE (Nat.add (lo + a) b)) = true := h
    obtain ⟨h1, h2⟩ := andB_eq_true.1 h'
    change andB (relsAll RB mul rels L ONE lo (a + b)) (relOK RB mul rels L ONE (lo + (a + b))) =
      true
    rw [relsAll_add ha h1, ← Nat.add_assoc]
    exact h2

theorem relsAll_join {RB : Nat → Nat} {mul : Nat → Nat → Nat} {rels : List (List (Nat × Bool))}
    {L ONE lo a lo' b c : Nat} (ha : relsAll RB mul rels L ONE lo a = true)
    (hb : relsAll RB mul rels L ONE lo' b = true) (h1 : lo + a = lo') (h2 : a + b = c) :
    relsAll RB mul rels L ONE lo c = true := by
  subst h1 h2
  exact relsAll_add ha hb

theorem relsNeAll_spec {RB : Nat → Nat} {mul : Nat → Nat → Nat} {rels : List (List (Nat × Bool))}
    {L ONE lo : Nat} : ∀ {k : Nat}, relsNeAll RB mul rels L ONE lo k = true →
      ∀ i < k, relNeOK RB mul rels L ONE (lo + i) = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, h, i, hi => by
    have h' : andB (relsNeAll RB mul rels L ONE lo k) (relNeOK RB mul rels L ONE (Nat.add lo k)) =
      true := h
    obtain ⟨h1, h2⟩ := andB_eq_true.1 h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact relsNeAll_spec h1 i hi
    · exact h2

theorem relsNeAll_add {RB : Nat → Nat} {mul : Nat → Nat → Nat} {rels : List (List (Nat × Bool))}
    {L ONE lo a : Nat} (ha : relsNeAll RB mul rels L ONE lo a = true) :
    ∀ {b : Nat}, relsNeAll RB mul rels L ONE (lo + a) b = true →
      relsNeAll RB mul rels L ONE lo (a + b) = true
  | 0, _ => ha
  | b + 1, h => by
    have h' : andB (relsNeAll RB mul rels L ONE (lo + a) b)
        (relNeOK RB mul rels L ONE (Nat.add (lo + a) b)) = true := h
    obtain ⟨h1, h2⟩ := andB_eq_true.1 h'
    change andB (relsNeAll RB mul rels L ONE lo (a + b))
      (relNeOK RB mul rels L ONE (lo + (a + b))) = true
    rw [relsNeAll_add ha h1, ← Nat.add_assoc]
    exact h2

theorem relsNeAll_join {RB : Nat → Nat} {mul : Nat → Nat → Nat} {rels : List (List (Nat × Bool))}
    {L ONE lo a lo' b c : Nat} (ha : relsNeAll RB mul rels L ONE lo a = true)
    (hb : relsNeAll RB mul rels L ONE lo' b = true) (h1 : lo + a = lo') (h2 : a + b = c) :
    relsNeAll RB mul rels L ONE lo c = true := by
  subst h1 h2
  exact relsNeAll_add ha hb

theorem lenL_eq {α : Type} : ∀ l : List α, lenL l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenL l) = _
    rw [lenL_eq l]
    rfl

theorem exists_nthRel : ∀ {rels : List (List (Nat × Bool))} {v}, v ∈ rels →
    ∃ r < lenRels rels, nthRel rels r = v
  | u :: rels, v, hv => by
    rcases List.mem_cons.1 hv with rfl | hv
    · exact ⟨0, Nat.succ_pos _, rfl⟩
    · obtain ⟨r, hr, e⟩ := exists_nthRel hv
      exact ⟨r + 1, Nat.succ_lt_succ hr, e⟩

theorem relsAll_all {RB : Nat → Nat} {mul : Nat → Nat → Nat} {rels : List (List (Nat × Bool))}
    {L ONE n : Nat} (h : relsAll RB mul rels L ONE 0 n = true) (hn : Nat.beq (lenRels rels) n = true) :
    ∀ r < lenRels rels, relOK RB mul rels L ONE r = true ∨ ∃ s < r, relDupOK rels s r = true := by
  intro r hr
  rw [Nat.eq_of_beq_eq_true hn] at hr
  have := relsAll_spec h r hr
  rw [Nat.zero_add] at this
  exact Or.inl this

theorem appK_eq : ∀ u v : List (Nat × Bool), appK u v = u ++ v
  | [], _ => rfl
  | x :: u, v => by
    change x :: appK u v = _
    rw [appK_eq u v]
    rfl

theorem imgWordK_eq : ∀ w : List Int, imgWordK w = w.map imgLetK
  | [] => rfl
  | z :: w => by
    change imgLetK z :: imgWordK w = _
    rw [imgWordK_eq w]
    rfl

theorem mkImgK_eq : ∀ (ws : List (List Int)) (k : Nat),
    mkImgK ws k = (List.range ws.length).map fun i =>
      (k + i + 2, false) :: (ws.getD i []).map imgLetK
  | [], _ => rfl
  | w :: ws, k => by
    change ((Nat.add k 2, false) :: imgWordK w) :: mkImgK ws (k + 1) = _
    rw [mkImgK_eq ws (k + 1), imgWordK_eq, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, List.getD_cons_succ]
    congr 2
    omega

theorem codeWordK_eq : ∀ w : List Nat, codeWordK w = w.map codeLetK
  | [] => rfl
  | c :: w => by
    change codeLetK c :: codeWordK w = _
    rw [codeWordK_eq w]
    rfl

theorem mkCodesK_eq : ∀ rs : List (List Nat), mkCodesK rs = rs.map fun r => r.map codeLetK
  | [] => rfl
  | r :: rs => by
    change codeWordK r :: mkCodesK rs = _
    rw [mkCodesK_eq rs, codeWordK_eq]
    rfl

theorem natWordK_eq : ∀ w : List (Nat × Bool), natWordK w = w.map natLetK
  | [] => rfl
  | l :: w => by
    change natLetK l :: natWordK w = _
    rw [natWordK_eq w]
    rfl

theorem mkNatK_eq : ∀ rs : List (List (Nat × Bool)), mkNatK rs = rs.map fun r => r.map natLetK
  | [] => rfl
  | r :: rs => by
    change natWordK r :: mkNatK rs = _
    rw [mkNatK_eq rs, natWordK_eq]
    rfl

theorem relsAll_of_forall {RB : Nat → Nat} {mul : Nat → Nat → Nat}
    {rels : List (List (Nat × Bool))} {L ONE : Nat} :
    ∀ {k : Nat}, (∀ j < k, relOK RB mul rels L ONE j = true) → relsAll RB mul rels L ONE 0 k = true
  | 0, _ => rfl
  | k + 1, h => by
    change andB (relsAll RB mul rels L ONE 0 k) (relOK RB mul rels L ONE (0 + k)) = true
    rw [andB_eq_true, Nat.zero_add]
    exact ⟨relsAll_of_forall fun j hj => h j (by omega), h k (by omega)⟩

theorem sgnWordK_eq : ∀ w : List Int, sgnWordK w = w.map sgnLetK
  | [] => rfl
  | z :: w => by
    change sgnLetK z :: sgnWordK w = _
    rw [sgnWordK_eq w]
    rfl

theorem mkSurjK_eq : ∀ (ws : List (List Int)) (k : Nat),
    mkSurjK ws k = (List.range ws.length).map fun i => (ws.getD i []).map sgnLetK ++ [(k + i, false)]
  | [], _ => rfl
  | w :: ws, k => by
    change appK (sgnWordK w) [(k, false)] :: mkSurjK ws (k + 1) = _
    rw [mkSurjK_eq ws (k + 1), appK_eq, sgnWordK_eq, List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, List.getD_cons_succ]
    congr 3
    omega

theorem finWordK_eq : ∀ w : List (Fin 7 × Bool), finWordK w = w.map finLetK
  | [] => rfl
  | l :: w => by
    change finLetK l :: finWordK w = _
    rw [finWordK_eq w]
    rfl

theorem finInvK_eq : ∀ (w : List (Fin 7 × Bool)) (acc : List (Nat × Bool)),
    finInvK w acc = ((w.map finLetK).map fun x => (x.1, !x.2)).reverse ++ acc
  | [], _ => rfl
  | l :: w, acc => by
    change finInvK w ((Prod.rec (motive := fun _ => Nat × Bool) (fun g s => (g, notB s))
      (finLetK l)) :: acc) = _
    rw [finInvK_eq w]
    obtain ⟨i, s⟩ := l
    cases s <;> simp [finLetK, notB]

theorem pairRelK_eq (p : List (Fin 7 × Bool) × List (Fin 7 × Bool)) :
    pairRelK p = p.1.map finLetK ++ ((p.2.map finLetK).map fun x => (x.1, !x.2)).reverse := by
  obtain ⟨u, v⟩ := p
  change appK (finWordK u) (finInvK v []) = _
  rw [appK_eq, finWordK_eq, finInvK_eq, List.append_nil]

theorem consNe_eq (r : List (Nat × Bool)) (rs : List (List (Nat × Bool))) :
    consNe r rs = if r = [] then rs else r :: rs := by
  cases r <;> rfl

theorem mem_mkPairsK : ∀ {P : List (List (Fin 7 × Bool) × List (Fin 7 × Bool))} {p}, p ∈ P →
    pairRelK p ≠ [] → pairRelK p ∈ mkPairsK P
  | q :: P, p, hp, hne => by
    change pairRelK p ∈ consNe (pairRelK q) (mkPairsK P)
    rw [consNe_eq]
    rcases List.mem_cons.1 hp with rfl | hp
    · simp only [hne, ↓reduceIte]
      exact List.mem_cons_self
    · have := mem_mkPairsK hp hne
      by_cases hq : pairRelK q = []
      · simp only [hq, ↓reduceIte]
        exact this
      · simp only [hq, ↓reduceIte]
        exact List.mem_cons_of_mem _ this

theorem mkPairsAllK_eq : ∀ P : List (List (Fin 7 × Bool) × List (Fin 7 × Bool)),
    mkPairsAllK P = P.map pairRelK
  | [] => rfl
  | p :: P => by
    change pairRelK p :: mkPairsAllK P = _
    rw [mkPairsAllK_eq P]
    rfl

theorem mkNeK_eq : ∀ (ws : List (List (Fin 7 × Bool))) (k : Nat),
    mkNeK ws k = (List.range ws.length).map fun i => (ws.getD i []).map finLetK ++ [(k + i, false)]
  | [], _ => rfl
  | w :: ws, k => by
    change appK (finWordK w) [(k, false)] :: mkNeK ws (k + 1) = _
    rw [mkNeK_eq ws (k + 1), appK_eq, finWordK_eq, List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, List.getD_cons_succ]
    congr 3
    omega

theorem imgLetK_of_ne {z : Int} (h : imgLetK z ≠ badLet) :
    0 ≤ z ∧ z.toNat < 4 ∧ imgLetK z = (z.toNat / 2, Nat.beq (z.toNat % 2) 0) := by
  rcases z with n | n
  · have e : imgLetK (Int.ofNat n) = Bool.rec (motive := fun _ => Nat × Bool) badLet
        (Nat.div n 2, Nat.beq (Nat.mod n 2) 0) (Nat.blt n 4) := rfl
    by_cases hn : n < 4
    · rw [e, blt_true hn]
      exact ⟨Int.natCast_nonneg n, by simpa using hn, rfl⟩
    · rw [e, blt_false hn] at h
      exact absurd rfl h
  · exact absurd rfl h

theorem codeLetK_of_ne {c : Nat} (h : codeLetK c ≠ badLet) :
    c < 14 ∧ codeLetK c = (c / 2 + 2, Nat.beq (c % 2) 0) := by
  have e : codeLetK c = Bool.rec (motive := fun _ => Nat × Bool) badLet
      (Nat.add (Nat.div c 2) 2, Nat.beq (Nat.mod c 2) 0) (Nat.blt c 14) := rfl
  by_cases hc : c < 14
  · rw [e, blt_true hc]
    exact ⟨hc, rfl⟩
  · rw [e, blt_false hc] at h
    exact absurd rfl h

theorem natLetK_of_ne {l : Nat × Bool} (h : natLetK l ≠ badLet) :
    l.1 < 7 ∧ natLetK l = (l.1 + 2, l.2) := by
  obtain ⟨k, s⟩ := l
  have e : natLetK (k, s) = Bool.rec (motive := fun _ => Nat × Bool) badLet
      (Nat.add k 2, s) (Nat.blt k 7) := rfl
  by_cases hk : k < 7
  · rw [e, blt_true hk]
    exact ⟨hk, rfl⟩
  · rw [e, blt_false hk] at h
    exact absurd rfl h

theorem sgnLetK_of_ne {z : Int} (h : sgnLetK z ≠ badLet) :
    z ≠ 0 ∧ z.natAbs ≤ 7 ∧
      sgnLetK z = if 0 < z then ((z - 1).toNat + 2, true) else ((-z - 1).toNat + 2, false) := by
  rcases z with n | n
  · have e : sgnLetK (Int.ofNat n) = Bool.rec (motive := fun _ => Nat × Bool) badLet
        (Nat.succ n, true) (andB (Nat.blt 0 n) (Nat.blt n 8)) := rfl
    by_cases hn : 0 < n ∧ n < 8
    · rw [e, blt_true hn.1, blt_true hn.2]
      have hp : (0 : Int) < Int.ofNat n := by simpa using hn.1
      refine ⟨by simp; omega, by simp; omega, ?_⟩
      simp only [hp, ↓reduceIte]
      change (n + 1, true) = _
      congr 1
      simp only [Int.ofNat_eq_natCast]
      omega
    · have hb : andB (Nat.blt 0 n) (Nat.blt n 8) = false := by
        by_cases h1 : 0 < n
        · rw [blt_true h1, blt_false (by omega)]
          rfl
        · rw [blt_false h1]
          rfl
      rw [e, hb] at h
      exact absurd rfl h
  · have e : sgnLetK (Int.negSucc n) = Bool.rec (motive := fun _ => Nat × Bool) badLet
        (Nat.add n 2, false) (Nat.blt n 7) := rfl
    by_cases hn : n < 7
    · rw [e, blt_true hn]
      refine ⟨Int.negSucc_ne_zero n, by simp; omega, ?_⟩
      have hp : ¬ (0 : Int) < Int.negSucc n := by simp
      simp only [hp, ↓reduceIte]
      change (n + 2, false) = _
      congr 1
      simp [Int.neg_negSucc]
    · rw [e, blt_false hn] at h
      exact absurd rfl h

end CFSG.KC.GMSW

end
