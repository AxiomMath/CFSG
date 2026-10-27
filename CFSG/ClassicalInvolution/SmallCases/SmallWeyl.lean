module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.ClassicalInvolution.SmallWeyl

@[expose] def parity (n : ℕ) : Bool :=
  let a := n ^^^ (n >>> 4)
  let b := a ^^^ (a >>> 2)
  (b ^^^ (b >>> 1)) % 2 == 1

@[expose] def pairC (f v : ℕ) : Bool := parity (f &&& v)

@[expose] def addC (a b : ℕ × ℕ) : ℕ × ℕ := (a.1 ^^^ b.1, a.2 ^^^ b.2)

@[expose] def adjC (a b : ℕ × ℕ) : Bool := pairC a.2 b.1 && pairC b.2 a.1

@[expose] def validC (d : ℕ) (a : ℕ × ℕ) : Bool :=
  decide (0 < a.1 ∧ a.1 < 2 ^ d ∧ 0 < a.2 ∧ a.2 < 2 ^ d) && !pairC a.2 a.1

@[expose] def allC (d : ℕ) : List (ℕ × ℕ) :=
  ((List.range (2 ^ d)).flatMap fun v => (List.range (2 ^ d)).map fun f => (v, f)).filter
    (validC d)

@[expose] def memC (x : ℕ × ℕ) : List (ℕ × ℕ) → Bool
  | [] => false
  | y :: l => (x.1 == y.1 && x.2 == y.2) || memC x l

@[expose] def grow : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, _, T => T
  | _ + 1, [], T => T
  | k + 1, x :: W, T =>
    if memC x T then grow k W T
    else if T.all (fun y => pairC x.2 y.1 == pairC y.2 x.1) then
      grow k (((T.filter fun y => adjC x y).map (addC x)) ++ W) (x :: T)
    else x :: T

@[expose] def eqL (S T : List (ℕ × ℕ)) : Bool :=
  S.all (fun x => memC x T) && T.all (fun x => memC x S)

@[expose] def symL (S : List (ℕ × ℕ)) : Bool :=
  S.all fun a => S.all fun b => pairC a.2 b.1 == pairC b.2 a.1

@[expose] def stepOK (d fuel : ℕ) (𝓛 : List (List (ℕ × ℕ))) (S : List (ℕ × ℕ)) : Bool :=
  (allC d).all fun q => memC q S || !(S.any fun s => adjC s q) ||
    (let T := grow fuel [q] S; !(symL T) || 𝓛.any (eqL T))

@[expose] def familyOK (d fuel : ℕ) (𝓛 : List (List (ℕ × ℕ))) : Bool :=
  𝓛.all (stepOK d fuel 𝓛)

@[expose] def seedsOK (d : ℕ) (𝓛 : List (List (ℕ × ℕ))) : Bool :=
  (allC d).all fun p => 𝓛.any (eqL [p])

@[expose] def valency (S : List (ℕ × ℕ)) (p : ℕ × ℕ) : ℕ :=
  (S.filter fun q => q != p && !adjC p q).length

@[expose] def tableOK (tab : List (ℕ × ℕ)) (𝓛 : List (List (ℕ × ℕ))) : Bool :=
  𝓛.all fun S => decide S.Nodup && tab.any fun e =>
    S.length == e.1 && S.all fun p => valency S p == e.2

theorem adjC_comm (a b : ℕ × ℕ) : adjC a b = adjC b a := by
  simp only [adjC, Bool.and_comm]

theorem mem_memC {x : ℕ × ℕ} {l : List (ℕ × ℕ)} : memC x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memC]
  | cons y l ih =>
    obtain ⟨a, b⟩ := x
    obtain ⟨c, e⟩ := y
    simp [memC, ih, Prod.ext_iff]

theorem mem_allC {d : ℕ} {x : ℕ × ℕ} : x ∈ allC d ↔ validC d x = true := by
  obtain ⟨v, f⟩ := x
  simp only [allC, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨⟨v, ?_, f, ?_, rfl, rfl⟩, h⟩ <;>
      · simp only [validC, Bool.and_eq_true, decide_eq_true_eq] at h
        omega

theorem mem_grow_of_mem {x : ℕ × ℕ} :
    ∀ (k : ℕ) (W T : List (ℕ × ℕ)), x ∈ T → x ∈ grow k W T
  | 0, W, T, h => by simpa [grow] using h
  | k + 1, [], T, h => by simpa [grow] using h
  | k + 1, y :: W, T, h => by
    rw [grow]
    split_ifs
    · exact mem_grow_of_mem k W T h
    · exact mem_grow_of_mem k _ _ (List.mem_cons_of_mem _ h)
    · exact List.mem_cons_of_mem _ h

theorem mem_grow_head {k : ℕ} (hk : 0 < k) {q : ℕ × ℕ} {S : List (ℕ × ℕ)} (hq : q ∉ S) :
    q ∈ grow k [q] S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hq' : memC q S = false := by
    by_contra h
    exact hq (mem_memC.mp (by simpa using h))
  rw [grow]
  by_cases hs : (S.all fun y => pairC q.2 y.1 == pairC y.2 q.1) = true
  · simp only [hq', Bool.false_eq_true, ↓reduceIte, hs]
    exact mem_grow_of_mem k _ _ (List.mem_cons_self ..)
  · simp only [hq', Bool.false_eq_true, ↓reduceIte, hs]
    exact List.mem_cons_self ..

theorem mem_of_mem_grow {P : ℕ × ℕ → Prop}
    (hP : ∀ a b, P a → P b → adjC a b = true → P (addC a b)) :
    ∀ (k : ℕ) (W T : List (ℕ × ℕ)), (∀ x ∈ W, P x) → (∀ x ∈ T, P x) →
      ∀ x ∈ grow k W T, P x
  | 0, W, T, _, hT => by simpa [grow] using hT
  | k + 1, [], T, _, hT => by simpa [grow] using hT
  | k + 1, y :: W, T, hW, hT => by
    rw [grow]
    split_ifs
    · exact mem_of_mem_grow hP k W T (fun x hx => hW x (List.mem_cons_of_mem _ hx)) hT
    · refine mem_of_mem_grow hP k _ _ ?_ ?_
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
          obtain ⟨hzT, hadj⟩ := List.mem_filter.mp hz
          exact hP y z (hW y (List.mem_cons_self ..)) (hT z hzT) hadj
        · exact hW x (List.mem_cons_of_mem _ hx)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hW _ (List.mem_cons_self ..)
        · exact hT x hx
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hW _ (List.mem_cons_self ..)
      · exact hT x hx

theorem exists_crossing {R : Finset (ℕ × ℕ)}
    (hconn : ∀ a ∈ R, ∀ b ∈ R,
      Relation.ReflTransGen (fun x y => x ∈ R ∧ y ∈ R ∧ adjC x y = true) a b)
    {S : List (ℕ × ℕ)} (hSR : ∀ x ∈ S, x ∈ R) (hS : S ≠ []) {b : ℕ × ℕ} (hb : b ∈ R)
    (hbS : b ∉ S) : ∃ s ∈ S, ∃ q ∈ R, q ∉ S ∧ adjC s q = true := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil S hS
  have key : ∀ c, Relation.ReflTransGen (fun x y => x ∈ R ∧ y ∈ R ∧ adjC x y = true) a c →
      c ∉ S → ∃ s ∈ S, ∃ q ∈ R, q ∉ S ∧ adjC s q = true := by
    intro c hc
    induction hc with
    | refl => exact fun h => absurd ha h
    | @tail c' c _ hstep ih =>
      intro hcS
      by_cases hc'S : c' ∈ S
      · exact ⟨c', hc'S, c, hstep.2.1, hcS, hstep.2.2⟩
      · exact ih hc'S
  exact key b (hconn a (hSR a ha) b hb) hbS

theorem exists_mem_family {d fuel : ℕ} (hfuel : 0 < fuel)
    {𝓛 : List (List (ℕ × ℕ))} (h : familyOK d fuel 𝓛 = true)
    (R : Finset (ℕ × ℕ)) (hvalid : ∀ x ∈ R, validC d x = true)
    (hclosed : ∀ a ∈ R, ∀ b ∈ R, adjC a b = true → addC a b ∈ R)
    (hsym : ∀ a ∈ R, ∀ b ∈ R, pairC a.2 b.1 = pairC b.2 a.1)
    (hconn : ∀ a ∈ R, ∀ b ∈ R,
      Relation.ReflTransGen (fun x y => x ∈ R ∧ y ∈ R ∧ adjC x y = true) a b)
    (hseed : ∃ S₀ ∈ 𝓛, S₀ ≠ [] ∧ ∀ x ∈ S₀, x ∈ R) : ∃ S ∈ 𝓛, ∀ x, x ∈ S ↔ x ∈ R := by
  simp only [familyOK, List.all_eq_true] at h
  have hstep := h
  have key : ∀ n : ℕ, ∀ S ∈ 𝓛, (∀ x ∈ S, x ∈ R) → S ≠ [] → R.card ≤ S.toFinset.card + n →
      ∃ S ∈ 𝓛, ∀ x, x ∈ S ↔ x ∈ R := by
    intro n
    induction n with
    | zero =>
      intro S hS hSR _ hcard
      refine ⟨S, hS, fun x => ⟨fun hx => hSR x hx, fun hx => ?_⟩⟩
      have hsub : S.toFinset ⊆ R := fun y hy => hSR y (List.mem_toFinset.mp hy)
      have := Finset.eq_of_subset_of_card_le hsub (by simpa using hcard)
      rw [← List.mem_toFinset, this]
      exact hx
    | succ n ih =>
      intro S hS hSR hne hcard
      by_cases hall : ∀ x ∈ R, x ∈ S
      · exact ⟨S, hS, fun x => ⟨fun hx => hSR x hx, fun hx => hall x hx⟩⟩
      push Not at hall
      obtain ⟨b, hbR, hbS⟩ := hall
      obtain ⟨s, hs, q, hqR, hqS, hadj⟩ := exists_crossing hconn hSR hne hbR hbS
      have hstepS := hstep S hS
      simp only [stepOK, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', mem_memC,
        List.any_eq_true] at hstepS
      have hq := hstepS q (mem_allC.mpr (hvalid q hqR))
      rcases hq with (hq | hq) | hq
      · exact absurd hq hqS
      · exfalso
        have : (S.any fun s => adjC s q) = true :=
          List.any_eq_true.mpr ⟨s, hs, hadj⟩
        simp [this] at hq
      · set T := grow fuel [q] S with hT
        have hTR : ∀ x ∈ T, x ∈ R := by
          refine mem_of_mem_grow (P := (· ∈ R)) (fun a b ha hb hab => hclosed a ha b hb hab)
            fuel [q] S ?_ hSR
          intro x hx
          rw [List.mem_singleton.mp hx]
          exact hqR
        have hsymT : symL T = true := by
          simp only [symL, List.all_eq_true, beq_iff_eq]
          exact fun a ha b hb => hsym a (hTR a ha) b (hTR b hb)
        obtain ⟨S', hS', hTS'⟩ : ∃ S' ∈ 𝓛, eqL T S' = true := by
          rcases hq with hq | hq
          · exact absurd (hsymT.symm.trans hq) (by decide)
          · exact hq
        have hTS'' : ∀ x, x ∈ T ↔ x ∈ S' := by
          simp only [eqL, Bool.and_eq_true, List.all_eq_true, mem_memC] at hTS'
          exact fun x => ⟨hTS'.1 x, hTS'.2 x⟩
        have hqT : q ∈ T := mem_grow_head hfuel hqS
        have hS'R : ∀ x ∈ S', x ∈ R := fun x hx => hTR x ((hTS'' x).mpr hx)
        have hS'ne : S' ≠ [] := List.ne_nil_of_mem ((hTS'' q).mp hqT)
        have hsub : S.toFinset ⊂ S'.toFinset := by
          refine Finset.ssubset_iff_of_subset (fun x hx => ?_) |>.mpr ⟨q, ?_, ?_⟩
          · exact List.mem_toFinset.mpr ((hTS'' x).mp (mem_grow_of_mem _ _ _
              (List.mem_toFinset.mp hx)))
          · exact List.mem_toFinset.mpr ((hTS'' q).mp hqT)
          · exact fun hh => hqS (List.mem_toFinset.mp hh)
        have := Finset.card_lt_card hsub
        exact ih S' hS' hS'R hS'ne (by omega)
  obtain ⟨S₀, hS₀, hS₀ne, hS₀R⟩ := hseed
  exact key R.card S₀ hS₀ hS₀R hS₀ne (by omega)

structure CodedSet (d : ℕ) (R : Finset (ℕ × ℕ)) : Prop where
  valid : ∀ x ∈ R, validC d x = true
  closed : ∀ a ∈ R, ∀ b ∈ R, adjC a b = true → addC a b ∈ R
  sym : ∀ a ∈ R, ∀ b ∈ R, pairC a.2 b.1 = pairC b.2 a.1
  conn : ∀ a ∈ R, ∀ b ∈ R,
    Relation.ReflTransGen (fun x y => x ∈ R ∧ y ∈ R ∧ adjC x y = true) a b

@[expose] def GoodSet (tab : List (ℕ × ℕ)) (R : Finset (ℕ × ℕ)) : Prop :=
  ∃ e ∈ tab, R.card = e.1 ∧ ∀ p ∈ R, (R.filter fun q => q ≠ p ∧ adjC p q = false).card = e.2

theorem classification_of_family {d fuel : ℕ} (hfuel : 0 < fuel) {𝓛 : List (List (ℕ × ℕ))}
    {tab : List (ℕ × ℕ)} (hfam : familyOK d fuel 𝓛 = true) (htab : tableOK tab 𝓛 = true)
    {R : Finset (ℕ × ℕ)} (hR : CodedSet d R) (hseed : ∃ S₀ ∈ 𝓛, S₀ ≠ [] ∧ ∀ x ∈ S₀, x ∈ R) :
    GoodSet tab R := by
  obtain ⟨S, hS, hSR⟩ :=
    exists_mem_family hfuel hfam R hR.valid hR.closed hR.sym hR.conn hseed
  simp only [tableOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true] at htab
  obtain ⟨hnd, e, he, hlen, hval⟩ := htab S hS
  have hRS : R = S.toFinset := Finset.ext fun x => by rw [List.mem_toFinset, hSR]
  simp only [beq_iff_eq] at hlen hval
  refine ⟨e, he, ?_, fun p hp => ?_⟩
  · rw [hRS, List.toFinset_card_of_nodup hnd, hlen]
  · have hfilt : R.filter (fun q => q ≠ p ∧ adjC p q = false) =
        (S.filter fun q => q != p && !adjC p q).toFinset := by
      ext q
      simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter, hSR, Bool.and_eq_true,
        bne_iff_ne, ne_eq, Bool.not_eq_true']
    rw [hfilt, List.toFinset_card_of_nodup (hnd.filter _)]
    simpa only [valency, beq_iff_eq] using hval p ((hSR p).mpr hp)

theorem classification_of_cert {d fuel : ℕ} (hfuel : 0 < fuel) {𝓛 : List (List (ℕ × ℕ))}
    {tab : List (ℕ × ℕ)} (hfam : familyOK d fuel 𝓛 = true) (hseeds : seedsOK d 𝓛 = true)
    (htab : tableOK tab 𝓛 = true) {R : Finset (ℕ × ℕ)} (hne : R.Nonempty)
    (hR : CodedSet d R) : GoodSet tab R := by
  obtain ⟨p₀, hp₀⟩ := hne
  refine classification_of_family hfuel hfam htab hR ?_
  simp only [seedsOK, List.all_eq_true, List.any_eq_true] at hseeds
  obtain ⟨S₀, hS₀, hS₀p⟩ := hseeds p₀ (mem_allC.mpr (hR.valid p₀ hp₀))
  simp only [eqL, Bool.and_eq_true, List.all_eq_true, mem_memC] at hS₀p
  refine ⟨S₀, hS₀, List.ne_nil_of_mem (hS₀p.1 p₀ (List.mem_singleton_self _)), fun x hx => ?_⟩
  rw [List.mem_singleton.mp (hS₀p.2 x hx)]
  exact hp₀

section Datum

structure Datum (A : Type*) [AddCommGroup A] where
  vec : A
  form : A →+ ZMod 2
  vec_ne_zero : vec ≠ 0
  form_ne_zero : form ≠ 0
  form_vec : form vec = 0

variable {A : Type*} [AddCommGroup A]

namespace Datum

@[ext] theorem ext {p q : Datum A} (hv : p.vec = q.vec) (hf : p.form = q.form) : p = q := by
  cases p
  cases q
  simp_all

@[expose] def pair (p q : Datum A) : ZMod 2 := p.form q.vec

@[expose] def Adj (p q : Datum A) : Prop := p.pair q = 1 ∧ q.pair p = 1

theorem Adj.symm {p q : Datum A} (h : p.Adj q) : q.Adj p := ⟨h.2, h.1⟩

theorem pair_self (p : Datum A) : p.pair p = 0 := p.form_vec

private theorem zmod_two_eq_zero_of_ne_one : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide

@[expose] def conj (p q : Datum A) : Datum A where
  vec := q.vec + (if p.pair q = 1 then p.vec else 0)
  form := q.form + (if q.pair p = 1 then p.form else 0)
  vec_ne_zero := by
    intro h
    by_cases hc : p.pair q = 1
    · simp only [hc, ↓reduceIte] at h
      have h1 := congrArg p.form h
      rw [map_add, p.form_vec, add_zero, map_zero] at h1
      exact one_ne_zero (hc.symm.trans h1)
    · simp only [hc, ↓reduceIte, add_zero] at h
      exact q.vec_ne_zero h
  form_ne_zero := by
    intro h
    by_cases hc : q.pair p = 1
    · simp only [hc, ↓reduceIte] at h
      have h1 := congrArg (fun f : A →+ ZMod 2 => f p.vec) h
      simp only [AddMonoidHom.add_apply, p.form_vec, add_zero, AddMonoidHom.zero_apply] at h1
      exact one_ne_zero (hc.symm.trans h1)
    · simp only [hc, ↓reduceIte, add_zero] at h
      exact q.form_ne_zero h
  form_vec := by
    have hq := q.form_vec
    have hpp := p.form_vec
    by_cases ha : p.pair q = 1 <;> by_cases hb : q.pair p = 1 <;>
      simp only [ha, hb, ↓reduceIte, add_zero, map_add, AddMonoidHom.add_apply, hq, hpp, zero_add]
    · have h1 : q.form p.vec = 1 := hb
      have h2 : p.form q.vec = 1 := ha
      rw [h1, h2]
      decide
    · have h1 : q.form p.vec = 0 := zmod_two_eq_zero_of_ne_one _ hb
      exact h1
    · have h2 : p.form q.vec = 0 := zmod_two_eq_zero_of_ne_one _ ha
      exact h2

end Datum

@[expose] def IsSymm (R : Finset (Datum A)) : Prop := ∀ p ∈ R, ∀ q ∈ R, p.pair q = q.pair p

@[expose] def IsClosed (R : Finset (Datum A)) : Prop := ∀ p ∈ R, ∀ q ∈ R, p.conj q ∈ R

@[expose] def IsConn (R : Finset (Datum A)) : Prop :=
  ∀ p ∈ R, ∀ q ∈ R, Relation.ReflTransGen (fun a b => a ∈ R ∧ b ∈ R ∧ a.Adj b) p q

end Datum

section Coding

open Matrix

def enc {d : ℕ} (x : Fin d → ZMod 2) : ℕ := ∑ i : Fin d, (x i).val * 2 ^ (i : ℕ)

structure EncOK (d : ℕ) : Prop where
  lt : ∀ x : Fin d → ZMod 2, enc x < 2 ^ d
  inj : ∀ x y : Fin d → ZMod 2, enc x = enc y → x = y
  add : ∀ x y : Fin d → ZMod 2, enc (x + y) = enc x ^^^ enc y
  pair : ∀ c x : Fin d → ZMod 2, pairC (enc c) (enc x) = decide (c ⬝ᵥ x = 1)

theorem encOK_two : EncOK 2 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem encOK_three : EncOK 3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem encOK_four : EncOK 4 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem enc_zero (d : ℕ) : enc (0 : Fin d → ZMod 2) = 0 := by simp [enc]


variable {A : Type*} [AddCommGroup A]

def coord {d : ℕ} (e : A ≃+ (Fin d → ZMod 2)) (f : A →+ ZMod 2) : Fin d → ZMod 2 :=
  fun i => f (e.symm (Pi.single i 1))

theorem coord_add {d : ℕ} (e : A ≃+ (Fin d → ZMod 2)) (f g : A →+ ZMod 2) :
    coord e (f + g) = coord e f + coord e g := by
  ext i
  simp [coord]

theorem form_apply {d : ℕ} (e : A ≃+ (Fin d → ZMod 2)) (f : A →+ ZMod 2) (x : A) :
    f x = coord e f ⬝ᵥ e x := by
  have hx : x = e.symm (∑ i : Fin d, Pi.single i (e x i)) := by
    rw [Finset.univ_sum_single, AddEquiv.symm_apply_apply]
  have hsingle : ∀ i : Fin d,
      (Pi.single i (e x i) : Fin d → ZMod 2) = (e x i).val • Pi.single i 1 := by
    intro i
    ext j
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  conv_lhs => rw [hx]
  rw [map_sum, map_sum, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsingle, map_nsmul, map_nsmul, nsmul_eq_mul, mul_comm]
  simp [coord]

theorem coord_ne_zero {d : ℕ} (e : A ≃+ (Fin d → ZMod 2)) {f : A →+ ZMod 2} (hf : f ≠ 0) :
    coord e f ≠ 0 := by
  intro h
  apply hf
  ext x
  rw [form_apply e f x, h]
  simp

def Datum.code {d : ℕ} (e : A ≃+ (Fin d → ZMod 2)) (p : Datum A) : ℕ × ℕ :=
  (enc (e p.vec), enc (coord e p.form))

section CodeLemmas

variable {d : ℕ} (hE : EncOK d) (e : A ≃+ (Fin d → ZMod 2))

include hE

theorem Datum.pairC_code (p q : Datum A) :
    pairC (p.code e).2 (q.code e).1 = decide (p.pair q = 1) := by
  rw [Datum.code, Datum.code, hE.pair, ← form_apply]
  rfl

theorem Datum.adjC_code (p q : Datum A) : adjC (p.code e) (q.code e) = true ↔ p.Adj q := by
  simp only [adjC, Bool.and_eq_true, Datum.pairC_code hE e, decide_eq_true_eq]
  rfl

theorem Datum.code_injective : Function.Injective (Datum.code (A := A) e) := by
  intro p q h
  simp only [Datum.code, Prod.mk.injEq] at h
  have hv : e p.vec = e q.vec := hE.inj _ _ h.1
  have hf : coord e p.form = coord e q.form := hE.inj _ _ h.2
  refine Datum.ext (e.injective hv) ?_
  ext x
  rw [form_apply e p.form, form_apply e q.form, hf]

theorem Datum.validC_code (p : Datum A) : validC d (p.code e) = true := by
  have h1 : e p.vec ≠ 0 := fun h => p.vec_ne_zero (e.injective (h.trans (map_zero e).symm))
  have h2 : coord e p.form ≠ 0 := coord_ne_zero e p.form_ne_zero
  have h1' : enc (e p.vec) ≠ 0 := fun h => h1 (hE.inj _ _ (h.trans (enc_zero d).symm))
  have h2' : enc (coord e p.form) ≠ 0 := fun h => h2 (hE.inj _ _ (h.trans (enc_zero d).symm))
  have h3 : pairC (p.code e).2 (p.code e).1 = false := by
    rw [Datum.pairC_code hE e]
    simp [Datum.pair_self]
  simp only [validC, Datum.code, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨decide_eq_true ⟨Nat.pos_of_ne_zero h1', hE.lt _, Nat.pos_of_ne_zero h2', hE.lt _⟩, ?_⟩
  simpa [Datum.code] using h3

theorem Datum.addC_code {p q : Datum A} (h : p.Adj q) :
    addC (p.code e) (q.code e) = (p.conj q).code e := by
  simp only [addC, Datum.code, Datum.conj, h.1, h.2, ↓reduceIte, Prod.mk.injEq]
  constructor
  · rw [← hE.add, ← map_add, add_comm]
  · rw [← hE.add, ← coord_add, add_comm]

end CodeLemmas


section Bridge

variable {d : ℕ}

theorem classification_of_datum (hE : EncOK d) {tab : List (ℕ × ℕ)}
    (hgood : ∀ R : Finset (ℕ × ℕ), R.Nonempty → CodedSet d R → GoodSet tab R)
    (e : A ≃+ (Fin d → ZMod 2)) (R : Finset (Datum A)) (hne : R.Nonempty) (hs : IsSymm R)
    (hc : IsClosed R) (hconn : IsConn R) :
    ∃ x ∈ tab, R.card = x.1 ∧
      ∀ p ∈ R, Set.ncard {q | q ∈ R ∧ q ≠ p ∧ ¬ p.Adj q} = x.2 := by
  classical
  have hinj := Datum.code_injective hE e
  obtain ⟨x, hx, hcard, hval⟩ := hgood (R.image (Datum.code e)) (hne.image _)
    { valid := by
        intro a ha
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp ha
        exact Datum.validC_code hE e p
      closed := by
        intro a ha b hb hab
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
        rw [Datum.addC_code hE e ((Datum.adjC_code hE e p q).mp hab)]
        exact Finset.mem_image_of_mem _ (hc p hp q hq)
      sym := by
        intro a ha b hb
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
        rw [Datum.pairC_code hE e, Datum.pairC_code hE e, hs p hp q hq]
      conn := by
        intro a ha b hb
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
        refine (hconn p hp q hq).lift (Datum.code e) fun a b hab => ?_
        exact ⟨Finset.mem_image_of_mem _ hab.1, Finset.mem_image_of_mem _ hab.2.1,
          (Datum.adjC_code hE e a b).mpr hab.2.2⟩ }
  refine ⟨x, hx, ?_, fun p hp => ?_⟩
  · rw [← hcard, Finset.card_image_of_injective _ hinj]
  · have hset : {q | q ∈ R ∧ q ≠ p ∧ ¬ p.Adj q} =
        ↑(R.filter fun q => q ≠ p ∧ ¬ p.Adj q) := by
      ext q
      simp
    have hfilt : (R.image (Datum.code e)).filter
        (fun q => q ≠ p.code e ∧ adjC (p.code e) q = false) =
        (R.filter fun q => q ≠ p ∧ ¬ p.Adj q).image (Datum.code e) := by
      ext q'
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨q, hq, rfl⟩, hne', hadj⟩
        refine ⟨q, ⟨hq, fun h => hne' (h ▸ rfl), ?_⟩, rfl⟩
        rw [Bool.eq_false_iff] at hadj
        exact fun h => hadj ((Datum.adjC_code hE e p q).mpr h)
      · rintro ⟨q, ⟨hq, hne', hadj⟩, rfl⟩
        refine ⟨⟨q, hq, rfl⟩, fun h => hne' (hinj h), ?_⟩
        rw [Bool.eq_false_iff]
        exact fun h => hadj ((Datum.adjC_code hE e p q).mp h)
    rw [hset, Set.ncard_coe_finset, ← Finset.card_image_of_injective _ hinj, ← hfilt]
    exact hval _ (Finset.mem_image_of_mem _ hp)

end Bridge

end Coding

section Classification

variable {A : Type*} [AddCommGroup A]

theorem nonempty_addEquiv_of_card {d : ℕ} (h2 : ∀ x : A, x + x = 0)
    (hcard : Nat.card A = 2 ^ d) : Nonempty (A ≃+ (Fin d → ZMod 2)) := by
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  let _ : Module (ZMod 2) A :=
    AddCommGroup.zmodModule (n := 2) fun x => by rw [two_nsmul]; exact h2 x
  have : Module.Finite (ZMod 2) A := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 2) A = d := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A)
    rw [hcard, Nat.card_zmod] at this
    exact (Nat.pow_right_injective (le_refl 2) this).symm
  exact ⟨(Module.finBasisOfFinrankEq (ZMod 2) A hrank).equivFun.toAddEquiv⟩

theorem classification_of_card {d : ℕ} (hE : EncOK d) {tab : List (ℕ × ℕ)}
    (hgood : ∀ R : Finset (ℕ × ℕ), R.Nonempty → CodedSet d R → GoodSet tab R)
    (h2 : ∀ x : A, x + x = 0) (hcard : Nat.card A = 2 ^ d) (R : Finset (Datum A))
    (hne : R.Nonempty) (hs : IsSymm R) (hc : IsClosed R) (hconn : IsConn R) :
    ∃ x ∈ tab, R.card = x.1 ∧
      ∀ p ∈ R, Set.ncard {q | q ∈ R ∧ q ≠ p ∧ ¬ p.Adj q} = x.2 := by
  obtain ⟨e⟩ := nonempty_addEquiv_of_card h2 hcard
  exact classification_of_datum hE hgood e R hne hs hc hconn

theorem adj_of_ncard_eq_zero {R : Finset (Datum A)} {p : Datum A}
    (h : Set.ncard {q | q ∈ R ∧ q ≠ p ∧ ¬ p.Adj q} = 0) : ∀ q ∈ R, q ≠ p → p.Adj q := by
  intro q hq hqp
  by_contra hadj
  have hfin : {q | q ∈ R ∧ q ≠ p ∧ ¬ p.Adj q}.Finite := R.finite_toSet.subset fun x hx => hx.1
  have := (Set.ncard_eq_zero hfin).mp h
  exact (Set.eq_empty_iff_forall_notMem.mp this) q ⟨hq, hqp, hadj⟩

theorem existsUnique_of_ncard_eq_one {R : Finset (Datum A)} {p : Datum A}
    (h : Set.ncard {q | q ∈ R ∧ q ≠ p ∧ ¬ p.Adj q} = 1) :
    ∃! q, q ∈ R ∧ q ≠ p ∧ ¬ p.Adj q := by
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h
  refine ⟨a, ?_, fun q hq => ?_⟩
  · have : a ∈ ({a} : Set (Datum A)) := rfl
    rw [← ha] at this
    exact this
  · have : q ∈ {q | q ∈ R ∧ q ≠ p ∧ ¬ p.Adj q} := hq
    rw [ha] at this
    exact this

end Classification

section Families

private def fam2 : List (List (ℕ × ℕ)) := [
  [(1, 2)],
  [(2, 1)],
  [(3, 3)],
  [(1, 2), (2, 1), (3, 3)]
]

private def fam3 : List (List (ℕ × ℕ)) := [
  [(1, 2)],
  [(1, 4)],
  [(1, 6)],
  [(2, 1)],
  [(2, 4)],
  [(2, 5)],
  [(3, 3)],
  [(3, 4)],
  [(3, 7)],
  [(4, 1)],
  [(4, 2)],
  [(4, 3)],
  [(5, 2)],
  [(5, 5)],
  [(5, 7)],
  [(6, 1)],
  [(6, 6)],
  [(6, 7)],
  [(7, 3)],
  [(7, 5)],
  [(7, 6)],
  [(1, 2), (2, 1), (3, 3)],
  [(1, 2), (2, 5), (3, 7)],
  [(1, 2), (6, 1), (7, 3)],
  [(1, 2), (6, 7), (7, 5)],
  [(1, 4), (4, 1), (5, 5)],
  [(1, 4), (4, 3), (5, 7)],
  [(1, 4), (6, 1), (7, 5)],
  [(1, 4), (6, 7), (7, 3)],
  [(1, 6), (2, 1), (3, 7)],
  [(1, 6), (2, 5), (3, 3)],
  [(1, 6), (4, 1), (5, 7)],
  [(1, 6), (4, 3), (5, 5)],
  [(2, 1), (5, 2), (7, 3)],
  [(2, 1), (5, 7), (7, 6)],
  [(2, 4), (4, 2), (6, 6)],
  [(2, 4), (4, 3), (6, 7)],
  [(2, 4), (5, 2), (7, 6)],
  [(2, 4), (5, 7), (7, 3)],
  [(2, 5), (4, 2), (6, 7)],
  [(2, 5), (4, 3), (6, 6)],
  [(3, 3), (5, 2), (6, 1)],
  [(3, 3), (5, 5), (6, 6)],
  [(3, 4), (4, 1), (7, 5)],
  [(3, 4), (4, 2), (7, 6)],
  [(3, 4), (5, 2), (6, 6)],
  [(3, 4), (5, 5), (6, 1)],
  [(3, 7), (4, 1), (7, 6)],
  [(3, 7), (4, 2), (7, 5)],
  [(1, 2), (1, 4), (6, 1), (6, 7), (7, 3), (7, 5)],
  [(1, 2), (1, 6), (2, 1), (2, 5), (3, 3), (3, 7)],
  [(1, 2), (2, 1), (3, 3), (5, 2), (6, 1), (7, 3)],
  [(1, 2), (2, 5), (3, 7), (4, 2), (6, 7), (7, 5)],
  [(1, 4), (1, 6), (4, 1), (4, 3), (5, 5), (5, 7)],
  [(1, 4), (2, 4), (4, 3), (5, 7), (6, 7), (7, 3)],
  [(1, 4), (3, 4), (4, 1), (5, 5), (6, 1), (7, 5)],
  [(1, 6), (2, 1), (3, 7), (4, 1), (5, 7), (7, 6)],
  [(1, 6), (2, 5), (3, 3), (4, 3), (5, 5), (6, 6)],
  [(2, 1), (2, 4), (5, 2), (5, 7), (7, 3), (7, 6)],
  [(2, 4), (2, 5), (4, 2), (4, 3), (6, 6), (6, 7)],
  [(2, 4), (3, 4), (4, 2), (5, 2), (6, 6), (7, 6)],
  [(3, 3), (3, 4), (5, 2), (5, 5), (6, 1), (6, 6)],
  [(3, 4), (3, 7), (4, 1), (4, 2), (7, 5), (7, 6)]
]

private theorem familyOK_two : familyOK 2 30 fam2 = true := by decide +kernel

private theorem seedsOK_two : seedsOK 2 fam2 = true := by decide +kernel

private theorem tableOK_two : tableOK [(1, 0), (3, 0)] fam2 = true := by decide +kernel

private theorem familyOK_three : familyOK 3 30 fam3 = true := by decide +kernel

private theorem seedsOK_three : seedsOK 3 fam3 = true := by decide +kernel

private theorem tableOK_three : tableOK [(1, 0), (3, 0), (6, 1)] fam3 = true := by
  decide +kernel

theorem goodSet_two {R : Finset (ℕ × ℕ)} (hne : R.Nonempty) (hR : CodedSet 2 R) :
    GoodSet [(1, 0), (3, 0)] R :=
  classification_of_cert (by norm_num) familyOK_two seedsOK_two tableOK_two hne hR

theorem goodSet_three {R : Finset (ℕ × ℕ)} (hne : R.Nonempty) (hR : CodedSet 3 R) :
    GoodSet [(1, 0), (3, 0), (6, 1)] R :=
  classification_of_cert (by norm_num) familyOK_three seedsOK_three tableOK_three hne hR

end Families

section Dimensions

variable {A : Type*} [AddCommGroup A]

theorem rootSet_classification_two (h2 : ∀ x : A, x + x = 0) (hcard : Nat.card A = 4)
    (R : Finset (Datum A)) (hne : R.Nonempty) (hs : IsSymm R) (hc : IsClosed R)
    (hconn : IsConn R) :
    R.card = 1 ∨ (R.card = 3 ∧ ∀ p ∈ R, ∀ q ∈ R, p ≠ q → p.Adj q) := by
  obtain ⟨x, hx, hcd, hval⟩ := classification_of_card encOK_two
    (fun _ hne hR => goodSet_two hne hR) h2 (hcard.trans (by norm_num : 4 = 2 ^ 2)) R hne hs hc
    hconn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact Or.inl hcd
  · refine Or.inr ⟨hcd, fun p hp q hq hpq => ?_⟩
    exact adj_of_ncard_eq_zero (hval p hp) q hq (Ne.symm hpq)

theorem rootSet_classification_three (h2 : ∀ x : A, x + x = 0) (hcard : Nat.card A = 8)
    (R : Finset (Datum A)) (hne : R.Nonempty) (hs : IsSymm R) (hc : IsClosed R)
    (hconn : IsConn R) :
    R.card = 1 ∨ (R.card = 3 ∧ ∀ p ∈ R, ∀ q ∈ R, p ≠ q → p.Adj q) ∨
      (R.card = 6 ∧ ∀ p ∈ R, ∃! q, q ∈ R ∧ q ≠ p ∧ ¬ p.Adj q) := by
  obtain ⟨x, hx, hcd, hval⟩ := classification_of_card encOK_three
    (fun _ hne hR => goodSet_three hne hR) h2 (hcard.trans (by norm_num : 8 = 2 ^ 3)) R hne hs hc
    hconn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact Or.inl hcd
  · refine Or.inr (Or.inl ⟨hcd, fun p hp q hq hpq => ?_⟩)
    exact adj_of_ncard_eq_zero (hval p hp) q hq (Ne.symm hpq)
  · exact Or.inr (Or.inr ⟨hcd, fun p hp => existsUnique_of_ncard_eq_one (hval p hp)⟩)

end Dimensions

end CFSG.ClassicalInvolution.SmallWeyl
