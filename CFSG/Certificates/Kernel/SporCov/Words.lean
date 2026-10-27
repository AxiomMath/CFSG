module

public import Certificates.Data.Kernel.SporCov.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov

theorem chW_nil (L : ℕ → Bool) : chW L [] = true := rfl

theorem chW_cons (L : ℕ → Bool) (l : ℕ) (w : List ℕ) : chW L (l :: w) = (L l && chW L w) := rfl

theorem chW_append (L : ℕ → Bool) : ∀ u v : List ℕ, chW L (u ++ v) = (chW L u && chW L v)
  | [], v => by rw [List.nil_append, chW_nil, Bool.true_and]
  | l :: u, v => by rw [List.cons_append, chW_cons, chW_cons, chW_append L u v, Bool.and_assoc]

theorem chW_append_of {L : ℕ → Bool} {u v : List ℕ} (hu : chW L u = true) (hv : chW L v = true) :
    chW L (u ++ v) = true := by
  rw [chW_append, hu, hv, Bool.and_self]

theorem chA_iff (L : ℕ → Bool) : ∀ W : List (List ℕ), chA L W = true ↔ ∀ w ∈ W, chW L w = true
  | [] => by simp [chA]
  | w :: W => by
    change (chW L w && chA L W) = true ↔ _
    rw [Bool.and_eq_true, chA_iff L W, List.forall_mem_cons]

theorem lenLe_iff : ∀ (W : List (List ℕ)) (n : ℕ), lenLe W n = true ↔ W.length ≤ n
  | [], n => by simp [lenLe]
  | w :: W, 0 => by simp [lenLe]
  | w :: W, n + 1 => by
    change lenLe W n = true ↔ _
    rw [lenLe_iff W n, List.length_cons]
    omega

theorem nthW_nil (i : ℕ) : nthW [] i = [] := rfl

theorem nthW_cons_zero (w : List ℕ) (l : List (List ℕ)) : nthW (w :: l) 0 = w := rfl

theorem nthW_cons_succ (w : List ℕ) (l : List (List ℕ)) (i : ℕ) :
    nthW (w :: l) (i + 1) = nthW l i := rfl

theorem nthW_mem_or : ∀ (l : List (List ℕ)) (i : ℕ), nthW l i ∈ l ∨ nthW l i = []
  | [], i => Or.inr (nthW_nil i)
  | w :: l, 0 => Or.inl (by rw [nthW_cons_zero]; exact List.mem_cons_self)
  | w :: l, i + 1 => by
    rw [nthW_cons_succ]
    rcases nthW_mem_or l i with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr h

theorem nthW_ge : ∀ (l : List (List ℕ)) (i : ℕ), l.length ≤ i → nthW l i = []
  | [], i, _ => nthW_nil i
  | w :: l, 0, h => absurd h (by simp)
  | w :: l, i + 1, h => by
    rw [nthW_cons_succ]
    exact nthW_ge l i (by simp at h; omega)

theorem exists_nthW : ∀ (l : List (List ℕ)) (w : List ℕ), w ∈ l → ∃ k < l.length, nthW l k = w
  | [], _, h => absurd h List.not_mem_nil
  | v :: l, w, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨k, hk, e⟩ := exists_nthW l w h
      exact ⟨k + 1, by simp; omega, by rw [nthW_cons_succ, e]⟩

theorem chW_nthW {L : ℕ → Bool} {W : List (List ℕ)} (h : chA L W = true) (i : ℕ) :
    chW L (nthW W i) = true := by
  rcases nthW_mem_or W i with hm | hm
  · exact (chA_iff L W).1 h _ hm
  · rw [hm]
    exact chW_nil L

theorem expC_nil (M : List (List ℕ)) : expC M [] = [] := rfl

theorem expC_cons (M : List (List ℕ)) (k : ℕ) (c : List ℕ) :
    expC M (k :: c) = nthW M k ++ expC M c := rfl

theorem chW_expC {L : ℕ → Bool} {M : List (List ℕ)} (h : chA L M = true) :
    ∀ c : List ℕ, chW L (expC M c) = true
  | [] => chW_nil L
  | k :: c => by
    rw [expC_cons]
    exact chW_append_of (chW_nthW h k) (chW_expC h c)

theorem catW_nil : catW [] = [] := rfl

theorem catW_cons (w : List ℕ) (R : List (List ℕ)) : catW (w :: R) = w ++ catW R := rfl

theorem chW_catW {L : ℕ → Bool} : ∀ {R : List (List ℕ)}, chA L R = true → chW L (catW R) = true
  | [], _ => chW_nil L
  | w :: R, h => by
    change (chW L w && chA L R) = true at h
    rw [Bool.and_eq_true] at h
    rw [catW_cons]
    exact chW_append_of h.1 (chW_catW h.2)

theorem repW_zero (w : List ℕ) : repW w 0 = [] := rfl

theorem repW_succ (w : List ℕ) (p : ℕ) : repW w (p + 1) = w ++ repW w p := rfl

theorem chW_repW {L : ℕ → Bool} {w : List ℕ} (h : chW L w = true) :
    ∀ p : ℕ, chW L (repW w p) = true
  | 0 => chW_nil L
  | p + 1 => by
    rw [repW_succ]
    exact chW_append_of h (chW_repW h p)

variable {G : Type} [Group G]

structure Model (L : ℕ → Bool) (E : List ℕ → List ℕ → Bool) (ev : List ℕ → G) : Prop where
  nil : ev [] = 1
  append : ∀ u v, ev (u ++ v) = ev v * ev u
  sound : ∀ u v, chW L u = true → chW L v = true → E u v = true → ev u = ev v

@[expose] def wE (f : ℕ → G) : List ℕ → G
  | [] => 1
  | c :: w => wE f w * f c

theorem wE_nil (f : ℕ → G) : wE f [] = 1 := rfl

theorem wE_cons (f : ℕ → G) (c : ℕ) (w : List ℕ) : wE f (c :: w) = wE f w * f c := rfl

theorem wE_append (f : ℕ → G) : ∀ u v : List ℕ, wE f (u ++ v) = wE f v * wE f u
  | [], v => by rw [List.nil_append, wE_nil, mul_one]
  | c :: u, v => by rw [List.cons_append, wE_cons, wE_append f u v, wE_cons, mul_assoc]

theorem Model.of_wE {L : ℕ → Bool} {E : List ℕ → List ℕ → Bool} (f : ℕ → G)
    (h : ∀ u v, chW L u = true → chW L v = true → E u v = true → wE f u = wE f v) :
    Model L E (wE f) :=
  ⟨rfl, wE_append f, h⟩

variable {L : ℕ → Bool} {E : List ℕ → List ℕ → Bool} {ev : List ℕ → G}

namespace Model

variable (hM : Model L E ev)
include hM

theorem repW_eq (w : List ℕ) : ∀ p : ℕ, ev (repW w p) = ev w ^ p
  | 0 => by rw [repW_zero, hM.nil, pow_zero]
  | p + 1 => by rw [repW_succ, hM.append, repW_eq w p, pow_succ]

theorem eq {u v : List ℕ} (hu : chW L u = true) (hv : chW L v = true) (h : E u v = true) :
    ev u = ev v :=
  hM.sound u v hu hv h

theorem pow {w : List ℕ} {p : ℕ} (hw : chW L w = true) (h : E (repW w p) [] = true) :
    ev w ^ p = 1 := by
  rw [← hM.repW_eq, ← hM.nil]
  exact hM.eq (chW_repW hw p) (chW_nil L) h

theorem pow_eq {w z : List ℕ} {p e : ℕ} (hw : chW L w = true) (hz : chW L z = true)
    (h : E (repW w p) (repW z e) = true) : ev w ^ p = ev z ^ e := by
  rw [← hM.repW_eq, ← hM.repW_eq]
  exact hM.eq (chW_repW hw p) (chW_repW hz e) h

theorem comm {u v : List ℕ} (hu : chW L u = true) (hv : chW L v = true) (h : cm E u v = true) :
    ev u * ev v = ev v * ev u := by
  have e := hM.eq (chW_append_of hu hv) (chW_append_of hv hu) h
  rw [hM.append, hM.append] at e
  exact e.symm

theorem conj {t g x : List ℕ} (ht : chW L t = true) (hg : chW L g = true) (hx : chW L x = true)
    (h : cjOK E t g x = true) : ev t * ev g = ev g * ev x := by
  have e := hM.eq (chW_append_of hg ht) (chW_append_of hx hg) h
  rwa [hM.append, hM.append] at e

theorem conj' {x h z : List ℕ} (hx : chW L x = true) (hh : chW L h = true) (hz : chW L z = true)
    (e : E (h ++ x) (z ++ h) = true) : ev x * ev h = ev h * ev z := by
  have e' := hM.eq (chW_append_of hh hx) (chW_append_of hz hh) e
  rwa [hM.append, hM.append] at e'

theorem ne_one (hc : ∀ u, chW L u = true → ev u = 1 → E u [] = true) {u : List ℕ}
    (hu : chW L u = true) (h : neOK E u = true) : ev u ≠ 1 := by
  intro e
  unfold neOK at h
  rw [hc u hu e] at h
  exact Bool.noConfusion h

theorem genOK_facts {a ai b bi : List ℕ} (h : genOK E L a ai b bi = true) :
    chW L a = true ∧ chW L ai = true ∧ chW L b = true ∧ chW L bi = true ∧
      ev ai = (ev a)⁻¹ ∧ ev bi = (ev b)⁻¹ := by
  unfold genOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨ha, hai⟩, hb⟩, hbi⟩, e₁⟩, e₂⟩ := h
  have f₁ := hM.eq (chW_append_of ha hai) (chW_nil L) e₁
  have f₂ := hM.eq (chW_append_of hb hbi) (chW_nil L) e₂
  rw [hM.append, hM.nil, mul_eq_one_iff_eq_inv] at f₁ f₂
  exact ⟨ha, hai, hb, hbi, f₁, f₂⟩

theorem repOK_facts {p : ℕ} {T : List (List ℕ)} {i : ℕ} {r : List ℕ}
    (h : repOK E L p T i r = true) :
    chW L (nthW T i) = true ∧ ev (nthW T i) = ev r ∧ ev (nthW T i) ^ p = 1 := by
  unfold repOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hc, hr⟩, he⟩, hp⟩ := h
  exact ⟨hc, hM.eq hc hr he, hM.pow hc hp⟩

theorem p3OK_facts {p e₁ e₂ : ℕ} {g₁ g₂ z : List ℕ} (h : p3OK E L p g₁ g₂ z e₁ e₂ = true) :
    chW L g₁ = true ∧ chW L g₂ = true ∧ chW L z = true ∧ neOK E z = true ∧ ev z ^ p = 1 ∧
      ev z * ev g₁ = ev g₁ * ev z ∧ ev z * ev g₂ = ev g₂ * ev z ∧
      ev g₁ * ev g₂ = ev z * (ev g₂ * ev g₁) ∧ ev g₁ ^ p = ev z ^ e₁ ∧ ev g₂ ^ p = ev z ^ e₂ := by
  unfold p3OK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hz⟩, hne⟩, hzp⟩, c₁⟩, c₂⟩, hrel⟩, hp₁⟩, hp₂⟩ := h
  have e := hM.eq (chW_append_of h2 h1) (chW_append_of (chW_append_of h1 h2) hz) hrel
  rw [hM.append, hM.append, hM.append] at e
  exact ⟨h1, h2, hz, hne, hM.pow hz hzp, hM.comm hz h1 c₁, hM.comm hz h2 c₂, e,
    hM.pow_eq h1 hz hp₁, hM.pow_eq h2 hz hp₂⟩

theorem lineOK_eq {g₁ g₂ t : List ℕ} {i : ℕ} (h₁ : chW L g₁ = true) (h₂ : chW L g₂ = true)
    (h : lineOK E L g₁ g₂ i t = true) : chW L t = true ∧ ev t = ev g₁ * ev g₂ ^ i := by
  unfold lineOK at h
  rw [Bool.and_eq_true] at h
  have e := hM.eq h.1 (chW_append_of (chW_repW h₂ i) h₁) h.2
  rw [hM.append, hM.repW_eq] at e
  exact ⟨h.1, e⟩

theorem mem_of_letters {y₁ y₂ : List ℕ} {M : List (List ℕ)} {nL n : ℕ}
    (hM2 : lenLe M (2 * nL) = true) (hMc : chA L M = true) (o₁ : chW L y₁ = true)
    (o₂ : chW L y₂ = true) (hL : ∀ j < nL, clL E y₁ y₂ n M j = true) (k : ℕ) :
    ev (nthW M k) ∈ Subgroup.closure
      ((Subgroup.centralizer {ev y₁} : Set G) ∪ Subgroup.centralizer {ev y₂}) := by
  set S : Subgroup G :=
    Subgroup.closure ((Subgroup.centralizer {ev y₁} : Set G) ∪ Subgroup.centralizer {ev y₂})
  have hMl := (lenLe_iff _ _).1 hM2
  by_cases hk : k < 2 * nL
  swap
  · rw [nthW_ge M k (by omega), hM.nil]
    exact S.one_mem
  have oM := chW_nthW hMc
  have hj := hL (k / 2) (by omega)
  unfold clL at hj
  rw [Bool.and_eq_true] at hj
  obtain ⟨hinv, hj⟩ := hj
  have hw : ev (nthW M (2 * (k / 2))) ∈ S := by
    apply Subgroup.subset_closure
    cases hb : Nat.blt (k / 2) n
    · rw [hb, cond_false] at hj
      exact Or.inr (Subgroup.mem_centralizer_singleton_iff.2 (hM.comm (oM _) o₂ hj))
    · rw [hb, cond_true] at hj
      exact Or.inl (Subgroup.mem_centralizer_singleton_iff.2 (hM.comm (oM _) o₁ hj))
  have hinv' := hM.eq (chW_append_of (oM _) (oM _)) (chW_nil L) hinv
  rw [hM.append, hM.nil, mul_eq_one_iff_eq_inv] at hinv'
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have e : 2 * j / 2 = j := by omega
    rwa [e] at hw
  · have e : (2 * j + 1) / 2 = j := by omega
    rw [e] at hw hinv'
    rw [hinv']
    exact S.inv_mem hw

theorem mem_expC {S : Subgroup G} {M : List (List ℕ)} (h : ∀ k, ev (nthW M k) ∈ S) :
    ∀ c, ev (expC M c) ∈ S
  | [] => by
    rw [expC_nil, hM.nil]
    exact S.one_mem
  | k :: c => by
    rw [expC_cons, hM.append]
    exact S.mul_mem (mem_expC h c) (h k)

theorem mem_of_stages {S : Subgroup G} {M C R : List (List ℕ)} {nR : ℕ}
    (hlet : ∀ k, ev (nthW M k) ∈ S) (hMc : chA L M = true) (hs : stH L R nR = true)
    (hS : ∀ k < nR, stOK E M C R k = true) (k : ℕ) : ev (nthW R k) ∈ S := by
  unfold stH at hs
  rw [Bool.and_eq_true] at hs
  by_cases hk : k < nR
  · have h := hS k hk
    unfold stOK at h
    rw [← hM.eq (chW_expC hMc _) (chW_nthW hs.2 k) h]
    exact hM.mem_expC hlet _
  · rw [nthW_ge R k (by have := (lenLe_iff _ _).1 hs.1; omega), hM.nil]
    exact S.one_mem

theorem mem_catW {S : Subgroup G} : ∀ {R : List (List ℕ)}, (∀ w ∈ R, ev w ∈ S) →
    ev (catW R) ∈ S
  | [], _ => by
    rw [catW_nil, hM.nil]
    exact S.one_mem
  | w :: R, h => by
    rw [catW_cons, hM.append]
    exact S.mul_mem (mem_catW fun v hv => h v (List.mem_cons_of_mem _ hv))
      (h w List.mem_cons_self)

theorem mem_of_prOK {S : Subgroup G} {R : List (List ℕ)} {nR : ℕ} {o : List ℕ}
    (hR : ∀ k, ev (nthW R k) ∈ S) (hs : stH L R nR = true) (hP : prOK E L R o = true) :
    ev o ∈ S := by
  unfold stH at hs
  unfold prOK at hP
  rw [Bool.and_eq_true] at hs hP
  rw [← hM.eq (chW_catW hs.2) hP.1 hP.2]
  exact hM.mem_catW fun w hw => by
    obtain ⟨k, -, rfl⟩ := exists_nthW R w hw
    exact hR k

end Model

end CFSG.KD.SporCov

end
