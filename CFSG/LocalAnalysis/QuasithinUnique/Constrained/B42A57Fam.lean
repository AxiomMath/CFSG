module

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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.B42A57

open Equiv

theorem exists_perm_extend (s : Finset (Fin 7)) (f : Fin 7 → Fin 7) (hf : Set.InjOn f s) :
    ∃ σ : Perm (Fin 7), ∀ i ∈ s, σ i = f i := by
  classical
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq (α := Fin 7) (t := Finset.univ)
    (by simp) (s := s) (f := f) (by intro x _; simp) hf
  refine ⟨g.trans (Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _)), fun i hi => ?_⟩
  simpa using hg i hi

theorem exists_perm_list (xs ys : List (Fin 7)) (hx : xs.Nodup) (hy : ys.Nodup)
    (hl : xs.length = ys.length) :
    ∃ σ : Perm (Fin 7), ∀ i (hi : i < xs.length), σ (xs[i]) = ys[i]'(hl ▸ hi) := by
  classical
  let f : Fin 7 → Fin 7 := fun x => ys.getD (xs.idxOf x) x
  have hxs : ∀ i (hi : i < xs.length), xs.idxOf (xs[i]) = i := fun i hi =>
    hx.idxOf_getElem i hi
  have hf : ∀ i (hi : i < xs.length), f (xs[i]) = ys[i]'(hl ▸ hi) := fun i hi => by
    simp only [f, hxs i hi]
    rw [List.getD_eq_getElem _ _ (hl ▸ hi)]
  have hinj : Set.InjOn f (xs.toFinset : Finset (Fin 7)) := by
    intro a ha b hb hab
    have ha' := List.mem_toFinset.1 ha
    have hb' := List.mem_toFinset.1 hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha'
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hb'
    rw [hf i hi, hf j hj] at hab
    have : i = j := by
      have := (List.Nodup.getElem_inj_iff hy).1 hab
      exact this
    subst this
    rfl
  obtain ⟨σ, hσ⟩ := exists_perm_extend xs.toFinset f hinj
  refine ⟨σ, fun i hi => ?_⟩
  rw [hσ _ (List.mem_toFinset.2 (List.getElem_mem hi)), hf i hi]

theorem family_contradiction {S : Type} [CommGroup S] [Finite S] {N c : ℕ} (F : Fin N → Subgroup S)
    (hc : ∀ i, Nat.card (F i) = c) (hd : ∀ i j, i ≠ j → F i ⊓ F j = ⊥) (hN : 11 ≤ N)
    (hc4 : 4 ≤ c) (hS : Nat.card S ≤ 8 * c) : False := by
  classical
  have : Fintype S := Fintype.ofFinite S
  let U : Fin N → Finset S := fun i => (Finset.univ.filter (fun x => x ∈ F i)).erase 1
  have hUcard : ∀ i, (U i).card = c - 1 := by
    intro i
    have h1 : (Finset.univ.filter (fun x => x ∈ F i)).card = c := by
      rw [← hc i, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [U]
    rw [Finset.card_erase_of_mem (by simp [one_mem]), h1]
  have hdisj : (Set.univ : Set (Fin N)).PairwiseDisjoint U := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    simp only [U, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hxi hxj
    have : x ∈ F i ⊓ F j := ⟨hxi.2, hxj.2⟩
    rw [hd i j hij] at this
    exact hxi.1 (Subgroup.mem_bot.1 this)
  have hunion : (Finset.univ.biUnion U).card = N * (c - 1) := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hdisj (Set.mem_univ i) (Set.mem_univ j) hij)]
    simp [hUcard]
  have hsub : (Finset.univ.biUnion U) ⊆ Finset.univ.erase 1 := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, U, Finset.mem_erase,
      Finset.mem_filter] at hx
    obtain ⟨i, hx1, _⟩ := hx
    simp [hx1]
  have hle := Finset.card_le_card hsub
  rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ← Nat.card_eq_fintype_card] at hle
  have h4 : 11 * (c - 1) ≤ N * (c - 1) := Nat.mul_le_mul_right _ hN
  omega

end CFSG.QuasithinUnique.B42A57
