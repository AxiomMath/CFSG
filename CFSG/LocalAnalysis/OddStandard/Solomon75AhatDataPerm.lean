module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataInputs
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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Equiv Equiv.Perm Subgroup

theorem nat_all_iff {n : ℕ} {f : (i : ℕ) → i < n → Bool} :
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro H i hi
    exact H ⟨i, hi⟩ (List.mem_finRange _)
  · rintro H ⟨i, hi⟩ -
    exact H i hi

theorem nat_any_iff {n : ℕ} {f : (i : ℕ) → i < n → Bool} :
    Nat.any n f = true ↔ ∃ i, ∃ h : i < n, f i h = true := by
  rw [Nat.any_eq_finRange_any, List.any_eq_true]
  constructor
  · rintro ⟨⟨i, hi⟩, -, h⟩
    exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, hi⟩, List.mem_finRange _, h⟩

@[expose] def Rep (n : ℕ) (t : Array ℕ) (σ : Perm (Fin n)) : Prop :=
  ∀ i : Fin n, t[(i : ℕ)]! = (σ i : ℕ)

variable {n : ℕ}

theorem getElem!_ofFn_nat {m : ℕ} (f : Fin m → ℕ) {i : ℕ} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem Rep.unique {t : Array ℕ} {σ τ : Perm (Fin n)} (h₁ : Rep n t σ) (h₂ : Rep n t τ) :
    σ = τ := Equiv.ext fun x => Fin.ext ((h₁ x).symm.trans (h₂ x))

theorem Rep.apply {t : Array ℕ} {σ : Perm (Fin n)} (h : Rep n t σ) {i : ℕ} (hi : i < n) :
    t[i]! = (σ ⟨i, hi⟩ : ℕ) := h ⟨i, hi⟩

theorem rep_idA : Rep n (idA n) 1 := fun x => by
  rw [idA, getElem!_ofFn_nat _ x.2]
  rfl

theorem rep_mulA {t u : Array ℕ} {σ τ : Perm (Fin n)} (ht : Rep n t σ) (hu : Rep n u τ) :
    Rep n (mulA n t u) (σ * τ) := fun x => by
  rw [mulA, getElem!_ofFn_nat _ x.2, hu x]
  exact ht (τ x)

theorem eqA_iff {t u : Array ℕ} {σ τ : Perm (Fin n)} (ht : Rep n t σ) (hu : Rep n u τ) :
    eqA n t u = true ↔ σ = τ := by
  rw [eqA, nat_all_iff]
  constructor
  · intro H
    refine Equiv.ext fun x => Fin.ext ?_
    have := H x x.2
    rwa [beq_iff_eq, ht x, hu x] at this
  · rintro rfl i hi
    rw [beq_iff_eq, ht.apply hi, hu.apply hi]

theorem rep_of_eqA_left {t u : Array ℕ} {τ : Perm (Fin n)} (ht : Rep n t τ)
    (h : eqA n t u = true) : Rep n u τ := fun x => by
  rw [eqA, nat_all_iff] at h
  have := h x x.2
  rw [beq_iff_eq, ht x] at this
  exact this.symm

theorem eqA_comm {t u : Array ℕ} : eqA n t u = eqA n u t := by
  unfold eqA
  congr 1
  funext i _
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  exact ⟨Eq.symm, Eq.symm⟩

theorem rep_swapA {a b : ℕ} (ha : a < n) (hb : b < n) :
    Rep n (swapA n a b) (swap ⟨a, ha⟩ ⟨b, hb⟩) := fun x => by
  rw [swapA, getElem!_ofFn_nat _ x.2]
  by_cases h1 : (x : ℕ) = a
  · have : x = ⟨a, ha⟩ := Fin.ext h1
    subst this
    simp
  · by_cases h2 : (x : ℕ) = b
    · have : x = ⟨b, hb⟩ := Fin.ext h2
      subst this
      simp
    · have e1 : x ≠ ⟨a, ha⟩ := fun h => h1 (by rw [h])
      have e2 : x ≠ ⟨b, hb⟩ := fun h => h2 (by rw [h])
      simp [h1, h2, swap_apply_of_ne_of_ne e1 e2]

theorem suppAux_eq_sum (t : Array ℕ) : ∀ k, suppAux t k =
    ∑ i ∈ Finset.range k, (if t[i]! == i then 0 else 1)
  | 0 => by simp [suppAux]
  | k + 1 => by rw [suppAux, Finset.sum_range_succ, suppAux_eq_sum t k]

theorem suppA_eq {t : Array ℕ} {σ : Perm (Fin n)} (h : Rep n t σ) :
    suppA n t = σ.support.card := by
  rw [suppA, suppAux_eq_sum, ← Fin.sum_univ_eq_sum_range
    (fun i => if t[i]! == i then 0 else 1) n, Equiv.Perm.support, Finset.card_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h x]
  by_cases hx : (σ x : ℕ) = x
  · have : σ x = x := Fin.ext hx
    simp [this]
  · have : σ x ≠ x := fun h' => hx (by rw [h'])
    simp [hx, this]

@[expose] def IsoI (σ : Perm (Fin n)) : Prop := σ * σ = 1 ∧ σ.support.card = 8

@[expose] def DblI (σ : Perm (Fin n)) : Prop := σ * σ = 1 ∧ σ.support.card = 4

@[expose] def AdjI (a b : Perm (Fin n)) : Prop := a ≠ b ∧ a * b = b * a ∧ IsoI (a * b)

@[expose] def AdjIn (Q : Subgroup (Perm (Fin n))) (a b : Perm (Fin n)) : Prop :=
  a ∈ Q ∧ b ∈ Q ∧ IsoI a ∧ IsoI b ∧ AdjI a b

@[expose] def Indep2 (a b : Perm (Fin n)) : Prop := a * b = b * a ∧ IsoI (a * b)

@[expose] def Indep3 (a b c : Perm (Fin n)) : Prop :=
  a * c = c * a ∧ b * c = c * b ∧ IsoI (a * c) ∧ IsoI (b * c) ∧ IsoI (a * b * c)

@[expose] def Indep4 (a b c d : Perm (Fin n)) : Prop :=
  a * d = d * a ∧ b * d = d * b ∧ c * d = d * c ∧ IsoI (a * d) ∧ IsoI (b * d) ∧ IsoI (c * d) ∧
    IsoI (a * b * d) ∧ IsoI (a * c * d) ∧ IsoI (b * c * d) ∧ IsoI (a * b * c * d)

theorem isoA_iff {t : Array ℕ} {σ : Perm (Fin n)} (h : Rep n t σ) :
    isoA n t = true ↔ IsoI σ := by
  unfold isoA IsoI
  rw [Bool.and_eq_true, beq_iff_eq, eqA_iff (rep_mulA h h) rep_idA, suppA_eq h]

theorem dblA_iff {t : Array ℕ} {σ : Perm (Fin n)} (h : Rep n t σ) :
    dblA n t = true ↔ DblI σ := by
  unfold dblA DblI
  rw [Bool.and_eq_true, beq_iff_eq, eqA_iff (rep_mulA h h) rep_idA, suppA_eq h]

theorem commA_iff {a b : Array ℕ} {σ τ : Perm (Fin n)} (ha : Rep n a σ) (hb : Rep n b τ) :
    commA n a b = true ↔ σ * τ = τ * σ :=
  eqA_iff (rep_mulA ha hb) (rep_mulA hb ha)

theorem adjA_iff {a b : Array ℕ} {σ τ : Perm (Fin n)} (ha : Rep n a σ) (hb : Rep n b τ) :
    adjA n a b = true ↔ AdjI σ τ := by
  unfold adjA AdjI
  rw [Bool.and_eq_true, Bool.and_eq_true, commA_iff ha hb, isoA_iff (rep_mulA ha hb),
    Bool.not_eq_true', Bool.eq_false_iff, Ne, eqA_iff ha hb]
  tauto

@[expose] def swapsPerm (n : ℕ) [NeZero n] (sw : List (ℕ × ℕ)) : Perm (Fin n) :=
  sw.foldl (fun σ p => σ * swap (Fin.ofNat n p.1) (Fin.ofNat n p.2)) 1

theorem fin_ofNat_eq [NeZero n] {a : ℕ} (h : a < n) : Fin.ofNat n a = ⟨a, h⟩ :=
  Fin.ext (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt h])

theorem rep_foldl_swaps [NeZero n] (sw : List (ℕ × ℕ)) (hsw : ∀ p ∈ sw, p.1 < n ∧ p.2 < n) :
    ∀ (t : Array ℕ) (σ : Perm (Fin n)), Rep n t σ →
      Rep n (sw.foldl (fun t p => mulA n t (swapA n p.1 p.2)) t)
        (sw.foldl (fun σ p => σ * swap (Fin.ofNat n p.1) (Fin.ofNat n p.2)) σ) := by
  induction sw with
  | nil => intro t σ h; exact h
  | cons p sw ih =>
    intro t σ h
    have hp := hsw p List.mem_cons_self
    simp only [List.foldl_cons]
    refine ih (fun q hq => hsw q (List.mem_cons_of_mem _ hq)) _ _ (rep_mulA h ?_)
    rw [fin_ofNat_eq hp.1, fin_ofNat_eq hp.2]
    exact rep_swapA hp.1 hp.2

theorem rep_swapsA [NeZero n] (sw : List (ℕ × ℕ)) (hsw : ∀ p ∈ sw, p.1 < n ∧ p.2 < n) :
    Rep n (swapsA n sw) (swapsPerm n sw) :=
  rep_foldl_swaps sw hsw _ _ rep_idA

theorem sign_foldl_swaps [NeZero n] (sw : List (ℕ × ℕ))
    (hsw : ∀ p ∈ sw, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2) :
    ∀ σ : Perm (Fin n),
      sign (sw.foldl (fun σ p => σ * swap (Fin.ofNat n p.1) (Fin.ofNat n p.2)) σ) =
        sign σ * (-1) ^ sw.length := by
  induction sw with
  | nil => intro σ; simp
  | cons p sw ih =>
    intro σ
    have hp := hsw p List.mem_cons_self
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (fun q hq => hsw q (List.mem_cons_of_mem _ hq)), Perm.sign_mul,
      Perm.sign_swap]
    · rw [pow_succ]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    · rw [fin_ofNat_eq hp.1, fin_ofNat_eq hp.2.1]
      exact fun h => hp.2.2 (congrArg Fin.val h)

theorem sign_swapsPerm [NeZero n] (sw : List (ℕ × ℕ))
    (hsw : ∀ p ∈ sw, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2) (hev : Even sw.length) :
    sign (swapsPerm n sw) = 1 := by
  rw [swapsPerm, sign_foldl_swaps sw hsw]
  simp [hev.neg_one_pow]

theorem genSwaps_ok (hn : 8 ≤ n) (hn' : n ≤ 11) :
    ∀ sw ∈ genSwaps n, (∀ p ∈ sw, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2) ∧ Even sw.length := by
  interval_cases n <;> decide

section Sylow

variable [NeZero n]

@[expose] def genPerms (n : ℕ) [NeZero n] : List (Perm (Fin n)) := (genSwaps n).map (swapsPerm n)

@[expose] def P0 (n : ℕ) [NeZero n] : Subgroup (Perm (Fin n)) :=
  Subgroup.closure {σ | σ ∈ genPerms n}

theorem mem_gensA (hn : 8 ≤ n) (hn' : n ≤ 11) :
    (∀ x ∈ gensA n, ∃ σ ∈ genPerms n, Rep n x σ) ∧
      (∀ σ ∈ genPerms n, ∃ x ∈ gensA n, Rep n x σ) := by
  have hok := genSwaps_ok hn hn'
  constructor
  · intro x hx
    simp only [gensA, Array.mem_map, List.mem_toArray] at hx
    obtain ⟨sw, hsw, rfl⟩ := hx
    exact ⟨swapsPerm n sw, List.mem_map_of_mem hsw,
      rep_swapsA sw fun p hp => ⟨((hok sw hsw).1 p hp).1, ((hok sw hsw).1 p hp).2.1⟩⟩
  · intro σ hσ
    simp only [genPerms, List.mem_map] at hσ
    obtain ⟨sw, hsw, rfl⟩ := hσ
    refine ⟨swapsA n sw, ?_, rep_swapsA sw fun p hp =>
      ⟨((hok sw hsw).1 p hp).1, ((hok sw hsw).1 p hp).2.1⟩⟩
    simp only [gensA, Array.mem_map, List.mem_toArray]
    exact ⟨sw, hsw, rfl⟩

theorem genPerms_sq (hn : 8 ≤ n) (hn' : n ≤ 11)
    (h : (gensA n).all (fun x => eqA n (mulA n x x) (idA n)) = true) :
    ∀ σ ∈ genPerms n, σ * σ = 1 := by
  intro σ hσ
  obtain ⟨x, hx, hxσ⟩ := (mem_gensA hn hn').2 σ hσ
  rw [Array.all_eq_true'] at h
  have := h x hx
  exact (eqA_iff (rep_mulA hxσ hxσ) rep_idA).1 this

structure TableSpec (n : ℕ) [NeZero n] (tab : Array (Array ℕ)) (card : ℕ) : Prop where
  size : tab.size = card
  mem : ∀ a ∈ tab, ∃ σ ∈ P0 n, Rep n a σ
  surj : ∀ σ ∈ P0 n, ∃ a ∈ tab, Rep n a σ
  inj : ∀ (k l : ℕ) (hk : k < tab.size) (hl : l < tab.size) (σ : Perm (Fin n)),
    Rep n tab[k] σ → Rep n tab[l] σ → k = l

theorem tableSpec_of_tableOK (hn : 8 ≤ n) (hn' : n ≤ 11) {tab : Array (Array ℕ)}
    {par lab : Array ℕ} {card : ℕ} (hcard : 0 < card)
    (h : tableOK n (gensA n) tab par lab card = true) : TableSpec n tab card := by
  simp only [tableOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hsize : 0 < tab.size := by rw [h1]; exact hcard
  have hgen := mem_gensA hn hn'
  have hsq := genPerms_sq hn hn' h5
  have hid : Rep n tab[0] 1 := by
    have := rep_of_eqA_left (rep_idA (n := n)) (by
      rw [eqA_comm]
      simpa [getElem!_pos, hsize] using h4)
    exact this
  have hmem : ∀ k (hk : k < tab.size), ∃ σ ∈ P0 n, Rep n tab[k] σ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · exact ⟨1, one_mem _, hid⟩
      · rw [nat_all_iff] at h6
        have h6k := h6 k hk
        simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h6k
        rcases h6k with h0 | ⟨⟨hp, hl⟩, he⟩
        · omega
        · obtain ⟨σ', hσ', hrep⟩ := ih (par[k]!) hp (by omega)
          have hgmem : (gensA n)[lab[k]!]'hl ∈ gensA n := Array.getElem_mem _
          obtain ⟨τ, hτ, hτrep⟩ := hgen.1 _ hgmem
          have hrep' := rep_mulA hrep hτrep
          rw [getElem!_pos tab (par[k]!) (by omega), getElem!_pos (gensA n) (lab[k]!) hl,
            getElem!_pos tab k hk] at he
          exact ⟨σ' * τ, mul_mem hσ' (subset_closure hτ), rep_of_eqA_left hrep' he⟩
  have hmem' : ∀ a ∈ tab, ∃ σ ∈ P0 n, Rep n a σ := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 ha
    exact hmem k hk
  have hsurj : ∀ σ ∈ P0 n, ∃ a ∈ tab, Rep n a σ := by
    have step : ∀ (x y : Perm (Fin n)), (∃ a ∈ tab, Rep n a x) → y ∈ genPerms n →
        ∃ a ∈ tab, Rep n a (x * y) := by
      rintro x y ⟨a, ha, hax⟩ hy
      obtain ⟨g', hg', hg'rep⟩ := hgen.2 y hy
      obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 ha
      rw [nat_all_iff] at h7
      have h7k := h7 k hk
      rw [Array.all_eq_true'] at h7k
      have := h7k g' hg'
      rw [Array.any_eq_true'] at this
      obtain ⟨y', hy', hey⟩ := this
      rw [getElem!_pos tab k hk] at hey
      exact ⟨y', hy', rep_of_eqA_left (rep_mulA hax hg'rep) hey⟩
    intro σ hσ
    refine Subgroup.closure_induction_right (p := fun x _ => ∃ a ∈ tab, Rep n a x) ?_ ?_ ?_ hσ
    · exact ⟨tab[0], Array.getElem_mem _, hid⟩
    · intro x hx y hy ih
      exact step x y ih hy
    · intro x hx y hy ih
      have : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
      rw [this]
      exact step x y ih hy
  have hinj : ∀ (k l : ℕ) (hk : k < tab.size) (hl : l < tab.size) (σ : Perm (Fin n)),
      Rep n tab[k] σ → Rep n tab[l] σ → k = l := by
    intro k l hk hl σ hkσ hlσ
    by_contra hne
    have key : ∀ k l (hk : k < tab.size) (hl : l < tab.size), l < k →
        ∀ σ : Perm (Fin n), Rep n tab[k] σ → Rep n tab[l] σ → False := by
      intro k l hk hl hlk σ hkσ hlσ
      rw [nat_all_iff] at h8
      have := h8 k hk
      rw [nat_all_iff] at this
      have := this l hlk
      rw [getElem!_pos tab k hk, getElem!_pos tab l hl] at this
      have h' : eqA n tab[k] tab[l] = true := (eqA_iff hkσ hlσ).2 rfl
      simp [h'] at this
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact key l k hl hk hlt σ hlσ hkσ
    · exact key k l hk hl hlt σ hkσ hlσ
  exact ⟨h1, hmem', hsurj, hinj⟩

theorem TableSpec.card_eq {tab : Array (Array ℕ)} {card : ℕ} (T : TableSpec n tab card) :
    Nat.card (P0 n) = card := by
  classical
  have hm : ∀ k : Fin tab.size, ∃ σ ∈ P0 n, Rep n tab[(k : ℕ)] σ := fun k =>
    T.mem _ (Array.getElem_mem _)
  choose σ hσ hrep using hm
  let f : Fin tab.size → P0 n := fun k => ⟨σ k, hσ k⟩
  have hf : Function.Bijective f := by
    constructor
    · intro k l hkl
      have : σ k = σ l := congrArg Subtype.val hkl
      exact Fin.ext (T.inj k l k.2 l.2 (σ k) (hrep k) (this ▸ hrep l))
    · rintro ⟨x, hx⟩
      obtain ⟨a, ha, hax⟩ := T.surj x hx
      obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 ha
      refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
      exact Rep.unique (hrep ⟨k, hk⟩) hax
  rw [← T.size, ← Nat.card_fin tab.size]
  exact (Nat.card_eq_of_bijective f hf).symm

theorem P0_le_alternatingGroup (hn : 8 ≤ n) (hn' : n ≤ 11) : P0 n ≤ alternatingGroup (Fin n) := by
  have hok := genSwaps_ok hn hn'
  rw [P0, Subgroup.closure_le]
  intro σ hσ
  simp only [genPerms, Set.mem_ofPred_eq, List.mem_map] at hσ
  obtain ⟨sw, hsw, rfl⟩ := hσ
  rw [SetLike.mem_coe, Perm.mem_alternatingGroup]
  exact sign_swapsPerm sw (hok sw hsw).1 (hok sw hsw).2

end Sylow

theorem AdjI.symm {a b : Perm (Fin n)} (h : AdjI a b) : AdjI b a := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.symm, h2.symm, ?_⟩
  rw [← h2]
  exact h3

theorem AdjIn.symm {Q : Subgroup (Perm (Fin n))} {a b : Perm (Fin n)} (h : AdjIn Q a b) :
    AdjIn Q b a :=
  ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.symm⟩

theorem mem_isoIdx {tab : Array (Array ℕ)} {k : ℕ} :
    k ∈ isoIdx n tab ↔ k < tab.size ∧ isoA n tab[k]! = true := by
  rw [isoIdx, Array.mem_filter, Array.mem_range]

theorem mem_isoArr {tab : Array (Array ℕ)} {a : Array ℕ} :
    a ∈ (isoIdx n tab).map (fun k => tab[k]!) ↔ a ∈ tab ∧ isoA n a = true := by
  rw [Array.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [mem_isoIdx] at hk
    exact ⟨by rw [getElem!_pos tab k hk.1]; exact Array.getElem_mem _, hk.2⟩
  · rintro ⟨ha, hiso⟩
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 ha
    refine ⟨k, mem_isoIdx.2 ⟨hk, ?_⟩, getElem!_pos tab k hk⟩
    rwa [getElem!_pos tab k hk]

section FromTable

variable [NeZero n] {tab : Array (Array ℕ)} {card : ℕ}

theorem nbr_of_nbrOK (T : TableSpec n tab card) (h : nbrOK n tab = true) :
    ∀ a ∈ P0 n, IsoI a → ∃ b ∈ P0 n, IsoI b ∧ AdjI a b := by
  intro a ha hiso
  obtain ⟨x, hx, hxa⟩ := T.surj a ha
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hx
  have hk' : k ∈ isoIdx n tab := by
    rw [mem_isoIdx, getElem!_pos tab k hk]
    exact ⟨hk, (isoA_iff hxa).2 hiso⟩
  rw [nbrOK, Array.all_eq_true'] at h
  have := h k hk'
  rw [Array.any_eq_true'] at this
  obtain ⟨l, hl, hadj⟩ := this
  rw [mem_isoIdx] at hl
  obtain ⟨b, hb, hbr⟩ := T.mem tab[l] (Array.getElem_mem hl.1)
  rw [getElem!_pos tab k hk, getElem!_pos tab l hl.1] at hadj
  have hl2 := hl.2
  rw [getElem!_pos tab l hl.1] at hl2
  exact ⟨b, hb, (isoA_iff hbr).1 hl2, (adjA_iff hxa hbr).1 hadj⟩

theorem conn_of_connOK (T : TableSpec n tab card) {ord : Array ℕ} (h : connOK n tab ord = true) :
    ∀ a ∈ P0 n, ∀ b ∈ P0 n, IsoI a → IsoI b →
      Relation.ReflTransGen (AdjIn (P0 n)) a b := by
  simp only [connOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hI0, hord0⟩, hcov⟩, hstep⟩ := h
  rw [nat_all_iff] at hcov hstep
  have hvtx : ∀ i, i < (isoIdx n tab).size →
      ∃ σ ∈ P0 n, IsoI σ ∧ Rep n (tab[(isoIdx n tab)[i]!]!) σ := by
    intro i hi
    have hmem : (isoIdx n tab)[i]! ∈ isoIdx n tab := by
      rw [getElem!_pos (isoIdx n tab) i hi]
      exact Array.getElem_mem _
    obtain ⟨hlt, hiso⟩ := mem_isoIdx.1 hmem
    obtain ⟨σ, hσ, hσr⟩ := T.mem tab[(isoIdx n tab)[i]!] (Array.getElem_mem hlt)
    rw [getElem!_pos tab _ hlt]
    rw [getElem!_pos tab _ hlt] at hiso
    exact ⟨σ, hσ, (isoA_iff hσr).1 hiso, hσr⟩
  obtain ⟨σ₀, hσ₀, hσ₀i, hσ₀r⟩ := hvtx 0 hI0
  have key : ∀ k (hk : k < ord.size), ∀ σ, Rep n (tab[(isoIdx n tab)[ord[k]!]!]!) σ →
      Relation.ReflTransGen (AdjIn (P0 n)) σ₀ σ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk σ hσ
      have hstepk := hstep k hk
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hstepk
      obtain ⟨hlt, hk0 | hex⟩ := hstepk
      · subst hk0
        rw [hord0] at hσ
        rw [Rep.unique hσ hσ₀r]
      · rw [nat_any_iff] at hex
        obtain ⟨j, hjk, hadj⟩ := hex
        have hj : j < ord.size := by omega
        have hjlt := (by
          have := hstep j hj
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at this
          exact this.1)
        obtain ⟨τ, hτ, hτi, hτr⟩ := hvtx _ hjlt
        obtain ⟨σ', hσ', hσ'i, hσ'r⟩ := hvtx _ hlt
        have hσσ' : σ = σ' := Rep.unique hσ hσ'r
        subst hσσ'
        have hadj' := (adjA_iff hτr hσ'r).1 hadj
        exact (ih j hjk hj τ hτr).tail ⟨hτ, hσ', hτi, hσ'i, hadj'⟩
  have reach : ∀ a ∈ P0 n, IsoI a → Relation.ReflTransGen (AdjIn (P0 n)) σ₀ a := by
    intro a ha hia
    obtain ⟨x, hx, hxa⟩ := T.surj a ha
    obtain ⟨m, hm, rfl⟩ := Array.mem_iff_getElem.1 hx
    have hmiso : m ∈ isoIdx n tab := by
      rw [mem_isoIdx, getElem!_pos tab m hm]
      exact ⟨hm, (isoA_iff hxa).2 hia⟩
    obtain ⟨i, hi, him⟩ := Array.mem_iff_getElem.1 hmiso
    have hc := hcov i hi
    rw [Array.contains_iff_mem] at hc
    obtain ⟨k, hk, hki⟩ := Array.mem_iff_getElem.1 hc
    refine key k hk a ?_
    rw [getElem!_pos ord k hk, hki, getElem!_pos (isoIdx n tab) i hi, him,
      getElem!_pos tab m hm]
    exact hxa
  intro a ha b hb hia hib
  have : Std.Symm (AdjIn (P0 n)) := ⟨fun _ _ h => h.symm⟩
  exact (Std.Symm.symm _ _ (reach a ha hia)).trans (reach b hb hib)

theorem exists_isoArr (T : TableSpec n tab card) {σ : Perm (Fin n)} (hσ : σ ∈ P0 n)
    (hi : IsoI σ) : ∃ x ∈ (isoIdx n tab).map (fun k => tab[k]!), Rep n x σ := by
  obtain ⟨x, hx, hxr⟩ := T.surj σ hσ
  exact ⟨x, mem_isoArr.2 ⟨hx, (isoA_iff hxr).2 hi⟩, hxr⟩

theorem of_mem_isoArr (T : TableSpec n tab card) {x : Array ℕ}
    (hx : x ∈ (isoIdx n tab).map (fun k => tab[k]!)) :
    ∃ σ ∈ P0 n, IsoI σ ∧ Rep n x σ := by
  obtain ⟨hxt, hxi⟩ := mem_isoArr.1 hx
  obtain ⟨σ, hσ, hσr⟩ := T.mem x hxt
  exact ⟨σ, hσ, (isoA_iff hσr).1 hxi, hσr⟩

theorem rank_of_rankOK (T : TableSpec n tab card) (h : rankOK n tab = true) :
    ∀ a ∈ P0 n, ∀ b ∈ P0 n, ∀ c ∈ P0 n, ∀ d ∈ P0 n, IsoI a → IsoI b → IsoI c → IsoI d →
      Indep2 a b → Indep3 a b c → ¬ Indep4 a b c d := by
  intro a ha b hb c hc d hd hia hib hic hid h2 h3 h4
  obtain ⟨xa, hxa, hxar⟩ := exists_isoArr T ha hia
  obtain ⟨xb, hxb, hxbr⟩ := exists_isoArr T hb hib
  obtain ⟨xc, hxc, hxcr⟩ := exists_isoArr T hc hic
  obtain ⟨xd, hxd, hxdr⟩ := exists_isoArr T hd hid
  simp only [rankOK, Array.all_eq_true'] at h
  have hP2 : (commA n xa xb && isoA n (mulA n xa xb)) = true := by
    rw [Bool.and_eq_true, commA_iff hxar hxbr, isoA_iff (rep_mulA hxar hxbr)]
    exact h2
  have hP3 : (commA n xa xc && commA n xb xc && isoA n (mulA n xa xc) &&
      isoA n (mulA n xb xc) && isoA n (mulA n (mulA n xa xb) xc)) = true := by
    simp only [Bool.and_eq_true, commA_iff hxar hxcr, commA_iff hxbr hxcr,
      isoA_iff (rep_mulA hxar hxcr), isoA_iff (rep_mulA hxbr hxcr),
      isoA_iff (rep_mulA (rep_mulA hxar hxbr) hxcr)]
    obtain ⟨h31, h32, h33, h34, h35⟩ := h3
    exact ⟨⟨⟨⟨h31, h32⟩, h33⟩, h34⟩, h35⟩
  have hP4 : (commA n xa xd && commA n xb xd && commA n xc xd &&
        isoA n (mulA n xa xd) && isoA n (mulA n xb xd) && isoA n (mulA n xc xd) &&
        isoA n (mulA n (mulA n xa xb) xd) && isoA n (mulA n (mulA n xa xc) xd) &&
        isoA n (mulA n (mulA n xb xc) xd) &&
        isoA n (mulA n (mulA n (mulA n xa xb) xc) xd)) = true := by
    simp only [Bool.and_eq_true, commA_iff hxar hxdr, commA_iff hxbr hxdr, commA_iff hxcr hxdr,
      isoA_iff (rep_mulA hxar hxdr), isoA_iff (rep_mulA hxbr hxdr),
      isoA_iff (rep_mulA hxcr hxdr), isoA_iff (rep_mulA (rep_mulA hxar hxbr) hxdr),
      isoA_iff (rep_mulA (rep_mulA hxar hxcr) hxdr),
      isoA_iff (rep_mulA (rep_mulA hxbr hxcr) hxdr),
      isoA_iff (rep_mulA (rep_mulA (rep_mulA hxar hxbr) hxcr) hxdr)]
    obtain ⟨h41, h42, h43, h44, h45, h46, h47, h48, h49, h410⟩ := h4
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h41, h42⟩, h43⟩, h44⟩, h45⟩, h46⟩, h47⟩, h48⟩, h49⟩, h410⟩
  have e1 := h xa hxa xb hxb
  simp only [hP2, Bool.not_true, Bool.false_or] at e1
  rw [Array.all_eq_true'] at e1
  have e2 := e1 xc hxc
  simp only [hP3, Bool.not_true, Bool.false_or] at e2
  rw [Array.all_eq_true'] at e2
  have e3 := e2 xd hxd
  simp only [hP4, Bool.not_true] at e3
  exact absurd e3 (by simp)

omit [NeZero n] in
theorem exists_eightSub {xa xb xc : Array ℕ} {a b c : Perm (Fin n)} (ha : Rep n xa a)
    (hb : Rep n xb b) (hc : Rep n xc c) {Q : Subgroup (Perm (Fin n))} (haQ : a ∈ Q) (hbQ : b ∈ Q)
    (hcQ : c ∈ Q) (hia : IsoI a) (hib : IsoI b) (hic : IsoI c) (hiab : IsoI (a * b))
    (hiac : IsoI (a * c)) (hibc : IsoI (b * c)) (hiabc : IsoI (a * b * c))
    (h : eightSubOK n xa xb xc = true) :
    ∃ E : Subgroup (Perm (Fin n)), E ≤ Q ∧ Nat.card E = 8 ∧ ∀ e ∈ E, e = 1 ∨ IsoI e := by
  set Ei : Fin 8 → Perm (Fin n) := ![1, a, b, a * b, c, a * c, b * c, a * b * c] with hEi
  have hsz : (eightArr n xa xb xc).size = 8 := rfl
  have hrep : ∀ i : Fin 8, Rep n (eightArr n xa xb xc)[(i : ℕ)]! (Ei i) := by
    intro i
    fin_cases i
    · exact rep_idA
    · exact ha
    · exact hb
    · exact rep_mulA ha hb
    · exact hc
    · exact rep_mulA ha hc
    · exact rep_mulA hb hc
    · exact rep_mulA (rep_mulA ha hb) hc
  have hsq : ∀ i : Fin 8, Ei i * Ei i = 1 := by
    intro i
    fin_cases i
    · exact mul_one 1
    · exact hia.1
    · exact hib.1
    · exact hiab.1
    · exact hic.1
    · exact hiac.1
    · exact hibc.1
    · exact hiabc.1
  have hiso : ∀ i : Fin 8, Ei i = 1 ∨ IsoI (Ei i) := by
    intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr hia
    · exact Or.inr hib
    · exact Or.inr hiab
    · exact Or.inr hic
    · exact Or.inr hiac
    · exact Or.inr hibc
    · exact Or.inr hiabc
  have hmemQ : ∀ i : Fin 8, Ei i ∈ Q := by
    intro i
    fin_cases i
    · exact Q.one_mem
    · exact haQ
    · exact hbQ
    · exact mul_mem haQ hbQ
    · exact hcQ
    · exact mul_mem haQ hcQ
    · exact mul_mem hbQ hcQ
    · exact mul_mem (mul_mem haQ hbQ) hcQ
  simp only [eightSubOK, Bool.and_eq_true] at h
  obtain ⟨hcl, hdist⟩ := h
  rw [nat_all_iff] at hcl hdist
  have hclosed : ∀ i j : Fin 8, ∃ k : Fin 8, Ei i * Ei j = Ei k := by
    intro i j
    have h1 := hcl i i.2
    rw [nat_all_iff] at h1
    have h2 := h1 j j.2
    rw [Array.any_eq_true'] at h2
    obtain ⟨z, hz, hzeq⟩ := h2
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hz
    have hk8 : k < 8 := by simpa [hsz] using hk
    refine ⟨⟨k, hk8⟩, ?_⟩
    have e2 := rep_of_eqA_left (rep_mulA (hrep i) (hrep j)) hzeq
    have e3 := hrep ⟨k, hk8⟩
    rw [getElem!_pos _ k hk] at e3
    exact Rep.unique e2 e3
  have hdist' : ∀ i j : Fin 8, (j : ℕ) < i → Ei i ≠ Ei j := by
    intro i j hji heq
    have h1 := hdist i i.2
    rw [nat_all_iff] at h1
    have h2 := h1 j hji
    rw [Bool.not_eq_true'] at h2
    have h3 : eqA n (eightArr n xa xb xc)[(i : ℕ)]! (eightArr n xa xb xc)[(j : ℕ)]! = true :=
      (eqA_iff (hrep i) (hrep j)).2 heq
    rw [h3] at h2
    exact absurd h2 (by simp)
  have hinj : Function.Injective Ei := by
    intro i j heq
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
    · exact hdist' j i hlt heq.symm
    · exact hdist' i j hlt heq
  let T : Subgroup (Perm (Fin n)) :=
    { carrier := {σ | ∃ i : Fin 8, σ = Ei i}
      mul_mem' := by
        rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
        obtain ⟨k, hk⟩ := hclosed i j
        exact ⟨k, hk⟩
      one_mem' := ⟨0, rfl⟩
      inv_mem' := by
        rintro _ ⟨i, rfl⟩
        exact ⟨i, inv_eq_of_mul_eq_one_right (hsq i)⟩ }
  refine ⟨T, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hmemQ i
  · have hbij : Function.Bijective (fun i : Fin 8 => (⟨Ei i, i, rfl⟩ : T)) := by
      constructor
      · intro i j heq
        exact hinj (congrArg Subtype.val heq)
      · rintro ⟨_, i, rfl⟩
        exact ⟨i, rfl⟩
    rw [← Nat.card_eq_of_bijective _ hbij]
    simp
  · rintro _ ⟨i, rfl⟩
    exact hiso i

theorem eight_of_eightOK (T : TableSpec n tab card) (h : eightOK n tab = true) :
    (∃ a ∈ P0 n, ∃ b ∈ P0 n, ∃ c ∈ P0 n, IsoI a ∧ IsoI b ∧ IsoI c ∧ Indep2 a b ∧ Indep3 a b c) ∧
    ∃ E : Subgroup (Perm (Fin n)), E ≤ P0 n ∧ Nat.card E = 8 ∧ ∀ e ∈ E, e = 1 ∨ IsoI e := by
  simp only [eightOK, Array.any_eq_true', Bool.and_eq_true] at h
  obtain ⟨xa, hxa, xb, hxb, ⟨h2c, h2i⟩, xc, hxc,
    ⟨⟨⟨⟨⟨h3ac, h3bc⟩, h3aci⟩, h3bci⟩, h3abci⟩, h8⟩⟩ := h
  obtain ⟨a, ha, hia, hxar⟩ := of_mem_isoArr T hxa
  obtain ⟨b, hb, hib, hxbr⟩ := of_mem_isoArr T hxb
  obtain ⟨c, hc, hic, hxcr⟩ := of_mem_isoArr T hxc
  have hiab := (isoA_iff (rep_mulA hxar hxbr)).1 h2i
  have hiac := (isoA_iff (rep_mulA hxar hxcr)).1 h3aci
  have hibc := (isoA_iff (rep_mulA hxbr hxcr)).1 h3bci
  have hiabc := (isoA_iff (rep_mulA (rep_mulA hxar hxbr) hxcr)).1 h3abci
  refine ⟨⟨a, ha, b, hb, c, hc, hia, hib, hic, ⟨(commA_iff hxar hxbr).1 h2c, hiab⟩,
    (commA_iff hxar hxcr).1 h3ac, (commA_iff hxbr hxcr).1 h3bc, hiac, hibc, hiabc⟩, ?_⟩
  exact exists_eightSub hxar hxbr hxcr ha hb hc hia hib hic hiab hiac hibc hiabc h8

theorem half_of_halfOK (T : TableSpec n tab card) (h : halfOK n tab = true) :
    ∃ t ∈ P0 n, IsoI t ∧ (∀ p ∈ P0 n, t * p = p * t) ∧
      ∃ s ∈ P0 n, DblI s ∧ s * t = t * s ∧ IsoI (s * t) := by
  simp only [halfOK, Array.any_eq_true', Bool.and_eq_true] at h
  obtain ⟨k, hk, hall, s, hs, ⟨hdbl, hcomm⟩, hiso⟩ := h
  rw [mem_isoIdx] at hk
  obtain ⟨hklt, hkiso⟩ := hk
  obtain ⟨t, ht, htr⟩ := T.mem tab[k] (Array.getElem_mem hklt)
  rw [getElem!_pos tab k hklt] at hkiso hall
  refine ⟨t, ht, (isoA_iff htr).1 hkiso, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, hx, hxp⟩ := T.surj p hp
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hx
    rw [nat_all_iff] at hall
    have := hall j hj
    rw [getElem!_pos tab j hj] at this
    exact (commA_iff htr hxp).1 this
  · obtain ⟨σ, hσ, hσr⟩ := T.mem s hs
    rw [getElem!_pos tab k hklt] at hcomm hiso
    exact ⟨σ, hσ, (dblA_iff hσr).1 hdbl, (commA_iff hσr htr).1 hcomm,
      (isoA_iff (rep_mulA hσr htr)).1 hiso⟩

end FromTable

structure SylowGood (n : ℕ) (Q : Subgroup (Perm (Fin n))) : Prop where
  nbr : ∀ a ∈ Q, IsoI a → ∃ b ∈ Q, IsoI b ∧ AdjI a b
  conn : ∀ a ∈ Q, ∀ b ∈ Q, IsoI a → IsoI b → Relation.ReflTransGen (AdjIn Q) a b
  rank : ∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, ∀ d ∈ Q, IsoI a → IsoI b → IsoI c → IsoI d →
    Indep2 a b → Indep3 a b c → ¬ Indep4 a b c d
  eight : ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q, IsoI a ∧ IsoI b ∧ IsoI c ∧ Indep2 a b ∧ Indep3 a b c
  eightSub : ∃ E : Subgroup (Perm (Fin n)), E ≤ Q ∧ Nat.card E = 8 ∧ ∀ e ∈ E, e = 1 ∨ IsoI e
  half : ∃ t ∈ Q, IsoI t ∧ (∀ p ∈ Q, t * p = p * t) ∧
    ∃ s ∈ Q, DblI s ∧ s * t = t * s ∧ IsoI (s * t)

theorem sylowGood_of_check [NeZero n] (hn : 8 ≤ n) (hn' : n ≤ 11) {card : ℕ} (hcard : 0 < card)
    (h : sylowCheck n card = true) : Nat.card (P0 n) = card ∧ SylowGood n (P0 n) := by
  simp only [sylowCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT, -⟩, hnbr⟩, hconn⟩, hrank⟩, h8⟩, hhalf⟩ := h
  have T := tableSpec_of_tableOK hn hn' hcard hT
  obtain ⟨h8a, h8b⟩ := eight_of_eightOK T h8
  exact ⟨T.card_eq, nbr_of_nbrOK T hnbr, conn_of_connOK T hconn,
    rank_of_rankOK T hrank, h8a, h8b, half_of_halfOK T hhalf⟩

@[expose] def conjSub (g : Perm (Fin n)) (Q : Subgroup (Perm (Fin n))) : Subgroup (Perm (Fin n)) :=
  Q.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {g x : Perm (Fin n)} {Q : Subgroup (Perm (Fin n))} :
    x ∈ conjSub g Q ↔ g⁻¹ * x * g ∈ Q := by
  rw [conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem conj_mem_conjSub {g x : Perm (Fin n)} {Q : Subgroup (Perm (Fin n))} (hx : x ∈ Q) :
    g * x * g⁻¹ ∈ conjSub g Q := by
  rw [mem_conjSub]
  simpa [mul_assoc] using hx

theorem isoI_conj {g σ : Perm (Fin n)} : IsoI (g * σ * g⁻¹) ↔ IsoI σ := by
  unfold IsoI
  have h1 : g * σ * g⁻¹ * (g * σ * g⁻¹) = g * (σ * σ) * g⁻¹ := by group
  rw [h1, card_support_conj]
  constructor
  · rintro ⟨h, h'⟩
    refine ⟨?_, h'⟩
    have : g * (σ * σ) * g⁻¹ = g * 1 * g⁻¹ := by rw [h]; group
    simpa using this
  · rintro ⟨h, h'⟩
    refine ⟨?_, h'⟩
    rw [h]
    group

theorem dblI_conj {g σ : Perm (Fin n)} : DblI (g * σ * g⁻¹) ↔ DblI σ := by
  unfold DblI
  have h1 : g * σ * g⁻¹ * (g * σ * g⁻¹) = g * (σ * σ) * g⁻¹ := by group
  rw [h1, card_support_conj]
  constructor
  · rintro ⟨h, h'⟩
    refine ⟨?_, h'⟩
    have : g * (σ * σ) * g⁻¹ = g * 1 * g⁻¹ := by rw [h]; group
    simpa using this
  · rintro ⟨h, h'⟩
    refine ⟨?_, h'⟩
    rw [h]
    group

theorem conj_mul_conj (g x y : Perm (Fin n)) :
    (g * x * g⁻¹) * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by
  group

theorem conj_comm_iff {g x y : Perm (Fin n)} :
    (g * x * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * x * g⁻¹) ↔ x * y = y * x := by
  rw [conj_mul_conj, conj_mul_conj]
  constructor
  · intro h
    exact mul_left_cancel (mul_right_cancel h)
  · intro h
    rw [h]

theorem conj_ne_iff {g x y : Perm (Fin n)} : g * x * g⁻¹ ≠ g * y * g⁻¹ ↔ x ≠ y := by
  simp [mul_left_inj, mul_right_inj]

theorem adjI_conj {g x y : Perm (Fin n)} : AdjI (g * x * g⁻¹) (g * y * g⁻¹) ↔ AdjI x y := by
  unfold AdjI
  simp only [conj_ne_iff, conj_mul_conj, isoI_conj, mul_left_inj, mul_right_inj]

theorem indep2_conj {g x y : Perm (Fin n)} :
    Indep2 (g * x * g⁻¹) (g * y * g⁻¹) ↔ Indep2 x y := by
  unfold Indep2
  simp only [conj_mul_conj, isoI_conj, mul_left_inj, mul_right_inj]

theorem indep3_conj {g x y z : Perm (Fin n)} :
    Indep3 (g * x * g⁻¹) (g * y * g⁻¹) (g * z * g⁻¹) ↔ Indep3 x y z := by
  unfold Indep3
  simp only [conj_mul_conj, isoI_conj, mul_left_inj, mul_right_inj]

theorem indep4_conj {g x y z w : Perm (Fin n)} :
    Indep4 (g * x * g⁻¹) (g * y * g⁻¹) (g * z * g⁻¹) (g * w * g⁻¹) ↔ Indep4 x y z w := by
  unfold Indep4
  simp only [conj_mul_conj, isoI_conj, mul_left_inj, mul_right_inj]

theorem exists_conj_mem {g x : Perm (Fin n)} {Q : Subgroup (Perm (Fin n))} :
    x ∈ conjSub g Q ↔ ∃ y ∈ Q, x = g * y * g⁻¹ := by
  constructor
  · intro h
    exact ⟨g⁻¹ * x * g, mem_conjSub.1 h, by group⟩
  · rintro ⟨y, hy, rfl⟩
    exact conj_mem_conjSub hy

theorem SylowGood.conj {Q : Subgroup (Perm (Fin n))} (h : SylowGood n Q) (g : Perm (Fin n)) :
    SylowGood n (conjSub g Q) where
  nbr := by
    intro a ha hia
    obtain ⟨a₀, ha₀, rfl⟩ := exists_conj_mem.1 ha
    obtain ⟨b₀, hb₀, hib₀, hab⟩ := h.nbr a₀ ha₀ (isoI_conj.1 hia)
    exact ⟨g * b₀ * g⁻¹, conj_mem_conjSub hb₀, isoI_conj.2 hib₀, adjI_conj.2 hab⟩
  conn := by
    intro a ha b hb hia hib
    obtain ⟨a₀, ha₀, rfl⟩ := exists_conj_mem.1 ha
    obtain ⟨b₀, hb₀, rfl⟩ := exists_conj_mem.1 hb
    have hr := h.conn a₀ ha₀ b₀ hb₀ (isoI_conj.1 hia) (isoI_conj.1 hib)
    refine (Relation.ReflTransGen.lift (fun x : Perm (Fin n) => g * x * g⁻¹) ?_) a₀ b₀ hr
    intro x y hxy
    obtain ⟨hx, hy, hix, hiy, hadj⟩ := hxy
    exact ⟨conj_mem_conjSub hx, conj_mem_conjSub hy, isoI_conj.2 hix, isoI_conj.2 hiy,
      adjI_conj.2 hadj⟩
  rank := by
    intro a ha b hb c hc d hd hia hib hic hid h2 h3 h4
    obtain ⟨a₀, ha₀, rfl⟩ := exists_conj_mem.1 ha
    obtain ⟨b₀, hb₀, rfl⟩ := exists_conj_mem.1 hb
    obtain ⟨c₀, hc₀, rfl⟩ := exists_conj_mem.1 hc
    obtain ⟨d₀, hd₀, rfl⟩ := exists_conj_mem.1 hd
    exact h.rank a₀ ha₀ b₀ hb₀ c₀ hc₀ d₀ hd₀ (isoI_conj.1 hia) (isoI_conj.1 hib)
      (isoI_conj.1 hic) (isoI_conj.1 hid) (indep2_conj.1 h2) (indep3_conj.1 h3)
      (indep4_conj.1 h4)
  eight := by
    obtain ⟨a, ha, b, hb, c, hc, hia, hib, hic, h2, h3⟩ := h.eight
    exact ⟨g * a * g⁻¹, conj_mem_conjSub ha, g * b * g⁻¹, conj_mem_conjSub hb, g * c * g⁻¹,
      conj_mem_conjSub hc, isoI_conj.2 hia, isoI_conj.2 hib, isoI_conj.2 hic, indep2_conj.2 h2,
      indep3_conj.2 h3⟩
  eightSub := by
    obtain ⟨E, hEQ, hEcard, hEiso⟩ := h.eightSub
    refine ⟨conjSub g E, Subgroup.map_mono hEQ, ?_, ?_⟩
    · rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hEcard
    · intro e he
      obtain ⟨e₀, he₀, rfl⟩ := exists_conj_mem.1 he
      rcases hEiso e₀ he₀ with h1 | h1
      · left
        rw [h1]
        group
      · exact Or.inr (isoI_conj.2 h1)
  half := by
    obtain ⟨t, ht, hit, htc, s, hs, hds, hst, hist⟩ := h.half
    refine ⟨g * t * g⁻¹, conj_mem_conjSub ht, isoI_conj.2 hit, ?_, g * s * g⁻¹,
      conj_mem_conjSub hs, dblI_conj.2 hds, ?_, ?_⟩
    · intro p hp
      obtain ⟨p₀, hp₀, rfl⟩ := exists_conj_mem.1 hp
      rw [conj_mul_conj, conj_mul_conj, htc p₀ hp₀]
    · rw [conj_mul_conj, conj_mul_conj, hst]
    · rw [conj_mul_conj]
      exact isoI_conj.2 hist

@[expose] def Wit (e w : Perm (Fin n)) : Prop := (w * e * w⁻¹) * e ≠ e * (w * e * w⁻¹)

@[expose] def BalanceGood (n rmin : ℕ) (Q : Subgroup (Perm (Fin n))) : Prop :=
  ∀ e : Perm (Fin n), e ≠ 1 → ∀ r : ℕ, r.Prime → rmin ≤ r → e ^ r = 1 →
    ∃ w₁ ∈ Q, ∃ w₂ ∈ Q, Wit e w₁ ∧ Wit e w₂ ∧ Wit e (w₁ * w₂)

theorem BalanceGood.mono {Q : Subgroup (Perm (Fin n))} {rmin rmin' : ℕ} (h : BalanceGood n rmin Q)
    (hle : rmin ≤ rmin') : BalanceGood n rmin' Q :=
  fun e he r hr hrmin her => h e he r hr (hle.trans hrmin) her

theorem wit_conj {g e w : Perm (Fin n)} : Wit (g * e * g⁻¹) (g * w * g⁻¹) ↔ Wit e w := by
  unfold Wit
  have h1 : (g * w * g⁻¹) * (g * e * g⁻¹) * (g * w * g⁻¹)⁻¹ = g * (w * e * w⁻¹) * g⁻¹ := by
    group
  rw [h1, conj_mul_conj, conj_mul_conj, Ne, Ne, mul_left_inj, mul_right_inj]

theorem BalanceGood.conj {Q : Subgroup (Perm (Fin n))} {rmin : ℕ} (h : BalanceGood n rmin Q)
    (g : Perm (Fin n)) : BalanceGood n rmin (conjSub g Q) := by
  intro e he r hr hrmin her
  obtain ⟨e₀, rfl⟩ : ∃ e₀, e = g * e₀ * g⁻¹ := ⟨g⁻¹ * e * g, by group⟩
  have he₀ : e₀ ≠ 1 := by
    rintro rfl
    exact he (by group)
  have her₀ : e₀ ^ r = 1 := by
    rw [conj_pow] at her
    have : g * e₀ ^ r * g⁻¹ = g * 1 * g⁻¹ := by rw [her]; group
    simpa using this
  obtain ⟨w₁, hw₁, w₂, hw₂, h1, h2, h12⟩ := h e₀ he₀ r hr hrmin her₀
  refine ⟨g * w₁ * g⁻¹, conj_mem_conjSub hw₁, g * w₂ * g⁻¹, conj_mem_conjSub hw₂,
    wit_conj.2 h1, wit_conj.2 h2, ?_⟩
  rw [conj_mul_conj]
  exact wit_conj.2 h12

end CFSG.OddStandard.Solomon75.AhatData
