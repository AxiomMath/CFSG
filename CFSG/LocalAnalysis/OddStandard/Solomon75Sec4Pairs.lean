module

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
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
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

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup

@[expose] def pairEmb (n k : ℕ) (h : 2 * k ≤ n) : Fin k × Fin 2 ↪ Fin n where
  toFun p := ⟨2 * p.1.val + p.2.val, by have := p.1.2; have := p.2.2; omega⟩
  inj' := by
    rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ h
    simp only [Fin.mk.injEq] at h
    have : i = i' := by omega
    have : j = j' := by omega
    simp_all

@[expose] def swapSecond (k : ℕ) : Perm (Fin k × Fin 2) :=
  Equiv.prodCongr (Equiv.refl (Fin k)) (Equiv.swap (0 : Fin 2) 1)

noncomputable def stdInv (n k : ℕ) (h : 2 * k ≤ n) : Perm (Fin n) :=
  (swapSecond k).viaEmbedding (pairEmb n k h)

@[expose] def permProdOne (k : ℕ) : Perm (Fin k) →* Perm (Fin k × Fin 2) where
  toFun τ := Equiv.prodCongr τ (Equiv.refl (Fin 2))
  map_one' := by ext <;> rfl
  map_mul' τ τ' := by ext <;> rfl

noncomputable def pairHom (n k : ℕ) (h : 2 * k ≤ n) : Perm (Fin k) →* Perm (Fin n) :=
  (Equiv.Perm.viaEmbeddingHom (pairEmb n k h)).comp (permProdOne k)

@[expose] def fixEmb (n k : ℕ) (h : 2 * k ≤ n) : Fin (n - 2 * k) ↪ Fin n where
  toFun i := ⟨2 * k + i.val, by have := i.2; omega⟩
  inj' := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    simp only [Fin.mk.injEq] at h
    simp only [Fin.mk.injEq]
    omega

@[expose] def altFix (n k : ℕ) (h : 2 * k ≤ n) : Subgroup (Perm (Fin n)) where
  carrier := {g | (∀ x ∈ Set.range (pairEmb n k h), g x = x) ∧ sign g = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [Perm.mul_apply, hb x hx, ha x hx]
    · rw [Perm.sign_mul, ha', hb', mul_one]
  one_mem' := ⟨fun x _ => rfl, Perm.sign_one⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · have := ha x hx
      rw [Perm.inv_eq_iff_eq]
      exact this.symm
    · rw [Perm.sign_inv, ha']

@[expose] def dblPair (n k : ℕ) (h : 2 * k ≤ n) (i l : Fin k) : Perm (Fin n) :=
  swap (pairEmb n k h (i, 0)) (pairEmb n k h (i, 1)) *
    swap (pairEmb n k h (l, 0)) (pairEmb n k h (l, 1))

variable {n k : ℕ} {h : 2 * k ≤ n}

theorem swap_zero_one_apply_ne (j : Fin 2) : Equiv.swap (0 : Fin 2) 1 j ≠ j := by
  fin_cases j <;> simp

theorem cycleType_eq_replicate_of_involution {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (h2 : σ * σ = 1) (hk : σ.support.card = 2 * k) :
    σ.cycleType = Multiset.replicate k 2 := by
  have hpow : σ ^ 2 = 1 := by rw [pow_two, h2]
  have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one hpow
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hrep, Multiset.sum_replicate, hk, smul_eq_mul] at hsum
  have : σ.cycleType.card = k := by omega
  rw [hrep, this]

theorem stdInv_apply_pair (i : Fin k) (j : Fin 2) :
    stdInv n k h (pairEmb n k h (i, j)) = pairEmb n k h (i, Equiv.swap 0 1 j) :=
  Equiv.Perm.viaEmbedding_apply (swapSecond k) (pairEmb n k h) (i, j)

theorem stdInv_apply_of_notMem (x : Fin n) (hx : x ∉ Set.range (pairEmb n k h)) :
    stdInv n k h x = x :=
  Equiv.Perm.viaEmbedding_apply_of_notMem (swapSecond k) (pairEmb n k h) x hx

theorem stdInv_mul_self : stdInv n k h * stdInv n k h = 1 := by
  refine Equiv.Perm.ext fun x => ?_
  by_cases hx : x ∈ Set.range (pairEmb n k h)
  · obtain ⟨⟨i, j⟩, rfl⟩ := hx
    simp [stdInv_apply_pair]
  · simp [stdInv_apply_of_notMem x hx]

theorem stdInv_ne_self_iff (x : Fin n) :
    stdInv n k h x ≠ x ↔ x ∈ Set.range (pairEmb n k h) := by
  constructor
  · intro hx
    by_contra hne
    exact hx (stdInv_apply_of_notMem x hne)
  · rintro ⟨⟨i, j⟩, rfl⟩ heq
    rw [stdInv_apply_pair] at heq
    exact swap_zero_one_apply_ne j (congrArg Prod.snd ((pairEmb n k h).injective heq))

theorem card_support_stdInv : (stdInv n k h).support.card = 2 * k := by
  have h1 : (stdInv n k h).support = Finset.univ.map (pairEmb n k h) := by
    ext x
    rw [Equiv.Perm.mem_support, stdInv_ne_self_iff, Finset.mem_map]
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p, Finset.mem_univ _, hp⟩
    · rintro ⟨p, -, hp⟩
      exact ⟨p, hp⟩
  rw [h1, Finset.card_map, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, mul_comm]

theorem stdInv_cycleType : (stdInv n k h).cycleType = Multiset.replicate k 2 :=
  cycleType_eq_replicate_of_involution stdInv_mul_self card_support_stdInv

theorem pairHom_apply_pair (τ : Perm (Fin k)) (i : Fin k) (j : Fin 2) :
    pairHom n k h τ (pairEmb n k h (i, j)) = pairEmb n k h (τ i, j) :=
  Equiv.Perm.viaEmbedding_apply (permProdOne k τ) (pairEmb n k h) (i, j)

theorem pairHom_apply_of_notMem (τ : Perm (Fin k)) (x : Fin n)
    (hx : x ∉ Set.range (pairEmb n k h)) : pairHom n k h τ x = x :=
  Equiv.Perm.viaEmbedding_apply_of_notMem (permProdOne k τ) (pairEmb n k h) x hx

theorem pairHom_comm_stdInv (τ : Perm (Fin k)) :
    pairHom n k h τ * stdInv n k h = stdInv n k h * pairHom n k h τ := by
  refine Equiv.Perm.ext fun x => ?_
  by_cases hx : x ∈ Set.range (pairEmb n k h)
  · obtain ⟨⟨i, j⟩, rfl⟩ := hx
    simp [pairHom_apply_pair, stdInv_apply_pair]
  · simp [pairHom_apply_of_notMem τ x hx, stdInv_apply_of_notMem x hx]

theorem sign_pairHom (τ : Perm (Fin k)) : sign (pairHom n k h τ) = 1 := by
  have h1 : pairHom n k h τ = (permProdOne k τ).viaEmbedding (pairEmb n k h) := rfl
  have h2 : permProdOne k τ = Equiv.prodCongrLeft (fun _ : Fin 2 => τ) := by
    refine Equiv.Perm.ext fun ⟨i, j⟩ => ?_
    rfl
  rw [h1, Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain, h2,
    Equiv.Perm.sign_prodCongrLeft]
  simp [Finset.prod_const, sq]

theorem pairHom_injective : Function.Injective (pairHom n k h) := by
  intro τ τ' hττ'
  refine Equiv.Perm.ext fun i => ?_
  have := congrArg (fun g : Perm (Fin n) => g (pairEmb n k h (i, 0))) hττ'
  simp only [pairHom_apply_pair] at this
  exact congrArg Prod.fst ((pairEmb n k h).injective this)

theorem stdInv_apply_eq_self_iff (x : Fin n) :
    stdInv n k h x = x ↔ x ∉ Set.range (pairEmb n k h) := by
  rw [← stdInv_ne_self_iff, not_not]

theorem exists_conj_stdInv {σ : Perm (Fin n)} (hσ : σ * σ = 1) (hk : σ.support.card = 2 * k) :
    ∃ g : Perm (Fin n), g * σ * g⁻¹ = stdInv n k h := by
  have hc : σ.cycleType = (stdInv n k h).cycleType := by
    rw [stdInv_cycleType, cycleType_eq_replicate_of_involution hσ hk]
  exact isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr hc)

theorem pairEmb_ne_fixEmb (p : Fin k × Fin 2) (i : Fin (n - 2 * k)) :
    pairEmb n k h p ≠ fixEmb n k h i := by
  intro heq
  have h1 := congrArg Fin.val heq
  have h2 := p.1.2
  have h3 := p.2.2
  simp only [pairEmb, fixEmb, Function.Embedding.coeFn_mk] at h1
  omega

theorem mem_range_pairEmb_or_fixEmb (x : Fin n) :
    x ∈ Set.range (pairEmb n k h) ∨ x ∈ Set.range (fixEmb n k h) := by
  have hx := x.2
  by_cases hxk : x.val < 2 * k
  · left
    refine ⟨(⟨x.val / 2, by omega⟩, ⟨x.val % 2, by omega⟩), ?_⟩
    ext
    simp only [pairEmb, Function.Embedding.coeFn_mk]
    omega
  · right
    refine ⟨⟨x.val - 2 * k, by omega⟩, ?_⟩
    ext
    simp only [fixEmb, Function.Embedding.coeFn_mk]
    omega

theorem mem_range_pairEmb_of_comm {g : Perm (Fin n)}
    (hg : g * stdInv n k h = stdInv n k h * g) {y : Fin n}
    (hy : y ∈ Set.range (pairEmb n k h)) : g y ∈ Set.range (pairEmb n k h) := by
  by_contra hcon
  have h1 : stdInv n k h (g y) = g y := stdInv_apply_of_notMem _ hcon
  have h2 : g (stdInv n k h y) = stdInv n k h (g y) := by
    simpa only [Perm.mul_apply] using congrArg (fun f => f y) hg
  rw [h1] at h2
  exact (stdInv_apply_eq_self_iff y).mp (g.injective h2) hy

theorem altFix_comm_stdInv {x : Perm (Fin n)} (hx : x ∈ altFix n k h) :
    x * stdInv n k h = stdInv n k h * x := by
  obtain ⟨hfix, -⟩ := hx
  ext y
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hy : y ∈ Set.range (pairEmb n k h)
  · obtain ⟨⟨i, j⟩, rfl⟩ := hy
    have h1 : x (pairEmb n k h (i, Equiv.swap 0 1 j)) = pairEmb n k h (i, Equiv.swap 0 1 j) :=
      hfix _ ⟨_, rfl⟩
    have h2 : x (pairEmb n k h (i, j)) = pairEmb n k h (i, j) := hfix _ ⟨_, rfl⟩
    rw [stdInv_apply_pair, h1, h2, stdInv_apply_pair]
  · have hxy : x y ∉ Set.range (pairEmb n k h) := by
      intro hxy
      have h1 : x y = y := x.injective (hfix _ hxy)
      exact hy (h1 ▸ hxy)
    rw [stdInv_apply_of_notMem y hy, stdInv_apply_of_notMem _ hxy]

theorem altFix_le_alternatingGroup : altFix n k h ≤ alternatingGroup (Fin n) :=
  fun _ hg => Perm.mem_alternatingGroup.mpr hg.2

theorem altFix_conj_mem {g x : Perm (Fin n)} (hg : g * stdInv n k h = stdInv n k h * g)
    (hx : x ∈ altFix n k h) : g * x * g⁻¹ ∈ altFix n k h := by
  obtain ⟨hfix, hsign⟩ := hx
  have hg' : g⁻¹ * stdInv n k h = stdInv n k h * g⁻¹ := (show Commute g _ from hg).inv_left
  refine ⟨fun y hy => ?_, ?_⟩
  · rw [Perm.mul_apply, Perm.mul_apply, hfix _ (mem_range_pairEmb_of_comm hg' hy)]
    exact g.apply_symm_apply y
  · rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hsign, mul_one, Int.units_mul_self]

theorem map_alternatingGroup_eq_altFix :
    (alternatingGroup (Fin (n - 2 * k))).map (Equiv.Perm.viaEmbeddingHom (fixEmb n k h)) =
      altFix n k h := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    rw [Equiv.Perm.viaEmbeddingHom_apply]
    refine ⟨fun x hx => ?_, ?_⟩
    · refine Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ ?_
      rintro ⟨i, rfl⟩
      obtain ⟨p, hp⟩ := hx
      exact pairEmb_ne_fixEmb p i hp
    · rw [Equiv.Perm.viaEmbedding, Perm.sign_extendDomain]
      exact Perm.mem_alternatingGroup.mp hτ
  · rintro ⟨hfix, hsign⟩
    have hmem : ∀ i, ∃ j, fixEmb n k h j = g (fixEmb n k h i) := by
      intro i
      rcases mem_range_pairEmb_or_fixEmb (h := h) (g (fixEmb n k h i)) with ⟨p, hp⟩ | hr
      · have h1 : g (fixEmb n k h i) = fixEmb n k h i := g.injective (hfix _ ⟨p, hp⟩)
        exact absurd (hp.trans h1) (pairEmb_ne_fixEmb p i)
      · exact hr
    choose f hf using hmem
    have hinj : Function.Injective f := by
      intro i i' hii
      apply (fixEmb n k h).injective
      apply g.injective
      rw [← hf i, ← hf i', hii]
    let τ : Perm (Fin (n - 2 * k)) := Equiv.ofBijective f hinj.bijective_of_finite
    have hτ : ∀ i, fixEmb n k h (τ i) = g (fixEmb n k h i) := hf
    have hgτ : Equiv.Perm.viaEmbedding τ (fixEmb n k h) = g := by
      ext x
      rcases mem_range_pairEmb_or_fixEmb (h := h) x with ⟨p, rfl⟩ | ⟨i, rfl⟩
      · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ ?_, hfix _ ⟨p, rfl⟩]
        rintro ⟨i, hi⟩
        exact pairEmb_ne_fixEmb p i hi.symm
      · rw [Equiv.Perm.viaEmbedding_apply, hτ]
    refine ⟨τ, ?_, hgτ⟩
    rw [Perm.mem_alternatingGroup]
    have := congrArg Perm.sign hgτ
    rw [Equiv.Perm.viaEmbedding, Perm.sign_extendDomain] at this
    rw [this, hsign]

theorem perfect_hom_eq_one {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    [Group.IsSolvable H] (f : G →* H) (x : G) : f x = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    by_contra hns
    have : Nontrivial f.range := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  exact congrArg Subtype.val (Subsingleton.elim (⟨f x, x, rfl⟩ : f.range) 1)

theorem sign_eq_one_of_perfect {α : Type*} [Fintype α] [DecidableEq α] {P : Subgroup (Perm α)}
    (hP : ⁅P, P⁆ = P) {g : Perm α} (hg : g ∈ P) : sign g = 1 := by
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  exact perfect_hom_eq_one (sign.comp P.subtype) ⟨g, hg⟩

theorem perfect_fix_of_small {α : Type*} [Fintype α] [DecidableEq α] {P : Subgroup (Perm α)}
    (hP : ⁅P, P⁆ = P) (s : Finset α) (hs : s.card ≤ 4)
    (hinv : ∀ g ∈ P, ∀ x ∈ s, g x ∈ s) {g : Perm α} (hg : g ∈ P) {x : α} (hx : x ∈ s) :
    g x = x := by
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  have hmem : ∀ g ∈ P, ∀ x, g x ∈ s ↔ x ∈ s := fun g hg x =>
    ⟨fun hgx => by simpa using hinv g⁻¹ (P.inv_mem hg) _ hgx, hinv g hg x⟩
  let ρ : P →* Perm s :=
    MonoidHom.mk' (fun g => (g : Perm α).subtypePerm (hmem g g.2)) fun a b => by
      ext; rfl
  have : Group.IsSolvable (Perm s) := Equiv.Perm.isSolvable (by simpa using hs)
  have h1 := perfect_hom_eq_one ρ ⟨g, hg⟩
  have h2 := congrArg (fun f : Perm s => (f ⟨x, hx⟩ : α)) h1
  simpa [ρ] using h2

theorem perfect_le_altFix_of_preserves {P : Subgroup (Perm (Fin n))} (hP : ⁅P, P⁆ = P)
    (hpres : ∀ g ∈ P, ∀ (i : Fin k) (j : Fin 2), ∃ j' : Fin 2,
      g (pairEmb n k h (i, j)) = pairEmb n k h (i, j')) : P ≤ altFix n k h := by
  intro g hg
  refine ⟨?_, sign_eq_one_of_perfect hP hg⟩
  rintro x ⟨⟨i, j⟩, rfl⟩
  refine perfect_fix_of_small hP {pairEmb n k h (i, 0), pairEmb n k h (i, 1)}
    (Finset.card_le_two.trans (by norm_num)) ?_ hg (by fin_cases j <;> simp)
  intro g' hg' y hy
  have hy' : y = pairEmb n k h (i, 0) ∨ y = pairEmb n k h (i, 1) := by simpa using hy
  rcases hy' with rfl | rfl
  · obtain ⟨j', hj'⟩ := hpres g' hg' i 0
    rw [hj']
    fin_cases j' <;> simp
  · obtain ⟨j', hj'⟩ := hpres g' hg' i 1
    rw [hj']
    fin_cases j' <;> simp

theorem dblPair_apply_pair_of_ne {i l p : Fin k} (hpi : p ≠ i) (hpl : p ≠ l) (q : Fin 2) :
    dblPair n k h i l (pairEmb n k h (p, q)) = pairEmb n k h (p, q) := by
  have hne : ∀ (a : Fin k) (b : Fin 2), p ≠ a →
      pairEmb n k h (p, q) ≠ pairEmb n k h (a, b) :=
    fun a b hpa e => hpa (congrArg Prod.fst ((pairEmb n k h).injective e))
  unfold dblPair
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne (hne l 0 hpl) (hne l 1 hpl),
    swap_apply_of_ne_of_ne (hne i 0 hpi) (hne i 1 hpi)]

theorem dblPair_apply_pair_ne_self {i l : Fin k} (hil : i ≠ l) (q : Fin 2) :
    dblPair n k h i l (pairEmb n k h (i, q)) ≠ pairEmb n k h (i, q) := by
  have hne : ∀ b : Fin 2, pairEmb n k h (i, q) ≠ pairEmb n k h (l, b) :=
    fun b e => hil (congrArg Prod.fst ((pairEmb n k h).injective e))
  unfold dblPair
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne (hne 0) (hne 1)]
  fin_cases q
  · simp
  · simp

theorem preserves_pairs_of_comm_dbl (hk : 3 ≤ k) {g : Perm (Fin n)}
    (hσ : g * stdInv n k h = stdInv n k h * g)
    (hδ : ∀ i l : Fin k, i ≠ l → g * dblPair n k h i l = dblPair n k h i l * g)
    (i : Fin k) (j : Fin 2) : ∃ j' : Fin 2, g (pairEmb n k h (i, j)) = pairEmb n k h (i, j') := by
  have hx : pairEmb n k h (i, j) ∈ Set.range (pairEmb n k h) := ⟨(i, j), rfl⟩
  have hrange : g (pairEmb n k h (i, j)) ∈ Set.range (pairEmb n k h) := by
    by_contra hnot
    have h1 := (stdInv_apply_eq_self_iff (h := h) (g (pairEmb n k h (i, j)))).2 hnot
    have h2 : g (stdInv n k h (pairEmb n k h (i, j))) = g (pairEmb n k h (i, j)) := by
      have := congrArg (fun f : Perm (Fin n) => f (pairEmb n k h (i, j))) hσ
      simp only [Perm.mul_apply] at this
      rw [this]
      exact h1
    exact ((stdInv_apply_eq_self_iff (h := h) _).1 (g.injective h2)) hx
  obtain ⟨⟨p, q⟩, hpq⟩ := hrange
  have hcard : 1 < (Finset.univ.erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨l, hl, l', hl', hll'⟩ := Finset.one_lt_card.1 hcard
  have key : ∀ l : Fin k, l ≠ i → p = i ∨ p = l := by
    intro l hli
    by_contra hcon
    obtain ⟨hcon1, hcon2⟩ := not_or.1 hcon
    have hfix := dblPair_apply_pair_of_ne (h := h) (i := i) (l := l) hcon1 hcon2 q
    have hcomm := congrArg (fun f : Perm (Fin n) => f (pairEmb n k h (i, j)))
      (hδ i l (Ne.symm hli))
    simp only [Perm.mul_apply] at hcomm
    rw [← hpq, hfix, hpq] at hcomm
    exact dblPair_apply_pair_ne_self (h := h) (Ne.symm hli) j (g.injective hcomm)
  have hp : p = i := by
    rcases key l (Finset.mem_erase.1 hl).1 with h1 | h1
    · exact h1
    · rcases key l' (Finset.mem_erase.1 hl').1 with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hll'
  exact ⟨q, by rw [← hpq, hp]⟩

theorem perfect_le_altFix_of_small (hk : k ≤ 2) {P : Subgroup (Perm (Fin n))} (hP : ⁅P, P⁆ = P)
    (hσ : ∀ g ∈ P, g * stdInv n k h = stdInv n k h * g) : P ≤ altFix n k h := by
  intro g hg
  refine ⟨fun x hx => ?_, sign_eq_one_of_perfect hP hg⟩
  have hxs : x ∈ (stdInv n k h).support := by
    rw [Perm.mem_support]
    exact fun h' => ((stdInv_apply_eq_self_iff x).1 h') hx
  refine perfect_fix_of_small hP (stdInv n k h).support ?_ ?_ hg hxs
  · rw [card_support_stdInv]
    omega
  · intro g' hg' y hy
    exact (Perm.mem_support_iff_of_commute (hσ g' hg') y).2 hy

section InvSwap

@[expose] def invSwapGrp {α : Type*} (σ : Perm α) (hσ : σ * σ = 1) : Subgroup (Perm α) where
  carrier := {g | ∀ x, g x = x ∨ g x = σ x}
  mul_mem' := by
    intro a b ha hb x
    have hσσ : ∀ y, σ (σ y) = y := fun y => by
      have := congrArg (fun p : Perm α => p y) hσ
      simpa using this
    rw [Perm.mul_apply]
    rcases hb x with h | h
    · rw [h]; exact ha x
    · rw [h]
      rcases ha (σ x) with h' | h'
      · exact Or.inr h'
      · exact Or.inl (by rw [h', hσσ])
  one_mem' := fun x => Or.inl rfl
  inv_mem' := by
    intro a ha x
    have hσσ : ∀ y, σ (σ y) = y := fun y => by
      have := congrArg (fun p : Perm α => p y) hσ
      simpa using this
    set y := a⁻¹ x with hy
    have hxy : a y = x := by simp [hy]
    rcases ha y with h | h
    · left
      rw [← hxy, h]
    · right
      rw [h] at hxy
      rw [← hxy, hσσ]

variable {α : Type*} {σ : Perm α} (hσ : σ * σ = 1)

include hσ in
theorem invSwapGrp_comm {g : Perm α} (hg : g ∈ invSwapGrp σ hσ) : g * σ = σ * g := by
  have hσσ : ∀ y, σ (σ y) = y := fun y => by
    have := congrArg (fun p : Perm α => p y) hσ
    simpa using this
  ext x
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hx : σ x = x
  · rcases hg x with h | h <;> simp [h, hx]
  · rcases hg x with h | h
    · rw [h]
      rcases hg (σ x) with h' | h'
      · exact h'
      · exfalso
        have : g (σ x) = g x := by rw [h', hσσ, h]
        exact hx (g.injective this)
    · rw [h, hσσ]
      rcases hg (σ x) with h' | h'
      · exfalso
        have : g (σ x) = g x := by rw [h', h]
        exact hx (g.injective this)
      · rw [h', hσσ]

include hσ in
theorem invSwapGrp_mul_self {g : Perm α} (hg : g ∈ invSwapGrp σ hσ) : g * g = 1 := by
  have hcomm := invSwapGrp_comm hσ hg
  have hσσ : ∀ y, σ (σ y) = y := fun y => by
    have := congrArg (fun p : Perm α => p y) hσ
    simpa using this
  ext x
  rw [Perm.mul_apply, Perm.coe_one, id_eq]
  rcases hg x with h | h
  · rw [h, h]
  · have : g (σ x) = σ (g x) := by simpa using congrArg (fun p : Perm α => p x) hcomm
    rw [h, this, h, hσσ]

include hσ in
theorem invSwapGrp_conj_mem {g e : Perm α} (hg : g * σ = σ * g) (he : e ∈ invSwapGrp σ hσ) :
    g * e * g⁻¹ ∈ invSwapGrp σ hσ := by
  intro y
  set x := g⁻¹ y with hx
  have hxy : g x = y := by simp [hx]
  have hgσ : g (σ x) = σ y := by
    have := congrArg (fun p : Perm α => p x) hg
    simp only [Perm.mul_apply] at this
    rw [this, hxy]
  rw [Perm.mul_apply, Perm.mul_apply, ← hx]
  rcases he x with h | h
  · left
    rw [h, hxy]
  · right
    rw [h, hgσ]

end InvSwap

section InvSwapPairs

variable {n k : ℕ} {h : 2 * k ≤ n}

theorem swapPair_mem_invSwapGrp (i : Fin k) :
    swap (pairEmb n k h (i, 0)) (pairEmb n k h (i, 1)) ∈
      invSwapGrp (stdInv n k h) stdInv_mul_self := by
  intro x
  by_cases h0 : x = pairEmb n k h (i, 0)
  · right
    rw [h0, swap_apply_left, stdInv_apply_pair]
    rfl
  by_cases h1 : x = pairEmb n k h (i, 1)
  · right
    rw [h1, swap_apply_right, stdInv_apply_pair]
    rfl
  · left
    exact swap_apply_of_ne_of_ne h0 h1

theorem dblPair_mem_invSwapGrp (i l : Fin k) :
    dblPair n k h i l ∈ invSwapGrp (stdInv n k h) stdInv_mul_self :=
  Subgroup.mul_mem _ (swapPair_mem_invSwapGrp i) (swapPair_mem_invSwapGrp l)

end InvSwapPairs

end CFSG.OddStandard.Solomon75
