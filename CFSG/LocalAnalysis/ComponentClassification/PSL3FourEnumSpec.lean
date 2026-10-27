module

public import Certificates.Data.CFSGNative.PSL3Four.Basic
public import CFSG.Perm.OrbitTree
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Action.Concrete
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.ComponentClassification.PSL3Four

open CFSG.PSL3Four CFSG.PSL3Four.Native
open scoped commutatorElement

@[expose] def TabRep {n : ℕ} (t : Tab) (g : Equiv.Perm (Fin n)) : Prop :=
  t.size = n ∧ ∀ i : Fin n, t[i.val]! = (g i : ℕ)

namespace TabRep

variable {n : ℕ} {t t' s : Tab} {g g' h : Equiv.Perm (Fin n)}

theorem apply (ht : TabRep t g) (i : Fin n) : t[i.val]! = (g i : ℕ) := ht.2 i

theorem tab_eq (ht : TabRep t g) (ht' : TabRep t' g) : t = t' := by
  apply Array.ext (ht.1.trans ht'.1.symm)
  intro i hi hi'
  have hin : i < n := ht.1 ▸ hi
  have e := (ht.apply ⟨i, hin⟩).trans (ht'.apply ⟨i, hin⟩).symm
  rwa [getElem!_pos t i hi, getElem!_pos t' i hi'] at e

theorem perm_eq (ht : TabRep t g) (ht' : TabRep t g') : g = g' :=
  Equiv.ext fun i => Fin.ext ((ht.apply i).symm.trans (ht'.apply i))

theorem eq_iff (ht : TabRep t g) (ht' : TabRep t' g') : t = t' ↔ g = g' := by
  constructor
  · rintro rfl
    exact ht.perm_eq ht'
  · rintro rfl
    exact ht.tab_eq ht'

theorem beq_iff (ht : TabRep t g) (ht' : TabRep t' g') : (t == t') = true ↔ g = g' := by
  rw [beq_iff_eq]
  exact ht.eq_iff ht'

theorem comp_getElem! (p q : Tab) (i : Fin n) :
    (Native.comp n p q)[i.val]! = p[q[i.val]!]! := by
  show (Array.ofFn (n := n) fun i => p[q[i.val]!]!)[i.val]! = p[q[i.val]!]!
  rw [getElem!_pos _ _ (by simp), Array.getElem_ofFn]

theorem idTab_getElem! (i : Fin n) : (Native.idTab n)[i.val]! = i.val := by
  show (Array.ofFn (n := n) fun i => i.val)[i.val]! = i.val
  rw [getElem!_pos _ _ (by simp), Array.getElem_ofFn]

theorem comp (ht : TabRep t g) (hs : TabRep s h) : TabRep (Native.comp n t s) (g * h) := by
  refine ⟨Array.size_ofFn, fun i => ?_⟩
  rw [comp_getElem!, hs.apply i, ht.apply (h i), Equiv.Perm.mul_apply]

theorem idTab : TabRep (Native.idTab n) (1 : Equiv.Perm (Fin n)) :=
  ⟨Array.size_ofFn, fun i => by rw [idTab_getElem!]; rfl⟩

theorem inv (ht : TabRep t g) (hs : s.size = n) (hc : Native.comp n s t = Native.idTab n) :
    TabRep s g⁻¹ := by
  refine ⟨hs, fun j => ?_⟩
  have e : (Native.comp n s t)[(g⁻¹ j).val]! = (Native.idTab n)[(g⁻¹ j).val]! := by rw [hc]
  rw [comp_getElem!, idTab_getElem!, ht.apply] at e
  have hj : g (g⁻¹ j) = j := Equiv.apply_symm_apply g j
  rwa [hj] at e

theorem conjTab (ht : TabRep t g) (hs : TabRep s h) (hi : TabRep t' g⁻¹) :
    TabRep (Native.conjTab n t t' s) (g * h * g⁻¹) :=
  (ht.comp hs).comp hi

theorem commTab {x y xi yi : Tab} {a b : Equiv.Perm (Fin n)} (hx : TabRep x a)
    (hy : TabRep y b) (hxi : TabRep xi a⁻¹) (hyi : TabRep yi b⁻¹) :
    TabRep (Native.commTab n x y xi yi) ⁅a, b⁆ := by
  rw [commutatorElement_def]
  exact ((hx.comp hy).comp hxi).comp hyi

end TabRep

theorem allBelow_eq_true {m : ℕ} {f : ℕ → Bool} : allBelow m f = true ↔ ∀ k < m, f k = true := by
  simp [allBelow, List.all_eq_true, List.mem_range]

theorem anyBelow_eq_true {m : ℕ} {f : ℕ → Bool} : anyBelow m f = true ↔ ∃ k < m, f k = true := by
  simp [anyBelow, List.any_eq_true, List.mem_range]

theorem countBelow_eq (m : ℕ) (f : ℕ → Bool) :
    countBelow m f = ((Finset.range m).filter fun k => f k = true).card := by
  simp [countBelow, Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range]

theorem found_spec {idx : Std.HashMap Tab ℕ} {T : Array Tab} {x : Tab}
    (h : found idx T x = true) : posOf idx T x < T.size ∧ T[posOf idx T x]! = x := by
  simpa [found, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using h

theorem mem_of_found {idx : Std.HashMap Tab ℕ} {T : Array Tab} {x : Tab}
    (h : found idx T x = true) : x ∈ T.toList := by
  obtain ⟨hp, he⟩ := found_spec h
  rw [Array.mem_toList_iff, Array.mem_iff_getElem]
  refine ⟨_, hp, ?_⟩
  rw [← getElem!_pos T _ hp]
  exact he

theorem exists_getElem!_of_mem {T : Array Tab} {t : Tab} (ht : t ∈ T.toList) :
    ∃ k < T.size, T[k]! = t := by
  rw [Array.mem_toList_iff, Array.mem_iff_getElem] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  exact ⟨k, hk, getElem!_pos T k hk⟩

theorem getElem!_mem {T : Array Tab} {k : ℕ} (hk : k < T.size) : T[k]! ∈ T.toList := by
  rw [getElem!_pos T k hk, Array.mem_toList_iff]
  exact Array.getElem_mem hk

theorem eq_of_posOf {idx : Std.HashMap Tab ℕ} {T : Array Tab}
    (h : ∀ k < T.size, posOf idx T T[k]! = k) {k k' : ℕ} (hk : k < T.size) (hk' : k' < T.size)
    (he : T[k]! = T[k']!) : k = k' := by
  rw [← h k hk, ← h k' hk', he]

theorem nodup_of_posOf {idx : Std.HashMap Tab ℕ} {T : Array Tab}
    (h : ∀ k < T.size, posOf idx T T[k]! = k) : T.toList.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  simp only [Array.length_toList] at hi hj
  simp only [Array.getElem_toList] at hij
  apply Fin.ext
  exact eq_of_posOf h hi hj (by rw [getElem!_pos T i hi, getElem!_pos T j hj, hij])

theorem invsOK_spec {n : ℕ} {T inv : Array Tab} (h : invsOK n T inv = true) {k : ℕ}
    (hk : k < T.size) {g : Equiv.Perm (Fin n)} (hg : TabRep T[k]! g) : TabRep inv[k]! g⁻¹ := by
  simp only [invsOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at h
  obtain ⟨-, h⟩ := h
  obtain ⟨h1, h2⟩ := h k hk
  exact hg.inv h1 h2

theorem treeOK_spec {step : ℕ → Tab → Tab} {k : ℕ} {root : Tab} {E : Enum}
    (h : treeOK step k root E = true) :
    0 < E.tabs.size ∧ E.tabs[0]! = root ∧ E.tabs.toList.Nodup ∧
      (∀ i < E.tabs.size, ∀ j < k, step j E.tabs[i]! ∈ E.tabs.toList) ∧
      (∀ i < E.tabs.size, 0 < i → E.par[i]! < i ∧ E.lab[i]! < k ∧
        E.tabs[i]! = step E.lab[i]! E.tabs[E.par[i]!]!) := by
  simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allBelow_eq_true] at h
  obtain ⟨⟨hpos, h0⟩, hall⟩ := h
  refine ⟨hpos, h0, nodup_of_posOf fun i hi => (hall i hi).1.1,
    fun i hi j hj => mem_of_found ((hall i hi).1.2 j hj), fun i hi hi0 => ?_⟩
  have h2 := (hall i hi).2
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h2
  rcases h2 with h2 | ⟨⟨h3, h4⟩, h5⟩
  · omega
  · exact ⟨h3, h4, h5⟩

section Tree

variable {n : ℕ} {step : ℕ → Tab → Tab} {k : ℕ} {root : Tab} {E : Enum}
  {f : ℕ → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)}

theorem tree_sound (h : treeOK step k root E = true)
    (hf : ∀ j < k, ∀ t g, TabRep t g → TabRep (step j t) (f j g))
    {x₀ : Equiv.Perm (Fin n)} (hroot : TabRep root x₀) (P : Equiv.Perm (Fin n) → Prop)
    (hP₀ : P x₀) (hP : ∀ j < k, ∀ g, P g → P (f j g)) :
    ∀ i < E.tabs.size, ∃ g, P g ∧ TabRep E.tabs[i]! g := by
  obtain ⟨-, h0, -, -, htree⟩ := treeOK_spec h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact ⟨x₀, hP₀, h0 ▸ hroot⟩
    · obtain ⟨hpar, hlab, he⟩ := htree i hi hi0
      obtain ⟨g, hg, hrep⟩ := ih _ hpar (hpar.trans hi)
      exact ⟨f _ g, hP _ hlab g hg, he ▸ hf _ hlab _ _ hrep⟩

theorem tree_closed (h : treeOK step k root E = true)
    (hf : ∀ j < k, ∀ t g, TabRep t g → TabRep (step j t) (f j g)) {j : ℕ} (hj : j < k)
    {g : Equiv.Perm (Fin n)} (hg : ∃ t ∈ E.tabs.toList, TabRep t g) :
    ∃ t ∈ E.tabs.toList, TabRep t (f j g) := by
  obtain ⟨-, -, -, hclosed, -⟩ := treeOK_spec h
  obtain ⟨t, ht, hrep⟩ := hg
  obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
  exact ⟨_, hclosed i hi j hj, hf j hj _ _ hrep⟩

end Tree

structure Enumerates {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (T : List Tab) : Prop where
  sound : ∀ t ∈ T, ∃ g ∈ H, TabRep t g
  complete : ∀ g ∈ H, ∃ t ∈ T, TabRep t g
  nodup : T.Nodup

theorem card_set_of_tabs {n : ℕ} {X : Set (Equiv.Perm (Fin n))} {L : List Tab}
    (hs : ∀ t ∈ L, ∃ g ∈ X, TabRep t g) (hc : ∀ g ∈ X, ∃ t ∈ L, TabRep t g) (hn : L.Nodup) :
    Nat.card X = L.length := by
  classical
  have key : ∀ t : {t // t ∈ L}, ∃ g : X, TabRep t.1 (g : Equiv.Perm (Fin n)) := fun t => by
    obtain ⟨g, hg, hr⟩ := hs t.1 t.2
    exact ⟨⟨g, hg⟩, hr⟩
  let F : {t // t ∈ L} → X := fun t => (key t).choose
  have hF : ∀ t, TabRep t.1 (F t : Equiv.Perm (Fin n)) := fun t => (key t).choose_spec
  have hbij : Function.Bijective F := by
    constructor
    · intro t t' htt
      apply Subtype.ext
      have h' := hF t'
      rw [← htt] at h'
      exact (hF t).tab_eq h'
    · intro g
      obtain ⟨t, ht, hr⟩ := hc g g.2
      exact ⟨⟨t, ht⟩, Subtype.ext ((hF ⟨t, ht⟩).perm_eq hr)⟩
  rw [← Nat.card_eq_of_bijective F hbij]
  have e : {t // t ∈ L} ≃ L.toFinset := Equiv.subtypeEquivRight fun t => List.mem_toFinset.symm
  rw [Nat.card_congr e, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hn]

namespace Enumerates

variable {n : ℕ} {H K : Subgroup (Equiv.Perm (Fin n))} {T : List Tab}

theorem card (hH : Enumerates H T) : Nat.card H = T.length :=
  card_set_of_tabs (X := (H : Set (Equiv.Perm (Fin n)))) hH.sound hH.complete hH.nodup

theorem filter (hH : Enumerates H T) (p : Tab → Bool)
    (hp : ∀ t g, TabRep t g → (p t = true ↔ g ∈ K)) : Enumerates (K ⊓ H) (T.filter p) := by
  refine ⟨fun t ht => ?_, fun g hg => ?_, hH.nodup.filter p⟩
  · rw [List.mem_filter] at ht
    obtain ⟨g, hg, hr⟩ := hH.sound t ht.1
    exact ⟨g, ⟨(hp t g hr).1 ht.2, hg⟩, hr⟩
  · obtain ⟨t, ht, hr⟩ := hH.complete g hg.2
    exact ⟨t, List.mem_filter.2 ⟨ht, (hp t g hr).2 hg.1⟩, hr⟩

theorem exists_pos {T : Array Tab} (hH : Enumerates H T.toList) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ H) : ∃ k < T.size, TabRep T[k]! g := by
  obtain ⟨t, ht, hr⟩ := hH.complete g hg
  obtain ⟨k, hk, rfl⟩ := exists_getElem!_of_mem ht
  exact ⟨k, hk, hr⟩

theorem exists_elt {T : Array Tab} (hH : Enumerates H T.toList) {k : ℕ} (hk : k < T.size) :
    ∃ g ∈ H, TabRep T[k]! g :=
  hH.sound _ (getElem!_mem hk)

theorem pos_unique {T : Array Tab} (hH : Enumerates H T.toList) {k k' : ℕ} (hk : k < T.size)
    (hk' : k' < T.size) {g : Equiv.Perm (Fin n)} (h : TabRep T[k]! g) (h' : TabRep T[k']! g) :
    k = k' := by
  have he : T[k] = T[k'] := by
    rw [← getElem!_pos T k hk, ← getElem!_pos T k' hk']
    exact h.tab_eq h'
  have hn := hH.nodup
  rw [List.nodup_iff_injective_getElem] at hn
  have := @hn ⟨k, by simpa using hk⟩ ⟨k', by simpa using hk'⟩ (by simpa using he)
  simpa using this

end Enumerates

section Generated

variable {n : ℕ} {gens : Array Tab} {A : Set (Equiv.Perm (Fin n))}

theorem exists_gen_fun (hgens : ∀ j < gens.size, ∃ a ∈ A, TabRep gens[j]! a) :
    ∃ a : ℕ → Equiv.Perm (Fin n), ∀ j < gens.size, a j ∈ A ∧ TabRep gens[j]! (a j) := by
  classical
  refine ⟨fun j => if hj : j < gens.size then (hgens j hj).choose else 1, fun j hj => ?_⟩
  simp only [hj, ↓reduceDIte]
  exact (hgens j hj).choose_spec

theorem enumerates_closure {E : Enum}
    (hA : ∀ a ∈ A, ∃ j < gens.size, TabRep gens[j]! a)
    (hgens : ∀ j < gens.size, ∃ a ∈ A, TabRep gens[j]! a)
    (h : enumOK n gens E = true) : Enumerates (Subgroup.closure A) E.tabs.toList := by
  obtain ⟨a, ha⟩ := exists_gen_fun hgens
  have hf : ∀ j < gens.size, ∀ t g, TabRep t g → TabRep (leftStep n gens j t) (a j * g) :=
    fun j hj t g ht => (ha j hj).2.comp ht
  unfold enumOK at h
  obtain ⟨hpos, h0, hnodup, -, -⟩ := treeOK_spec h
  refine ⟨fun t ht => ?_, fun g hg => ?_, hnodup⟩
  · obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
    obtain ⟨g, hg, hrep⟩ := tree_sound h hf TabRep.idTab (· ∈ Subgroup.closure A)
      (Subgroup.one_mem _) (fun j hj g hg => Subgroup.mul_mem _
        (Subgroup.subset_closure (ha j hj).1) hg) i hi
    exact ⟨g, hg, hrep⟩
  · let F : Set (Equiv.Perm (Fin n)) := {g | ∃ t ∈ E.tabs.toList, TabRep t g}
    have hAF : ∀ x ∈ A, ∀ y ∈ F, x • y ∈ F := by
      intro x hx y hy
      obtain ⟨j, hj, hxj⟩ := hA x hx
      have hxa : x = a j := hxj.perm_eq (ha j hj).2
      rw [smul_eq_mul, hxa]
      exact tree_closed h hf hj hy
    have h1 : (1 : Equiv.Perm (Fin n)) ∈ F := ⟨_, getElem!_mem hpos, h0 ▸ TabRep.idTab⟩
    have := CFSG.Perm.smul_mem_of_finite_of_mem_closure (Set.toFinite F) hAF hg h1
    rwa [smul_eq_mul, mul_one] at this

theorem conj_orbit {ginv : Array Tab} {E : Enum} {x₀ : Equiv.Perm (Fin n)} {root : Tab}
    (hA : ∀ a ∈ A, ∃ j < gens.size, TabRep gens[j]! a)
    (hgens : ∀ j < gens.size, ∃ a ∈ A, TabRep gens[j]! a) (hroot : TabRep root x₀)
    (h : orbitOK n gens ginv root E = true) :
    (∀ t ∈ E.tabs.toList, ∃ c ∈ Subgroup.closure A, TabRep t (c * x₀ * c⁻¹)) ∧
      (∀ c ∈ Subgroup.closure A, ∃ t ∈ E.tabs.toList, TabRep t (c * x₀ * c⁻¹)) ∧
      E.tabs.toList.Nodup := by
  obtain ⟨a, ha⟩ := exists_gen_fun hgens
  unfold orbitOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hinv, h⟩ := h
  have hf : ∀ j < gens.size, ∀ t g, TabRep t g →
      TabRep (conjStep n gens ginv j t) (a j * g * (a j)⁻¹) :=
    fun j hj t g ht => (ha j hj).2.conjTab ht (invsOK_spec hinv hj (ha j hj).2)
  obtain ⟨hpos, h0, hnodup, -, -⟩ := treeOK_spec h
  refine ⟨fun t ht => ?_, fun c hc => ?_, hnodup⟩
  · obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
    obtain ⟨g, ⟨c, hc, rfl⟩, hrep⟩ := tree_sound h hf hroot
      (fun g => ∃ c ∈ Subgroup.closure A, g = c * x₀ * c⁻¹) ⟨1, Subgroup.one_mem _, by group⟩
      (fun j hj g ⟨c, hc, hgc⟩ => ⟨a j * c, Subgroup.mul_mem _
        (Subgroup.subset_closure (ha j hj).1) hc, by rw [hgc]; group⟩) i hi
    exact ⟨c, hc, hrep⟩
  · let F : Set (Equiv.Perm (Fin n)) := {g | ∃ t ∈ E.tabs.toList, TabRep t g}
    have hAF : ∀ x ∈ ConjAct.toConjAct '' A, ∀ y ∈ F, x • y ∈ F := by
      rintro _ ⟨x, hx, rfl⟩ y hy
      obtain ⟨j, hj, hxj⟩ := hA x hx
      have hxa : x = a j := hxj.perm_eq (ha j hj).2
      rw [ConjAct.toConjAct_smul, hxa]
      exact tree_closed h hf hj hy
    have hx₀ : x₀ ∈ F := ⟨_, getElem!_mem hpos, h0 ▸ hroot⟩
    have hc' : ConjAct.toConjAct c ∈ Subgroup.closure (ConjAct.toConjAct '' A) := by
      have := Subgroup.mem_map_of_mem
        (ConjAct.toConjAct : Equiv.Perm (Fin n) ≃* ConjAct (Equiv.Perm (Fin n))).toMonoidHom hc
      rw [MonoidHom.map_closure] at this
      simpa using this
    have := CFSG.Perm.smul_mem_of_finite_of_mem_closure (Set.toFinite F) hAF hc' hx₀
    rwa [ConjAct.toConjAct_smul] at this

end Generated

section Scans

variable {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}

theorem eq_one_of_centralOK {T gs : Array Tab} (hH : Enumerates H T.toList)
    (h : centralOK n T gs = true) {g : Equiv.Perm (Fin n)} (hg : g ∈ H)
    (hcomm : ∀ i < gs.size, ∃ a, TabRep gs[i]! a ∧ g * a = a * g) : g = 1 := by
  obtain ⟨k, hk, hrep⟩ := hH.exists_pos hg
  simp only [centralOK, allBelow_eq_true] at h
  have hk' := h k hk
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hk'
  rcases hk' with hk' | hk'
  · have hall : allBelow gs.size
        (fun i => Native.comp n T[k]! gs[i]! == Native.comp n gs[i]! T[k]!) = true := by
      rw [allBelow_eq_true]
      intro i hi
      obtain ⟨a, ha, hga⟩ := hcomm i hi
      exact ((hrep.comp ha).beq_iff (ha.comp hrep)).2 hga
    rw [hall] at hk'
    exact Bool.noConfusion hk'
  · exact (hrep.beq_iff TabRep.idTab).1 hk'

theorem exists_of_coverOK {T : Array Tab} {O : Array (Array Tab)} (hH : Enumerates H T.toList)
    (h : coverOK n T O = true) {g : Equiv.Perm (Fin n)} (hg : g ∈ H) (hg1 : g ≠ 1)
    (hg2 : g * g = 1) : ∃ i < O.size, ∃ t ∈ O[i]!.toList, TabRep t g := by
  obtain ⟨k, hk, hrep⟩ := hH.exists_pos hg
  simp only [coverOK, allBelow_eq_true] at h
  have hk' := h k hk
  simp only [Bool.or_eq_true, Bool.not_eq_true', anyBelow_eq_true] at hk'
  rcases hk' with (hk' | hk') | ⟨i, hi, hf⟩
  · exact (hg1 ((hrep.beq_iff TabRep.idTab).1 hk')).elim
  · rw [← Bool.not_eq_true, (hrep.comp hrep).beq_iff TabRep.idTab] at hk'
    exact (hk' hg2).elim
  · exact ⟨i, hi, _, mem_of_found hf, hrep⟩

theorem notInOK_spec {T : Array Tab} {x : Tab} {g : Equiv.Perm (Fin n)}
    (h : notInOK T x = true) (hx : TabRep x g) : ∀ t ∈ T.toList, ¬ TabRep t g := by
  intro t ht hrep
  obtain ⟨k, hk, rfl⟩ := exists_getElem!_of_mem ht
  simp only [notInOK, allBelow_eq_true, Bool.not_eq_true'] at h
  have := h k hk
  rw [← Bool.not_eq_true, hrep.beq_iff hx] at this
  exact this rfl

theorem not_mem_of_notInOK {T : Array Tab} {x : Tab} {g : Equiv.Perm (Fin n)}
    (hH : Enumerates H T.toList) (h : notInOK T x = true) (hx : TabRep x g) : g ∉ H := by
  intro hg
  obtain ⟨t, ht, hrep⟩ := hH.complete g hg
  exact notInOK_spec h hx t ht hrep

theorem conj_mem_of_normalOK {T gens ginv gs : Array Tab} (hH : Enumerates H T.toList)
    (h : normalOK n T gens ginv gs = true) {j i : ℕ} (hj : j < gens.size) (hi : i < gs.size)
    {a s : Equiv.Perm (Fin n)} (ha : TabRep gens[j]! a) (hs : TabRep gs[i]! s) :
    a * s * a⁻¹ ∈ H ∧ a⁻¹ * s * a ∈ H := by
  simp only [normalOK, Bool.and_eq_true, allBelow_eq_true] at h
  obtain ⟨hinv, h⟩ := h
  have hai := invsOK_spec hinv hj ha
  obtain ⟨h1, h2⟩ := h j hj i hi
  constructor
  · obtain ⟨g, hg, hr⟩ := hH.sound _ (mem_of_found h1)
    rwa [(ha.conjTab hs hai).perm_eq hr]
  · obtain ⟨g, hg, hr⟩ := hH.sound _ (mem_of_found h2)
    have := hai.conjTab hs (by rwa [inv_inv])
    rw [inv_inv] at this
    rwa [this.perm_eq hr]

end Scans

end CFSG.ComponentClassification.PSL3Four
