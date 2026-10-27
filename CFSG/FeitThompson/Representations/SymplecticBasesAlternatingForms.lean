module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Tactic.NormNum.GCD

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module Submodule
open LinearMap (BilinForm)

universe u

variable {K : Type*} [Field K] {V : Type u} [AddCommGroup V] [Module K V]

theorem mem_orthogonal_span_iff {β : BilinForm K V} {s : Set V} {x : V} :
    x ∈ β.orthogonal (span K s) ↔ ∀ v ∈ s, β v x = 0 := by
  refine ⟨fun hx v hv => LinearMap.BilinForm.mem_orthogonal_iff.mp hx v (subset_span hv), ?_⟩
  intro hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  have hsub : span K s ≤ LinearMap.ker (β.flip x) := by
    rw [span_le]
    intro v hv
    simpa [LinearMap.flip_apply] using hx v hv
  intro n hn
  simpa [LinearMap.flip_apply] using hsub hn

structure IsSymplecticBasis (β : BilinForm K V) {n : ℕ} (b : Basis (Fin n ⊕ Fin n) K V) :
    Prop where
  inl_inl : ∀ i j, β (b (Sum.inl i)) (b (Sum.inl j)) = 0
  inr_inr : ∀ i j, β (b (Sum.inr i)) (b (Sum.inr j)) = 0
  inl_inr : ∀ i j, β (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0

namespace IsSymplecticBasis

variable {β : BilinForm K V} {n : ℕ} {b : Basis (Fin n ⊕ Fin n) K V}

theorem finrank_eq (_hb : IsSymplecticBasis β b) : finrank K V = 2 * n := by
  rw [finrank_eq_card_basis b]; simp [two_mul]

theorem inr_inl (hb : IsSymplecticBasis β b) (halt : β.IsAlt) (i j : Fin n) :
    β (b (Sum.inr j)) (b (Sum.inl i)) = if i = j then -1 else 0 := by
  have h := halt.neg_eq (b (Sum.inl i)) (b (Sum.inr j))
  rw [hb.inl_inr i j] at h
  rw [← h]
  split <;> simp

theorem apply_inl_eq_repr (hb : IsSymplecticBasis β b) (i : Fin n) (x : V) :
    β (b (Sum.inl i)) x = b.repr x (Sum.inr i) := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum, Fintype.sum_sum_type]
  simp only [map_smul, smul_eq_mul, hb.inl_inl, hb.inl_inr, mul_zero, mul_ite, mul_one]
  simp [Finset.sum_ite_eq]

theorem apply_inr_eq_neg_repr (hb : IsSymplecticBasis β b) (halt : β.IsAlt) (j : Fin n) (x : V) :
    β (b (Sum.inr j)) x = -b.repr x (Sum.inl j) := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum, Fintype.sum_sum_type]
  simp only [map_smul, smul_eq_mul, hb.inr_inr, hb.inr_inl halt, mul_zero, mul_ite, mul_one,
    mul_neg]
  simp [Finset.sum_ite_eq']

end IsSymplecticBasis

theorem mem_span_range_comp_inl_iff {n : ℕ} (b : Basis (Fin n ⊕ Fin n) K V) {x : V} :
    x ∈ span K (Set.range (b ∘ Sum.inl)) ↔ ∀ i, b.repr x (Sum.inr i) = 0 := by
  rw [Set.range_comp, b.mem_span_image]
  constructor
  · intro h i
    by_contra hi
    obtain ⟨j, hj⟩ := h (Finsupp.mem_support_iff.mpr hi)
    exact Sum.inl_ne_inr hj
  · intro h j hj
    rcases j with j | j
    · exact ⟨j, rfl⟩
    · exact absurd (Finsupp.mem_support_iff.mp hj) (by simpa using h j)

theorem finrank_span_range_comp_inl {n : ℕ} (b : Basis (Fin n ⊕ Fin n) K V) :
    finrank K (span K (Set.range (b ∘ Sum.inl))) = n := by
  rw [finrank_span_eq_card (b.linearIndependent.comp Sum.inl Sum.inl_injective)]
  simp

theorem IsSymplecticBasis.orthogonal_span_range_comp_inl {β : BilinForm K V} {n : ℕ}
    {b : Basis (Fin n ⊕ Fin n) K V} (hb : IsSymplecticBasis β b) :
    β.orthogonal (span K (Set.range (b ∘ Sum.inl))) = span K (Set.range (b ∘ Sum.inl)) := by
  ext x
  rw [mem_span_range_comp_inl_iff, mem_orthogonal_span_iff]
  refine ⟨fun hx i => ?_, ?_⟩
  · rw [← hb.apply_inl_eq_repr]
    exact hx _ ⟨i, rfl⟩
  · rintro hx v ⟨i, rfl⟩
    exact (hb.apply_inl_eq_repr i x).trans (hx i)

theorem IsSymplecticBasis.mem_span_range_comp_inl_iff_forall {β : BilinForm K V} {n : ℕ}
    {b : Basis (Fin n ⊕ Fin n) K V} (hb : IsSymplecticBasis β b) (halt : β.IsAlt) {x : V} :
    x ∈ span K (Set.range (b ∘ Sum.inl)) ↔
      ∀ l ∈ span K (Set.range (b ∘ Sum.inl)), β x l = 0 := by
  constructor
  · intro hx l hl
    have hxo : x ∈ β.orthogonal (span K (Set.range (b ∘ Sum.inl))) := by
      rw [hb.orthogonal_span_range_comp_inl]; exact hx
    exact halt.isRefl l x (LinearMap.BilinForm.mem_orthogonal_iff.mp hxo l hl)
  · intro h
    rw [← hb.orthogonal_span_range_comp_inl, LinearMap.BilinForm.mem_orthogonal_iff]
    exact fun l hl => halt.isRefl x l (h l hl)

theorem IsSymplecticBasis.finrank_span_range_comp_inl {β : BilinForm K V} {n : ℕ}
    {b : Basis (Fin n ⊕ Fin n) K V} (_hb : IsSymplecticBasis β b) :
    finrank K (span K (Set.range (b ∘ Sum.inl))) = n :=
  _root_.CFSG.FeitThompson.finrank_span_range_comp_inl b

section Existence

private theorem exists_apply_eq_one {β : BilinForm K V} (hnd : β.SeparatingLeft) {e : V}
    (he : e ≠ 0) : ∃ f, β e f = 1 := by
  by_contra hc
  push Not at hc
  refine he (hnd e fun y => ?_)
  by_contra hy
  exact hc ((β e y)⁻¹ • y) (by simp [inv_mul_cancel₀ hy])

private theorem isCompl_orthogonal_span_pair [FiniteDimensional K V] {β : BilinForm K V}
    (halt : β.IsAlt) {e f : V} (hef : β e f = 1) :
    IsCompl (span K ({e, f} : Set V)) (β.orthogonal (span K {e, f})) ∧
      finrank K (span K ({e, f} : Set V)) = 2 := by
  have hfe : β f e = -1 := by
    have := halt.neg_eq e f
    rw [hef] at this
    linear_combination -this
  have hmem : ∀ x ∈ β.orthogonal (span K ({e, f} : Set V)), β e x = 0 ∧ β f x = 0 := by
    intro x hx
    rw [mem_orthogonal_span_iff] at hx
    exact ⟨hx e (by simp), hx f (by simp)⟩
  have hdisj : Disjoint (span K ({e, f} : Set V)) (β.orthogonal (span K {e, f})) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨h1, h2⟩ := hmem _ hx'
    simp only [map_add, map_smul, smul_eq_mul, halt.self_eq_zero, hef, hfe, mul_zero, mul_one,
      zero_add, add_zero, mul_neg] at h1 h2
    simp [h1, neg_eq_zero.mp h2]
  have hli : LinearIndependent K ![e, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun x => β e x) hst
    have h2 := congrArg (fun x => β f x) hst
    simp only [map_add, map_smul, smul_eq_mul, halt.self_eq_zero, hef, hfe, mul_zero, mul_one,
      zero_add, add_zero, mul_neg, map_zero] at h1 h2
    exact ⟨neg_eq_zero.mp h2, h1⟩
  have hrange : Set.range ![e, f] = ({e, f} : Set V) := by
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
  refine ⟨?_, by rw [← hrange, finrank_span_eq_card hli]; simp⟩
  rw [← LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal halt.isRefl]
  exact β.nondegenerate_restrict_of_disjoint_orthogonal halt.isRefl hdisj

private theorem linearIndependent_of_symplectic {n : ℕ} {β : BilinForm K V} {e f : Fin n → V}
    (hee : ∀ i j, β (e i) (e j) = 0) (hff : ∀ i j, β (f i) (f j) = 0)
    (hef : ∀ i j, β (e i) (f j) = if i = j then 1 else 0) :
    LinearIndependent K (Sum.elim e f) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hx : ∑ i, g (Sum.inl i) • e i + ∑ i, g (Sum.inr i) • f i = 0 := by
    simpa [Fintype.sum_sum_type] using hg
  have key : ∀ j, g (Sum.inl j) = 0 ∧ g (Sum.inr j) = 0 := by
    intro j
    refine ⟨?_, ?_⟩
    · have h := congrArg (fun x => β x (f j)) hx
      simp only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, map_smul,
        LinearMap.smul_apply, smul_eq_mul, hef, hff, map_zero, LinearMap.zero_apply] at h
      simpa using h
    · have h := congrArg (fun x => β (e j) x) hx
      simp only [map_add, map_sum, map_smul, smul_eq_mul, hee, hef, map_zero] at h
      simpa using h
  intro i
  cases i with
  | inl i => exact (key i).1
  | inr i => exact (key i).2

private theorem exists_isSymplecticBasis_aux (m : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (β : BilinForm K V),
      finrank K V ≤ m → β.IsAlt → β.SeparatingLeft →
      ∃ (n : ℕ) (b : Basis (Fin n ⊕ Fin n) K V), IsSymplecticBasis β b := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro V _ _ _ β hm halt hnd
    rcases subsingleton_or_nontrivial V with hs | hs
    · exact ⟨0, Basis.empty V, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
    obtain ⟨e, he⟩ := exists_ne (0 : V)
    obtain ⟨f, hef⟩ := exists_apply_eq_one hnd he
    obtain ⟨hcompl, hdimU⟩ := isCompl_orthogonal_span_pair halt hef
    set U := span K ({e, f} : Set V) with hU
    set W := β.orthogonal U with hW
    have heU : e ∈ U := subset_span (by simp)
    have hfU : f ∈ U := subset_span (by simp)
    have hEW : ∀ w ∈ W, β e w = 0 := fun w hw =>
      LinearMap.BilinForm.mem_orthogonal_iff.mp hw e heU
    have hFW : ∀ w ∈ W, β f w = 0 := fun w hw =>
      LinearMap.BilinForm.mem_orthogonal_iff.mp hw f hfU
    have haltW : (β.restrict W).IsAlt := by
      intro x; simp [LinearMap.BilinForm.restrict_apply, halt.self_eq_zero]
    have hndW : (β.restrict W).SeparatingLeft := by
      intro x hx
      refine Subtype.ext (hnd _ fun v => ?_)
      have hv : v ∈ U ⊔ W := by rw [hcompl.sup_eq_top]; exact mem_top
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
      have h1 : β (x : V) u = 0 :=
        halt.isRefl _ _ (LinearMap.BilinForm.mem_orthogonal_iff.mp x.2 u hu)
      have h2 : β (x : V) w = 0 := by
        simpa [LinearMap.BilinForm.restrict_apply] using hx ⟨w, hw⟩
      simp [h1, h2]
    have hsum : finrank K U + finrank K W = finrank K V :=
      Submodule.finrank_add_eq_of_isCompl hcompl
    have hlt : finrank K W < m := by omega
    obtain ⟨n, bW, hbW⟩ := ih _ hlt W (β.restrict W) le_rfl haltW hndW
    have hbWmem : ∀ i, (bW i : V) ∈ W := fun i => (bW i).2
    have hres : ∀ x y : W, (β.restrict W) x y = β (x : V) (y : V) := by
      intro x y; simp [LinearMap.BilinForm.restrict_apply]
    set E : Fin (n + 1) → V := Fin.cons e (fun i => (bW (Sum.inl i) : V)) with hE
    set F : Fin (n + 1) → V := Fin.cons f (fun i => (bW (Sum.inr i) : V)) with hF
    have hE0 : E 0 = e := by rw [hE, Fin.cons_zero]
    have hEs : ∀ i, E i.succ = (bW (Sum.inl i) : V) := fun i => by rw [hE, Fin.cons_succ]
    have hF0 : F 0 = f := by rw [hF, Fin.cons_zero]
    have hFs : ∀ i, F i.succ = (bW (Sum.inr i) : V) := fun i => by rw [hF, Fin.cons_succ]
    have hEE : ∀ i j, β (E i) (E j) = 0 := by
      refine Fin.cases (Fin.cases ?_ ?_) fun i => Fin.cases ?_ ?_
      · rw [hE0]; exact halt.self_eq_zero e
      · intro j; rw [hE0, hEs]; exact hEW _ (hbWmem _)
      · rw [hE0, hEs]; exact halt.isRefl _ _ (hEW _ (hbWmem (Sum.inl i)))
      · intro j; rw [hEs, hEs, ← hres]; exact hbW.inl_inl i j
    have hFF : ∀ i j, β (F i) (F j) = 0 := by
      refine Fin.cases (Fin.cases ?_ ?_) fun i => Fin.cases ?_ ?_
      · rw [hF0]; exact halt.self_eq_zero f
      · intro j; rw [hF0, hFs]; exact hFW _ (hbWmem _)
      · rw [hF0, hFs]; exact halt.isRefl _ _ (hFW _ (hbWmem (Sum.inr i)))
      · intro j; rw [hFs, hFs, ← hres]; exact hbW.inr_inr i j
    have hEF : ∀ i j, β (E i) (F j) = if i = j then 1 else 0 := by
      refine Fin.cases (Fin.cases ?_ ?_) fun i => Fin.cases ?_ ?_
      · rw [hE0, hF0, if_pos rfl]; exact hef
      · intro j
        rw [hE0, hFs, if_neg (Fin.succ_ne_zero j).symm]
        exact hEW _ (hbWmem _)
      · rw [hEs, hF0, if_neg (Fin.succ_ne_zero i)]
        exact halt.isRefl _ _ (hFW _ (hbWmem (Sum.inl i)))
      · intro j
        rw [hEs, hFs, ← hres, hbW.inl_inr i j]
        simp [Fin.succ_inj]
    have hli : LinearIndependent K (Sum.elim E F) := linearIndependent_of_symplectic hEE hFF hEF
    have hcard : Fintype.card (Fin (n + 1) ⊕ Fin (n + 1)) = finrank K V := by
      rw [← hsum, hdimU, hbW.finrank_eq]
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    have hb : ∀ i, (basisOfLinearIndependentOfCardEqFinrank hli hcard) i = Sum.elim E F i := by
      intro i
      simp only [coe_basisOfLinearIndependentOfCardEqFinrank]
    refine ⟨n + 1, basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_, ?_, ?_⟩
    · intro i j; rw [hb, hb]; exact hEE i j
    · intro i j; rw [hb, hb]; exact hFF i j
    · intro i j; rw [hb, hb]; exact hEF i j

theorem exists_isSymplecticBasis [FiniteDimensional K V] (β : BilinForm K V) (halt : β.IsAlt)
    (hnd : β.SeparatingLeft) :
    ∃ (n : ℕ) (b : Basis (Fin n ⊕ Fin n) K V), IsSymplecticBasis β b :=
  exists_isSymplecticBasis_aux (finrank K V) V β le_rfl halt hnd

theorem even_finrank_of_isAlt_of_separatingLeft [FiniteDimensional K V] (β : BilinForm K V)
    (halt : β.IsAlt) (hnd : β.SeparatingLeft) : ∃ n : ℕ, finrank K V = 2 * n := by
  obtain ⟨n, b, hb⟩ := exists_isSymplecticBasis β halt hnd
  exact ⟨n, hb.finrank_eq⟩

theorem exists_isSymplecticBasis_zmod {p : ℕ} [Fact p.Prime] {V : Type u} [AddCommGroup V]
    [Module (ZMod p) V] [FiniteDimensional (ZMod p) V] (β : BilinForm (ZMod p) V)
    (hself : ∀ v, β v v = 0) (hrad : ∀ v : V, (∀ w, β v w = 0) → v = 0) :
    ∃ (n : ℕ) (b : Basis (Fin n ⊕ Fin n) (ZMod p) V),
      IsSymplecticBasis β b ∧ finrank (ZMod p) V = 2 * n ∧
      β.orthogonal (span (ZMod p) (Set.range (b ∘ Sum.inl)))
        = span (ZMod p) (Set.range (b ∘ Sum.inl)) ∧
      finrank (ZMod p) (span (ZMod p) (Set.range (b ∘ Sum.inl))) = n := by
  obtain ⟨n, b, hb⟩ := exists_isSymplecticBasis β hself hrad
  exact ⟨n, b, hb, hb.finrank_eq, hb.orthogonal_span_range_comp_inl,
    hb.finrank_span_range_comp_inl⟩

end Existence

end

end CFSG.FeitThompson
