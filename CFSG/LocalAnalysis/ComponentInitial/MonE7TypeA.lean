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
public import Mathlib.GroupTheory.PresentedGroup
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

namespace CFSG.LocalAnalysis.ComponentInitial.MonE7

open Equiv

@[expose] def typeARels (m : ℕ) : Set (FreeGroup (Fin m)) :=
  {x | (∃ i, x = FreeGroup.of i ^ 2) ∨
    (∃ i j : Fin m, (j : ℕ) = i + 1 ∧ x = (FreeGroup.of i * FreeGroup.of j) ^ 3) ∨
    (∃ i j : Fin m, (i : ℕ) + 2 ≤ j ∧ x = (FreeGroup.of i * FreeGroup.of j) ^ 2)}

abbrev TypeA (m : ℕ) : Type := PresentedGroup (typeARels m)

@[expose] noncomputable def sA {m : ℕ} (i : Fin m) : TypeA m := PresentedGroup.of i

@[expose] def adjSwap {m : ℕ} (i : Fin m) : Perm (Fin (m + 1)) := swap i.castSucc i.succ

theorem adjSwap_rels (m : ℕ) : ∀ r ∈ typeARels m, FreeGroup.lift adjSwap r = 1 := by
  rintro r (⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
  · simp [adjSwap, pow_two, swap_mul_self]
  · have hj : j.castSucc = i.succ := Fin.ext (by simp [hij])
    simp only [map_pow, map_mul, FreeGroup.lift_apply_of, adjSwap]
    rw [hj, swap_comm i.castSucc i.succ]
    have h3 := (Perm.isThreeCycle_swap_mul_swap_same (a := i.succ) (b := i.castSucc)
      (c := j.succ) (fun h => by have := congrArg Fin.val h; simp at this)
      (fun h => by have := congrArg Fin.val h; simp [hij] at this)
      (fun h => by have := congrArg Fin.val h; simp [hij] at this; omega)).orderOf
    rw [← h3, pow_orderOf_eq_one]
  · simp only [map_pow, map_mul, FreeGroup.lift_apply_of, adjSwap]
    have hne : ∀ a b : Fin (m + 1), (a : ℕ) ≠ b → a ≠ b := fun a b h h' => h (congrArg _ h')
    have hd : (swap i.castSucc i.succ).Disjoint (swap j.castSucc j.succ) :=
      Perm.disjoint_swap_swap (List.nodup_cons.2 ⟨by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hne _ _ (by simp), hne _ _ (by simp; omega), hne _ _ (by simp; omega)⟩,
        List.nodup_cons.2 ⟨by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hne _ _ (by simp; omega), hne _ _ (by simp; omega)⟩,
        List.nodup_cons.2 ⟨by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact hne _ _ (by simp), List.nodup_singleton _⟩⟩⟩)
    rw [(hd.commute).mul_pow, pow_two, pow_two, swap_mul_self, swap_mul_self, mul_one]

@[expose] noncomputable def toPerm (m : ℕ) : TypeA m →* Perm (Fin (m + 1)) :=
  PresentedGroup.toGroup (adjSwap_rels m)

theorem toPerm_sA {m : ℕ} (i : Fin m) : toPerm m (sA i) = adjSwap i :=
  PresentedGroup.toGroup.of _

theorem toPerm_surjective (m : ℕ) : Function.Surjective (toPerm m) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  have h := Perm.mclosure_swap_castSucc_succ m
  intro σ _
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin m => swap i.castSucc i.succ) :=
    h ▸ Submonoid.mem_top σ
  refine (Submonoid.closure_le (S := (toPerm m).range.toSubmonoid)).2 ?_ hσ
  rintro _ ⟨i, rfl⟩
  exact ⟨sA i, toPerm_sA i⟩

section Relations

variable {m : ℕ}

theorem mk_rel {r : FreeGroup (Fin m)} (hr : r ∈ typeARels m) :
    PresentedGroup.mk (typeARels m) r = 1 := by
  rw [PresentedGroup.mk_eq_one_iff]
  exact Subgroup.subset_normalClosure hr

@[expose] noncomputable def gen (m : ℕ) (i : ℕ) : TypeA m :=
  if h : i < m then sA ⟨i, h⟩ else 1

theorem gen_of_lt {i : ℕ} (h : i < m) : gen m i = sA ⟨i, h⟩ := dite_eq_left h

theorem gen_mul_self (i : ℕ) : gen m i * gen m i = 1 := by
  unfold gen
  split_ifs with h
  · have := mk_rel (Or.inl ⟨⟨i, h⟩, rfl⟩ : FreeGroup.of (⟨i, h⟩ : Fin m) ^ 2 ∈ typeARels m)
    rwa [map_pow, pow_two] at this
  · exact mul_one 1

theorem gen_inv (i : ℕ) : (gen m i)⁻¹ = gen m i :=
  (eq_inv_of_mul_eq_one_left (gen_mul_self i)).symm

theorem gen_comm {i j : ℕ} (hij : i + 2 ≤ j) : gen m i * gen m j = gen m j * gen m i := by
  by_cases hj : j < m
  · have hi : i < m := by omega
    have h := mk_rel (Or.inr (Or.inr ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, rfl⟩) :
      (FreeGroup.of (⟨i, hi⟩ : Fin m) * FreeGroup.of ⟨j, hj⟩) ^ 2 ∈ typeARels m)
    rw [map_pow, map_mul] at h
    have h2 : gen m i * gen m j * (gen m i * gen m j) = 1 := by
      rw [gen_of_lt hi, gen_of_lt hj, ← pow_two]; exact h
    rw [eq_inv_of_mul_eq_one_left h2, mul_inv_rev, gen_inv, gen_inv]
  · have h1 : gen m j = 1 := by simp [gen, hj]
    rw [h1, mul_one, one_mul]

theorem gen_braid {i : ℕ} (hi : i + 1 < m) :
    gen m i * gen m (i + 1) * gen m i = gen m (i + 1) * gen m i * gen m (i + 1) := by
  have hi' : i < m := by omega
  have h := mk_rel (Or.inr (Or.inl ⟨⟨i, hi'⟩, ⟨i + 1, hi⟩, rfl, rfl⟩) :
    (FreeGroup.of (⟨i, hi'⟩ : Fin m) * FreeGroup.of ⟨i + 1, hi⟩) ^ 3 ∈ typeARels m)
  rw [map_pow, map_mul] at h
  have h' : (gen m i * gen m (i + 1)) ^ 3 = 1 := by
    rw [gen_of_lt hi', gen_of_lt hi]
    exact h
  set a := gen m i
  set b := gen m (i + 1)
  have h3 : a * b * a * (b * a * b) = 1 := by
    rw [← h', pow_three]
    simp only [mul_assoc]
  rw [eq_inv_of_mul_eq_one_left h3, mul_inv_rev, mul_inv_rev, gen_inv, gen_inv, mul_assoc]

end Relations

section Cosets

variable (m : ℕ)

theorem incl_rels : ∀ r ∈ typeARels m,
    FreeGroup.lift (fun i : Fin m => sA (m := m + 1) i.castSucc) r = 1 := by
  rintro r (⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
  · simp only [map_pow, FreeGroup.lift_apply_of]
    exact mk_rel (Or.inl ⟨i.castSucc, rfl⟩)
  · simp only [map_pow, map_mul, FreeGroup.lift_apply_of]
    exact mk_rel (Or.inr (Or.inl ⟨i.castSucc, j.castSucc, by simp [hij], rfl⟩))
  · simp only [map_pow, map_mul, FreeGroup.lift_apply_of]
    exact mk_rel (Or.inr (Or.inr ⟨i.castSucc, j.castSucc, by simpa using hij, rfl⟩))

@[expose] noncomputable def incl : TypeA m →* TypeA (m + 1) :=
  PresentedGroup.toGroup (incl_rels m)

variable {m}

theorem incl_gen {i : ℕ} (hi : i < m) : incl m (gen m i) = gen (m + 1) i := by
  rw [gen_of_lt hi, gen_of_lt (by omega : i < m + 1), incl, sA, PresentedGroup.toGroup.of]
  rfl

variable (m) in
@[expose] noncomputable def tw (j : ℕ) : TypeA (m + 1) :=
  if j ≤ m then tw (j + 1) * gen (m + 1) j else 1
termination_by m + 1 - j

theorem tw_of_le {j : ℕ} (h : j ≤ m) : tw m j = tw m (j + 1) * gen (m + 1) j := by
  rw [tw, ite_eq_left h]

theorem tw_of_gt {j : ℕ} (h : m < j) : tw m j = 1 := by
  rw [tw, ite_eq_right (by omega : ¬ j ≤ m)]

theorem tw_mul_gen_self {j : ℕ} (h : j ≤ m) : tw m j * gen (m + 1) j = tw m (j + 1) := by
  rw [tw_of_le h, mul_assoc, gen_mul_self, mul_one]

theorem tw_mul_gen_comm {i : ℕ} : ∀ k j : ℕ, m + 1 - j = k → i + 2 ≤ j →
    tw m j * gen (m + 1) i = gen (m + 1) i * tw m j := by
  intro k
  induction k with
  | zero =>
    intro j hk _
    rw [tw_of_gt (by omega), one_mul, mul_one]
  | succ k ih =>
    intro j hk hij
    rw [tw_of_le (by omega), mul_assoc, ← gen_comm hij, ← mul_assoc, ih (j + 1) (by omega)
      (by omega), mul_assoc]

theorem tw_mul_gen_of_lt : ∀ d j i : ℕ, i = j + 1 + d → i ≤ m →
    tw m j * gen (m + 1) i = gen (m + 1) (i - 1) * tw m j := by
  intro d
  induction d with
  | zero =>
    intro j i hi him
    obtain rfl : i = j + 1 := by omega
    have h1 : j ≤ m := by omega
    have h2 : j + 1 ≤ m := by omega
    rw [tw_of_le h1, tw_of_le h2, Nat.add_sub_cancel]
    calc tw m (j + 1 + 1) * gen (m + 1) (j + 1) * gen (m + 1) j * gen (m + 1) (j + 1)
        = tw m (j + 1 + 1) * (gen (m + 1) (j + 1) * gen (m + 1) j * gen (m + 1) (j + 1)) := by
          simp only [mul_assoc]
      _ = tw m (j + 1 + 1) * (gen (m + 1) j * gen (m + 1) (j + 1) * gen (m + 1) j) := by
          rw [gen_braid (by omega)]
      _ = gen (m + 1) j * tw m (j + 1 + 1) * gen (m + 1) (j + 1) * gen (m + 1) j := by
          rw [← mul_assoc, ← mul_assoc, tw_mul_gen_comm _ _ rfl (by omega)]
      _ = gen (m + 1) j * (tw m (j + 1 + 1) * gen (m + 1) (j + 1) * gen (m + 1) j) := by
          simp only [mul_assoc]
  | succ d ih =>
    intro j i hi him
    have h1 : j ≤ m := by omega
    rw [tw_of_le h1, mul_assoc, gen_comm (m := m + 1) (by omega : j + 2 ≤ i), ← mul_assoc,
      ih (j + 1) i (by omega) him, mul_assoc]

theorem gen_mem_range {i : ℕ} (hi : i < m) : gen (m + 1) i ∈ (incl m).range :=
  ⟨gen m i, incl_gen hi⟩

theorem exists_mul_gen {x : TypeA (m + 1)} {k : TypeA (m + 1)} (hk : k ∈ (incl m).range)
    {j : ℕ} (hj : j ≤ m + 1) (hx : x = k * tw m j) {i : ℕ} (hi : i ≤ m) :
    ∃ k' ∈ (incl m).range, ∃ j' ≤ m + 1, x * gen (m + 1) i = k' * tw m j' := by
  subst hx
  rcases lt_trichotomy (i + 1) j with h | h | h
  · by_cases h2 : i + 2 ≤ j
    · refine ⟨k * gen (m + 1) i, mul_mem hk (gen_mem_range (by omega)), j, hj, ?_⟩
      rw [mul_assoc, tw_mul_gen_comm _ _ rfl h2, mul_assoc]
    · omega
  · refine ⟨k, hk, i, by omega, ?_⟩
    rw [← h, mul_assoc, ← tw_of_le hi]
  · rcases (by omega : i = j ∨ j < i) with h' | h'
    · subst h'
      exact ⟨k, hk, i + 1, by omega, by rw [mul_assoc, tw_mul_gen_self hi]⟩
    · refine ⟨k * gen (m + 1) (i - 1), mul_mem hk (gen_mem_range (by omega)), j, hj, ?_⟩
      rw [mul_assoc, tw_mul_gen_of_lt (i - (j + 1)) j i (by omega) hi, mul_assoc]

theorem closure_range_sA : Subgroup.closure (Set.range (sA (m := m))) = ⊤ :=
  PresentedGroup.closure_range_of _

theorem exists_eq_mul_tw (g : TypeA (m + 1)) :
    ∃ k ∈ (incl m).range, ∃ j ≤ m + 1, g = k * tw m j := by
  have hg : g ∈ Subgroup.closure (Set.range (sA (m := m + 1))) := by
    rw [closure_range_sA]; trivial
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨1, one_mem _, m + 1, le_rfl, by rw [tw_of_gt (by omega), mul_one]⟩
  | mul_right x _ y hy ih =>
    obtain ⟨i, rfl⟩ := hy
    obtain ⟨k, hk, j, hj, hx⟩ := ih
    have := exists_mul_gen hk hj hx (i := i) (by omega)
    rwa [gen_of_lt i.2] at this
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨i, rfl⟩ := hy
    obtain ⟨k, hk, j, hj, hx⟩ := ih
    have := exists_mul_gen hk hj hx (i := i) (by omega)
    rwa [← gen_inv, gen_of_lt i.2] at this

variable (m) in
theorem card_succ_le [Finite (TypeA m)] :
    Finite (TypeA (m + 1)) ∧ Nat.card (TypeA (m + 1)) ≤ Nat.card (TypeA m) * (m + 2) := by
  let φ : TypeA m × Fin (m + 2) → TypeA (m + 1) := fun p => incl m p.1 * tw m p.2
  have hφ : Function.Surjective φ := by
    intro g
    obtain ⟨_, ⟨k, rfl⟩, j, hj, rfl⟩ := exists_eq_mul_tw g
    exact ⟨(k, ⟨j, by omega⟩), rfl⟩
  refine ⟨Finite.of_surjective φ hφ, ?_⟩
  calc Nat.card (TypeA (m + 1)) ≤ Nat.card (TypeA m × Fin (m + 2)) :=
        Nat.card_le_card_of_surjective φ hφ
    _ = Nat.card (TypeA m) * (m + 2) := by rw [Nat.card_prod, Nat.card_fin]

end Cosets

theorem card_typeA_le (m : ℕ) : Finite (TypeA m) ∧ Nat.card (TypeA m) ≤ (m + 1).factorial := by
  induction m with
  | zero =>
    have h : ∀ g : TypeA 0, g = 1 := by
      intro g
      have hg : g ∈ Subgroup.closure (Set.range (sA (m := 0))) := by
        rw [closure_range_sA]; trivial
      rw [Set.range_eq_empty, Subgroup.closure_empty, Subgroup.mem_bot] at hg
      exact hg
    have : Subsingleton (TypeA 0) := ⟨fun a b => by rw [h a, h b]⟩
    exact ⟨inferInstance, by rw [Nat.card_unique]; exact Nat.factorial_pos _⟩
  | succ m ih =>
    have := ih.1
    obtain ⟨hfin, hle⟩ := card_succ_le m
    refine ⟨hfin, hle.trans ?_⟩
    calc Nat.card (TypeA m) * (m + 2) ≤ (m + 1).factorial * (m + 2) :=
          Nat.mul_le_mul_right _ ih.2
      _ = (m + 1 + 1).factorial := by rw [Nat.factorial_succ (m + 1), mul_comm]

theorem type_A_coxeter_normal_form (m : ℕ) :
    ∃ e : TypeA m ≃* Perm (Fin (m + 1)), (∀ i, e (sA i) = swap i.castSucc i.succ) ∧
      Nat.card (TypeA m) = (m + 1).factorial := by
  obtain ⟨hfin, hle⟩ := card_typeA_le m
  have hcard : Nat.card (Perm (Fin (m + 1))) = (m + 1).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hbij : Function.Bijective (toPerm m) :=
    (toPerm_surjective m).bijective_of_nat_card_le (hcard ▸ hle)
  refine ⟨MulEquiv.ofBijective (toPerm m) hbij, fun i => ?_, ?_⟩
  · rw [MulEquiv.ofBijective_apply, toPerm_sA]
    rfl
  · rw [Nat.card_congr (MulEquiv.ofBijective (toPerm m) hbij).toEquiv, hcard]

end CFSG.LocalAnalysis.ComponentInitial.MonE7
