module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open scoped commutatorElement

abbrev BSet : Type := Array Bool

namespace BSet

@[expose] def has (b : BSet) (i : ℕ) : Bool := b.getD i false

@[expose] def ofFn (n : ℕ) (f : ℕ → Bool) : BSet := (Array.range n).map f

@[expose] def count (n : ℕ) (b : BSet) : ℕ := (List.range n).countP b.has

theorem has_ofFn {n i : ℕ} (f : ℕ → Bool) (h : i < n) : (ofFn n f).has i = f i := by
  simp [has, ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, h]

theorem has_ofFn_ge {n i : ℕ} (f : ℕ → Bool) (h : n ≤ i) : (ofFn n f).has i = false := by
  have : ¬ i < n := by omega
  simp [has, ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, this]

theorem size_ofFn (n : ℕ) (f : ℕ → Bool) : (ofFn n f).size = n := by simp [ofFn]

end BSet

structure TabData where
  n : ℕ
  rows : Array (Array ℕ)
  invs : Array ℕ

namespace TabData

@[expose] def mul (D : TabData) (i j : ℕ) : ℕ := (D.rows.getD i #[]).getD j 0

@[expose] def inv (D : TabData) (i : ℕ) : ℕ := D.invs.getD i 0

@[expose] def pow (D : TabData) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => D.mul (D.pow i k) i

@[expose] def conj (D : TabData) (c x : ℕ) : ℕ := D.mul (D.mul c x) (D.inv c)

@[expose] def comm (D : TabData) (x y : ℕ) : ℕ := D.mul (D.mul (D.mul x y) (D.inv x)) (D.inv y)

end TabData

structure Realizes (D : TabData) {Γ : Type*} [Group Γ] (elt : ℕ → Γ) : Prop where
  zero : elt 0 = 1
  zero_lt : 0 < D.n
  mul_lt : ∀ i < D.n, ∀ j < D.n, D.mul i j < D.n
  elt_mul : ∀ i < D.n, ∀ j < D.n, elt (D.mul i j) = elt i * elt j
  inv_lt : ∀ i < D.n, D.inv i < D.n
  elt_inv : ∀ i < D.n, elt (D.inv i) = (elt i)⁻¹
  inj : ∀ i < D.n, ∀ j < D.n, elt i = elt j → i = j

variable {Γ : Type*} [Group Γ] {D : TabData} {elt : ℕ → Γ}

namespace Realizes

theorem pow_lt (hR : Realizes D elt) {i : ℕ} (hi : i < D.n) : ∀ k, D.pow i k < D.n
  | 0 => hR.zero_lt
  | k + 1 => hR.mul_lt _ (pow_lt hR hi k) _ hi

theorem elt_pow (hR : Realizes D elt) {i : ℕ} (hi : i < D.n) :
    ∀ k, elt (D.pow i k) = elt i ^ k
  | 0 => by simp [TabData.pow, hR.zero]
  | k + 1 => by
    rw [TabData.pow, hR.elt_mul _ (hR.pow_lt hi k) _ hi, elt_pow hR hi k, pow_succ]

theorem conj_lt (hR : Realizes D elt) {c x : ℕ} (hc : c < D.n) (hx : x < D.n) :
    D.conj c x < D.n :=
  hR.mul_lt _ (hR.mul_lt _ hc _ hx) _ (hR.inv_lt _ hc)

theorem elt_conj (hR : Realizes D elt) {c x : ℕ} (hc : c < D.n) (hx : x < D.n) :
    elt (D.conj c x) = elt c * elt x * (elt c)⁻¹ := by
  rw [TabData.conj, hR.elt_mul _ (hR.mul_lt _ hc _ hx) _ (hR.inv_lt _ hc),
    hR.elt_mul _ hc _ hx, hR.elt_inv _ hc]

theorem comm_lt (hR : Realizes D elt) {x y : ℕ} (hx : x < D.n) (hy : y < D.n) :
    D.comm x y < D.n :=
  hR.mul_lt _ (hR.mul_lt _ (hR.mul_lt _ hx _ hy) _ (hR.inv_lt _ hx)) _ (hR.inv_lt _ hy)

theorem elt_comm (hR : Realizes D elt) {x y : ℕ} (hx : x < D.n) (hy : y < D.n) :
    elt (D.comm x y) = ⁅elt x, elt y⁆ := by
  rw [TabData.comm, hR.elt_mul _ (hR.mul_lt _ (hR.mul_lt _ hx _ hy) _ (hR.inv_lt _ hx)) _
    (hR.inv_lt _ hy), hR.elt_mul _ (hR.mul_lt _ hx _ hy) _ (hR.inv_lt _ hx),
    hR.elt_mul _ hx _ hy, hR.elt_inv _ hx, hR.elt_inv _ hy, commutatorElement_def]

theorem mul_eq_iff (hR : Realizes D elt) {i j k l : ℕ} (hi : i < D.n) (hj : j < D.n)
    (hk : k < D.n) (hl : l < D.n) :
    D.mul i j = D.mul k l ↔ elt i * elt j = elt k * elt l := by
  rw [← hR.elt_mul _ hi _ hj, ← hR.elt_mul _ hk _ hl]
  exact ⟨fun h => by rw [h], hR.inj _ (hR.mul_lt _ hi _ hj) _ (hR.mul_lt _ hk _ hl)⟩

end Realizes

@[expose] def tabSet (D : TabData) (elt : ℕ → Γ) : Set Γ := {x | ∃ i < D.n, elt i = x}

@[expose] def Rep (D : TabData) (elt : ℕ → Γ) (b : BSet) (X : Set Γ) : Prop :=
  (∀ i < D.n, b.has i = true ↔ elt i ∈ X) ∧ ∀ x ∈ X, ∃ i < D.n, elt i = x

namespace Rep

theorem mem_iff {b : BSet} {X : Set Γ} (h : Rep D elt b X) {i : ℕ} (hi : i < D.n) :
    elt i ∈ X ↔ b.has i = true := (h.1 i hi).symm

theorem unique {b : BSet} {X Y : Set Γ} (hX : Rep D elt b X) (hY : Rep D elt b Y) : X = Y := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hX.2 x hx
    exact (hY.1 i hi).1 ((hX.1 i hi).2 hx)
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hY.2 x hx
    exact (hX.1 i hi).1 ((hY.1 i hi).2 hx)

theorem ext_bits {b c : BSet} {X Y : Set Γ} (hX : Rep D elt b X) (hY : Rep D elt c Y)
    (h : ∀ i < D.n, b.has i = c.has i) : X = Y := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hX.2 x hx
    exact (hY.1 i hi).1 ((h i hi) ▸ (hX.1 i hi).2 hx)
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hY.2 x hx
    exact (hX.1 i hi).1 ((h i hi) ▸ (hY.1 i hi).2 hx)

theorem subset_tabSet {b : BSet} {X : Set Γ} (h : Rep D elt b X) : X ⊆ tabSet D elt :=
  fun x hx => h.2 x hx

end Rep

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
