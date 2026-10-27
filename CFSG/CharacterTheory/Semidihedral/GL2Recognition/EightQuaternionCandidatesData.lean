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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

public section

namespace CFSG.Semidihedral.GL2Recognition

open Matrix

@[expose] def planePoint (v : Fin 2 → ZMod 3) : Fin 11 :=
  ⟨(v 0).val + 3 * (v 1).val, by
    have h0 := (v 0).val_lt
    have h1 := (v 1).val_lt
    omega⟩

@[expose] def planeVector (x : Fin 11) : Fin 2 → ZMod 3 :=
  ![((x.val % 3 : ℕ) : ZMod 3), ((x.val / 3 : ℕ) : ZMod 3)]

theorem planePoint_lt (v : Fin 2 → ZMod 3) : (planePoint v).val < 9 := by
  have h0 := (v 0).val_lt
  have h1 := (v 1).val_lt
  change (v 0).val + 3 * (v 1).val < 9
  omega

theorem planeVector_planePoint (v : Fin 2 → ZMod 3) : planeVector (planePoint v) = v := by
  revert v
  decide

theorem planePoint_planeVector (x : Fin 11) (hx : x.val < 9) : planePoint (planeVector x) = x := by
  revert x
  decide

theorem planePoint_injective : Function.Injective planePoint := fun v w h => by
  rw [← planeVector_planePoint v, h, planeVector_planePoint]

@[expose] def affineMap (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) (t : Fin 2 → ZMod 3) (x : Fin 11) :
    Fin 11 :=
  if x.val < 9 then planePoint (A *ᵥ planeVector x + t) else x

theorem affineMap_planePoint (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) (t v : Fin 2 → ZMod 3) :
    affineMap A t (planePoint v) = planePoint (A *ᵥ v + t) := by
  rw [affineMap, ite_eq_left (planePoint_lt v), planeVector_planePoint]

theorem affineMap_of_le (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) (t : Fin 2 → ZMod 3) (x : Fin 11)
    (hx : 9 ≤ x.val) : affineMap A t x = x := by
  rw [affineMap, ite_eq_right (by omega)]

theorem affineMap_affineMap (A B : Matrix (Fin 2) (Fin 2) (ZMod 3)) (t s : Fin 2 → ZMod 3)
    (x : Fin 11) : affineMap A t (affineMap B s x) = affineMap (A * B) (A *ᵥ s + t) x := by
  by_cases hx : x.val < 9
  · rw [← planePoint_planeVector x hx, affineMap_planePoint, affineMap_planePoint,
      affineMap_planePoint, mulVec_add, mulVec_mulVec, add_assoc]
  · rw [affineMap_of_le _ _ x (by omega), affineMap_of_le _ _ x (by omega),
      affineMap_of_le _ _ x (by omega)]

theorem affineMap_one_zero (x : Fin 11) : affineMap 1 0 x = x := by
  by_cases hx : x.val < 9
  · rw [← planePoint_planeVector x hx, affineMap_planePoint, one_mulVec, add_zero]
  · exact affineMap_of_le _ _ x (by omega)

@[expose] def affineInvMap (A : GL (Fin 2) (ZMod 3)) (t : Fin 2 → ZMod 3) : Fin 11 → Fin 11 :=
  affineMap ((A⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (-(((A⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ t))

theorem affineInvMap_affineMap (A : GL (Fin 2) (ZMod 3)) (t : Fin 2 → ZMod 3) (x : Fin 11) :
    affineInvMap A t (affineMap A t x) = x := by
  unfold affineInvMap
  rw [affineMap_affineMap, Units.inv_mul,
    show ∀ v : Fin 2 → ZMod 3, v + -v = 0 from fun v => add_neg_cancel v]
  exact affineMap_one_zero x

theorem affineMap_affineInvMap (A : GL (Fin 2) (ZMod 3)) (t : Fin 2 → ZMod 3) (x : Fin 11) :
    affineMap A t (affineInvMap A t x) = x := by
  unfold affineInvMap
  rw [affineMap_affineMap, Units.mul_inv,
    show ∀ v : Fin 2 → ZMod 3, (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ -v =
      -((A : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v) from fun v => mulVec_neg v _,
    mulVec_mulVec, Units.mul_inv, one_mulVec,
    show ∀ v : Fin 2 → ZMod 3, -v + v = 0 from fun v => neg_add_cancel v]
  exact affineMap_one_zero x

@[expose] def affinePerm (A : GL (Fin 2) (ZMod 3)) (t : Fin 2 → ZMod 3) : Equiv.Perm (Fin 11) where
  toFun := affineMap A t
  invFun := affineInvMap A t
  left_inv := affineInvMap_affineMap A t
  right_inv := affineMap_affineInvMap A t

theorem affinePerm_planePoint (A : GL (Fin 2) (ZMod 3)) (t v : Fin 2 → ZMod 3) :
    affinePerm A t (planePoint v) = planePoint ((A : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v + t) :=
  affineMap_planePoint _ _ _

theorem affinePerm_of_le (A : GL (Fin 2) (ZMod 3)) (t : Fin 2 → ZMod 3) (x : Fin 11)
    (hx : 9 ≤ x.val) : affinePerm A t x = x :=
  affineMap_of_le _ _ x hx

@[expose] def I₀ : GL (Fin 2) (ZMod 3) :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by decide, by decide⟩

@[expose] def J₀ : GL (Fin 2) (ZMod 3) :=
  ⟨!![1, 1; 1, -1], !![-1, -1; -1, 1], by decide, by decide⟩

@[expose] def vecE : Fin 2 → ZMod 3 := ![1, 0]

@[expose] def genH₁ : Equiv.Perm (Fin 11) := affinePerm 1 ![1, 0]

@[expose] def genH₂ : Equiv.Perm (Fin 11) := affinePerm 1 ![0, 1]

@[expose] def genH₃ : Equiv.Perm (Fin 11) := affinePerm I₀ 0

@[expose] def genH₄ : Equiv.Perm (Fin 11) := affinePerm J₀ 0

@[expose] def qElem : Fin 8 → GL (Fin 2) (ZMod 3) :=
  ![1, I₀, J₀, I₀ * I₀, I₀ * J₀, J₀ * I₀, I₀ * I₀ * I₀, J₀ * J₀ * J₀]

@[expose] def qMul : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 3, 4, 6, 7, 2, 0, 5], ![2, 5, 3, 7, 1, 6, 4, 0],
    ![3, 6, 7, 0, 5, 4, 1, 2], ![4, 2, 6, 5, 3, 0, 7, 1], ![5, 7, 1, 4, 0, 3, 2, 6],
    ![6, 0, 5, 1, 2, 7, 3, 4], ![7, 4, 0, 2, 6, 1, 5, 3]]

@[expose] def qInv : Fin 8 → Fin 8 := ![0, 6, 7, 3, 5, 4, 1, 2]

theorem qElem_mul : ∀ i j, qElem i * qElem j = qElem (qMul i j) := by
  decide +kernel

theorem qElem_inv : ∀ i, (qElem i)⁻¹ = qElem (qInv i) := by
  decide +kernel

theorem qElem_injective : Function.Injective qElem := by
  intro i j h
  revert i j
  decide +kernel

@[expose] def ptTable : Fin 8 → Fin 11 := ![1, 6, 4, 2, 7, 5, 3, 8]

theorem planePoint_qElem_vecE :
    ∀ j, planePoint ((qElem j : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ vecE) = ptTable j := by
  decide +kernel

theorem point_cases : ∀ x : Fin 11, x = 9 ∨ x = 10 ∨ x = 0 ∨ ∃ j, x = ptTable j := by
  decide

@[expose] def autArray (a b : Fin 8) : Fin 8 → Fin 8 :=
  ![0, a, b, qMul a a, qMul a b, qMul b a, qMul (qMul a a) a, qMul (qMul b b) b]

@[expose] def candA : Fin 8 → Fin 8 := ![2, 2, 4, 4, 5, 5, 7, 7]

@[expose] def candB : Fin 8 → Fin 8 := ![4, 5, 1, 6, 1, 6, 4, 5]

theorem autArray_cand : ∀ k, autArray (candA k) (candB k) =
    ![![0, 2, 4, 3, 1, 6, 7, 5], ![0, 2, 5, 3, 6, 1, 7, 4], ![0, 4, 1, 3, 2, 7, 5, 6],
      ![0, 4, 6, 3, 7, 2, 5, 1], ![0, 5, 1, 3, 7, 2, 4, 6], ![0, 5, 6, 3, 2, 7, 4, 1],
      ![0, 7, 4, 3, 6, 1, 2, 5], ![0, 7, 5, 3, 1, 6, 2, 4]] k := by
  decide +kernel

theorem autArray_classification : ∀ a b : Fin 8,
    (∀ i j, autArray a b i = autArray a b j → i = j) →
    (∀ i j, autArray a b (qMul i j) = qMul (autArray a b i) (autArray a b j)) →
    (∀ i, autArray a b (autArray a b (autArray a b i)) = i) →
    (∃ i, autArray a b i ≠ i) →
    ∃ k, candA k = a ∧ candB k = b := by
  decide +kernel

@[expose] def tablePerm (f g : Fin 11 → Fin 11) (hgf : ∀ x, g (f x) = x) (hfg : ∀ x, f (g x) = x) :
    Equiv.Perm (Fin 11) :=
  ⟨f, g, hgf, hfg⟩

@[expose] def sigmaCand : Fin 8 → Equiv.Perm (Fin 11) :=
  ![tablePerm ![9, 1, 2, 8, 7, 3, 4, 6, 5, 10, 0] ![10, 1, 2, 5, 6, 8, 7, 4, 3, 0, 9]
      (by decide) (by decide),
    tablePerm ![9, 1, 2, 8, 5, 6, 4, 3, 7, 10, 0] ![10, 1, 2, 7, 6, 4, 5, 8, 3, 0, 9]
      (by decide) (by decide),
    tablePerm ![9, 1, 2, 5, 6, 8, 7, 4, 3, 10, 0] ![10, 1, 2, 8, 7, 3, 4, 6, 5, 0, 9]
      (by decide) (by decide),
    tablePerm ![9, 1, 2, 5, 3, 4, 7, 8, 6, 10, 0] ![10, 1, 2, 4, 5, 3, 8, 6, 7, 0, 9]
      (by decide) (by decide),
    tablePerm ![9, 1, 2, 7, 6, 4, 5, 8, 3, 10, 0] ![10, 1, 2, 8, 5, 6, 4, 3, 7, 0, 9]
      (by decide) (by decide),
    tablePerm ![9, 1, 2, 7, 3, 8, 5, 4, 6, 10, 0] ![10, 1, 2, 4, 7, 6, 8, 3, 5, 0, 9]
      (by decide) (by decide),
    tablePerm ![9, 1, 2, 4, 7, 6, 8, 3, 5, 10, 0] ![10, 1, 2, 7, 3, 8, 5, 4, 6, 0, 9]
      (by decide) (by decide),
    tablePerm ![9, 1, 2, 4, 5, 3, 8, 6, 7, 10, 0] ![10, 1, 2, 5, 3, 4, 7, 8, 6, 0, 9]
      (by decide) (by decide)]

theorem sigmaCand_triple : ∀ k, sigmaCand k 9 = 10 ∧ sigmaCand k 10 = 0 ∧ sigmaCand k 0 = 9 := by
  decide +kernel

theorem sigmaCand_ptTable :
    ∀ k j, sigmaCand k (ptTable j) = ptTable (autArray (candA k) (candB k) j) := by
  decide +kernel

@[expose] def signedWord (gens : List (Equiv.Perm (Fin 11))) (w : List ℤ) :
    Equiv.Perm (Fin 11) :=
  (w.map fun i => if 0 < i then gens.getD (i.toNat - 1) 1 else (gens.getD (i.natAbs - 1) 1)⁻¹).prod

theorem signedWord_mem (K : Subgroup (Equiv.Perm (Fin 11))) (gens : List (Equiv.Perm (Fin 11)))
    (hgens : ∀ g ∈ gens, g ∈ K) (w : List ℤ) : signedWord gens w ∈ K := by
  have hget : ∀ n, gens.getD n 1 ∈ K := fun n => by
    rw [List.getD_eq_getElem?_getD]
    cases h : gens[n]? with
    | none => exact K.one_mem
    | some g => exact hgens g (List.mem_of_getElem? h)
  refine K.list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  split
  · exact hget _
  · exact K.inv_mem (hget _)

@[expose] def m11GenA : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]

@[expose] def m11GenB : Equiv.Perm (Fin 11) :=
  List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]

@[expose] def conjCand : Fin 8 → Equiv.Perm (Fin 11) :=
  ![tablePerm ![0, 1, 2, 3, 7, 4, 10, 5, 9, 8, 6] ![0, 1, 2, 3, 5, 7, 10, 4, 9, 8, 6]
      (by decide) (by decide),
    tablePerm ![0, 1, 2, 3, 6, 8, 4, 9, 7, 5, 10] ![0, 1, 2, 3, 6, 9, 4, 8, 5, 7, 10]
      (by decide) (by decide),
    tablePerm ![0, 1, 2, 3, 7, 4, 9, 5, 10, 8, 6] ![0, 1, 2, 3, 5, 7, 10, 4, 9, 6, 8]
      (by decide) (by decide),
    1,
    tablePerm ![0, 1, 2, 3, 6, 8, 4, 10, 7, 5, 9] ![0, 1, 2, 3, 6, 9, 4, 8, 5, 10, 7]
      (by decide) (by decide),
    tablePerm ![0, 1, 2, 3, 8, 9, 7, 6, 5, 10, 4] ![0, 1, 2, 3, 10, 8, 7, 6, 4, 5, 9]
      (by decide) (by decide),
    tablePerm ![0, 1, 2, 3, 8, 10, 7, 6, 5, 9, 4] ![0, 1, 2, 3, 10, 8, 7, 6, 4, 9, 5]
      (by decide) (by decide),
    1]

@[expose] def wordA : Fin 8 → List ℤ :=
  ![[5, -1, -2, 5, 2, 5], [1, -2, 5, 2, 5, 1, -3], [5, -2, 5, 1, 2, 5], [],
    [1, -2, -5, 2, -4, -5, -2], [3, 3, -5, -1, 5], [3, 3, 5, -1, -5], []]

@[expose] def wordB : Fin 8 → List ℤ :=
  ![[2, -3, 5, 2, -5], [2, 3, 5, 1, -5], [2, -3, -5, 2, 5], [],
    [2, 3, -5, 1, 5], [2, 5, -1, -5, 4], [2, -5, -1, 5, 4], []]

@[expose] def candGens (k : Fin 8) : List (Equiv.Perm (Fin 11)) :=
  [genH₁, genH₂, genH₃, genH₄, sigmaCand k]

theorem conjCand_m11GenA : ∀ k, k ≠ 3 → k ≠ 7 →
    conjCand k * m11GenA * (conjCand k)⁻¹ = signedWord (candGens k) (wordA k) := by
  decide +kernel

theorem conjCand_m11GenB : ∀ k, k ≠ 3 → k ≠ 7 →
    conjCand k * m11GenB * (conjCand k)⁻¹ = signedWord (candGens k) (wordB k) := by
  decide +kernel

theorem fixedWord_cand : ∀ k, (k = 3 ∨ k = 7) →
    signedWord (candGens k) [1, 5, -1, -5] ≠ 1 ∧
      4 ≤ (Finset.univ.filter fun x => signedWord (candGens k) [1, 5, -1, -5] x = x).card := by
  decide +kernel

end CFSG.Semidihedral.GL2Recognition
