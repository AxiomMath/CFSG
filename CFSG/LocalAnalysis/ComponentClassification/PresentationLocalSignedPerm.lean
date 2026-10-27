module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SemidirectProduct

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Tactic.Ring.RingNF

public noncomputable section

namespace CFSG.ComponentClassification.PresentationLocal

open Equiv

variable {n : ℕ}

@[expose] def basisVec (i : Fin n) : Fin n → ZMod 2 := Pi.single i 1

@[expose] def permVec (σ : Perm (Fin n)) (v : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun j => v (σ⁻¹ j)

variable (n) in
@[expose] def evenSubspace : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {v | ∑ i, v i = 0}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at hv hw ⊢
    rw [hv, hw, add_zero]
  zero_mem' := by simp
  smul_mem' c v hv := by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hv ⊢
    rw [hv, mul_zero]

theorem mem_evenSubspace {v : Fin n → ZMod 2} : v ∈ evenSubspace n ↔ ∑ i, v i = 0 := Iff.rfl

@[simp] theorem permVec_apply (σ : Perm (Fin n)) (v : Fin n → ZMod 2) (j : Fin n) :
    permVec σ v j = v (σ⁻¹ j) := rfl

@[simp] theorem permVec_one (v : Fin n → ZMod 2) : permVec 1 v = v := rfl

theorem permVec_mul (σ τ : Perm (Fin n)) (v : Fin n → ZMod 2) :
    permVec (σ * τ) v = permVec σ (permVec τ v) := by
  funext j
  simp [mul_inv_rev, Perm.mul_apply]

@[simp] theorem permVec_add (σ : Perm (Fin n)) (v w : Fin n → ZMod 2) :
    permVec σ (v + w) = permVec σ v + permVec σ w := rfl

@[simp] theorem permVec_zero (σ : Perm (Fin n)) : permVec σ 0 = 0 := rfl

theorem permVec_basisVec (σ : Perm (Fin n)) (i : Fin n) :
    permVec σ (basisVec i) = basisVec (σ i) := by
  funext j
  simp only [permVec_apply, basisVec, Pi.single_apply, Perm.inv_eq_iff_eq]

theorem sum_permVec (σ : Perm (Fin n)) (v : Fin n → ZMod 2) :
    ∑ j, permVec σ v j = ∑ j, v j :=
  Equiv.sum_comp σ⁻¹ v

theorem permVec_mem (σ : Perm (Fin n)) {v : Fin n → ZMod 2} (hv : v ∈ evenSubspace n) :
    permVec σ v ∈ evenSubspace n := by
  rw [mem_evenSubspace, sum_permVec]
  exact hv

theorem basisVec_add_basisVec_mem (i j : Fin n) : basisVec i + basisVec j ∈ evenSubspace n := by
  rw [mem_evenSubspace]
  simp only [basisVec, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single',
    Finset.mem_univ, ite_true]
  decide

@[expose] def permAddAut (σ : Perm (Fin n)) : evenSubspace n ≃+ evenSubspace n where
  toFun v := ⟨permVec σ v, permVec_mem σ v.2⟩
  invFun v := ⟨permVec σ⁻¹ v, permVec_mem σ⁻¹ v.2⟩
  left_inv v := Subtype.ext (by
    change permVec σ⁻¹ (permVec σ v) = v
    rw [← permVec_mul, inv_mul_cancel, permVec_one])
  right_inv v := Subtype.ext (by
    change permVec σ (permVec σ⁻¹ v) = v
    rw [← permVec_mul, mul_inv_cancel, permVec_one])
  map_add' _ _ := rfl

variable (n) in
@[expose] def permAut : Perm (Fin n) →* MulAut (Multiplicative (evenSubspace n)) where
  toFun σ := AddEquiv.toMultiplicative (permAddAut σ)
  map_one' := by
    ext v
    rfl
  map_mul' σ τ := by
    ext v j
    exact congrFun (permVec_mul σ τ _) j

variable (n) in
abbrev W : Type := Multiplicative (evenSubspace n) ⋊[permAut n] Perm (Fin n)

@[expose] def vec (x : W n) : Fin n → ZMod 2 :=
  ((Multiplicative.toAdd x.left : evenSubspace n) : Fin n → ZMod 2)

@[expose] def mk (v : Fin n → ZMod 2) (hv : v ∈ evenSubspace n) (σ : Perm (Fin n)) : W n :=
  ⟨Multiplicative.ofAdd ⟨v, hv⟩, σ⟩

theorem vec_mem (x : W n) : vec x ∈ evenSubspace n := (Multiplicative.toAdd x.left).2

@[simp] theorem vec_mk (v : Fin n → ZMod 2) (hv : v ∈ evenSubspace n) (σ : Perm (Fin n)) :
    vec (mk v hv σ) = v := rfl

@[simp] theorem right_mk (v : Fin n → ZMod 2) (hv : v ∈ evenSubspace n) (σ : Perm (Fin n)) :
    (mk v hv σ).right = σ := rfl

theorem eq_mk (x : W n) : x = mk (vec x) (vec_mem x) x.right := rfl

theorem ext_vec {x y : W n} (hv : vec x = vec y) (hr : x.right = y.right) : x = y :=
  SemidirectProduct.ext (congrArg Multiplicative.ofAdd (Subtype.ext hv)) hr

theorem ext_vec_iff {x y : W n} : x = y ↔ vec x = vec y ∧ x.right = y.right :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => ext_vec h.1 h.2⟩

theorem vec_mul (x y : W n) : vec (x * y) = vec x + permVec x.right (vec y) := rfl

@[simp] theorem right_mul (x y : W n) : (x * y).right = x.right * y.right := rfl

@[simp] theorem vec_one : vec (1 : W n) = 0 := rfl

@[simp] theorem right_one : (1 : W n).right = 1 := rfl

theorem mk_mul_mk (v w : Fin n → ZMod 2) (hv : v ∈ evenSubspace n) (hw : w ∈ evenSubspace n)
    (σ τ : Perm (Fin n)) :
    mk v hv σ * mk w hw τ =
      mk (v + permVec σ w) (Submodule.add_mem _ hv (permVec_mem σ hw)) (σ * τ) := rfl

@[simp] theorem right_inv' (x : W n) : x⁻¹.right = x.right⁻¹ := rfl

theorem vec_inv (x : W n) : vec x⁻¹ = permVec x.right⁻¹ (vec x) := by
  change permVec x.right⁻¹ (-vec x) = permVec x.right⁻¹ (vec x)
  congr 1
  funext j
  exact ZMod.neg_eq_self_mod_two _

@[simp] theorem vec_inl (v : evenSubspace n) :
    vec (SemidirectProduct.inl (Multiplicative.ofAdd v) : W n) = v := rfl

@[simp] theorem vec_inr (σ : Perm (Fin n)) : vec (SemidirectProduct.inr σ : W n) = 0 := rfl

theorem mk_zero (σ : Perm (Fin n)) :
    mk 0 (Submodule.zero_mem _) σ = SemidirectProduct.inr σ := rfl

variable (n) in
@[expose] def signSubgroup : Subgroup (W n) := (SemidirectProduct.inl).range

theorem mem_signSubgroup_iff {x : W n} : x ∈ signSubgroup n ↔ x.right = 1 := by
  rw [signSubgroup, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
    SemidirectProduct.rightHom_eq_right]

@[expose] def sZero (h : 1 < n) : W n :=
  mk (basisVec ⟨0, by omega⟩ + basisVec ⟨1, h⟩) (basisVec_add_basisVec_mem _ _)
    (swap ⟨0, by omega⟩ ⟨1, h⟩)

@[expose] def s (i : Fin n) : W n :=
  if h : (i : ℕ) = 0 ∧ 1 < n then sZero h.2
  else mk 0 (Submodule.zero_mem _) (swap ⟨i - 1, by omega⟩ i)

theorem s_zero (h : 1 < n) : s (⟨0, by omega⟩ : Fin n) = sZero h := by
  rw [s, dite_eq_left ⟨rfl, h⟩]

theorem s_of_ne_zero {i : Fin n} (hi : (i : ℕ) ≠ 0) :
    s i = mk 0 (Submodule.zero_mem _) (swap ⟨i - 1, by omega⟩ i) := by
  rw [s, dite_eq_right fun h => hi h.1]

variable (R : Type*) [CommRing R]

@[expose] def negOnePow (a : ZMod 2) : R := (-1) ^ a.val

@[simp] theorem negOnePow_zero : negOnePow R 0 = 1 := by simp [negOnePow]

@[simp] theorem negOnePow_one : negOnePow R 1 = -1 := by
  simp [negOnePow, ZMod.val_one]

theorem negOnePow_add (a b : ZMod 2) : negOnePow R (a + b) = negOnePow R a * negOnePow R b := by
  rw [negOnePow, negOnePow, negOnePow, ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

@[expose] def signedPermAction : W n →* Module.End R (Fin n → R) where
  toFun x :=
    { toFun := fun f j => negOnePow R (vec x j) * f (x.right⁻¹ j)
      map_add' := fun f g => by
        funext j
        simp [mul_add]
      map_smul' := fun c f => by
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_one' := by
    refine LinearMap.ext fun f => funext fun j => ?_
    simp
  map_mul' x y := by
    refine LinearMap.ext fun f => funext fun j => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, vec_mul, right_mul,
      mul_inv_rev, Perm.mul_apply, Pi.add_apply, permVec_apply, negOnePow_add]
    ring

theorem signedPermAction_apply (x : W n) (f : Fin n → R) (j : Fin n) :
    signedPermAction R x f j = negOnePow R (vec x j) * f (x.right⁻¹ j) := rfl

theorem signedPermAction_single (x : W n) (i : Fin n) :
    signedPermAction R x (Pi.single i 1) =
      negOnePow R (vec x (x.right i)) • Pi.single (x.right i) 1 := by
  funext j
  rw [signedPermAction_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = x.right i
  · subst hj
    simp
  · have : x.right⁻¹ j ≠ i := fun h => hj (Perm.inv_eq_iff_eq.1 h)
    rw [Pi.single_eq_of_ne this, Pi.single_eq_of_ne hj, mul_zero, mul_zero]

@[expose] def simpleRoot (i : Fin n) : Fin n → R :=
  if h : (i : ℕ) = 0 ∧ 1 < n then -Pi.single ⟨0, by omega⟩ 1 - Pi.single ⟨1, h.2⟩ 1
  else Pi.single ⟨i - 1, by omega⟩ 1 - Pi.single i 1

@[expose] def roots : Set (Fin n → R) :=
  {x | ∃ i j : Fin n, i < j ∧ ∃ ε δ : R, (ε = 1 ∨ ε = -1) ∧ (δ = 1 ∨ δ = -1) ∧
    x = ε • Pi.single i 1 + δ • Pi.single j 1}

@[expose] def posRoots : Set (Fin n → R) :=
  {x | ∃ i j : Fin n, i < j ∧
    (x = Pi.single i 1 - Pi.single j 1 ∨ x = -Pi.single i 1 - Pi.single j 1)}

@[expose] def negRoots : Set (Fin n → R) := {x | -x ∈ posRoots R}

@[expose] def forkEdge (i j : Fin n) : Prop :=
  ((i : ℕ) = 0 ∧ (j : ℕ) = 2) ∨ ((i : ℕ) = 1 ∧ (j : ℕ) = 2) ∨ (2 ≤ (i : ℕ) ∧ (j : ℕ) = i + 1)

variable (n) in
@[expose] def forkGraph : SimpleGraph (Fin n) := SimpleGraph.fromRel forkEdge

theorem forkGraph_adj_iff {i j : Fin n} :
    (forkGraph n).Adj i j ↔
      ((i : ℕ) = 0 ∧ (j : ℕ) = 2) ∨ ((i : ℕ) = 2 ∧ (j : ℕ) = 0) ∨
        ((i : ℕ) = 1 ∧ (j : ℕ) = 2) ∨ ((i : ℕ) = 2 ∧ (j : ℕ) = 1) ∨
        (2 ≤ (i : ℕ) ∧ (j : ℕ) = i + 1) ∨ (2 ≤ (j : ℕ) ∧ (i : ℕ) = j + 1) := by
  rw [forkGraph, SimpleGraph.fromRel_adj, forkEdge, forkEdge]
  constructor
  · rintro ⟨-, h⟩
    omega
  · intro h
    refine ⟨fun hij => ?_, by omega⟩
    subst hij
    omega

instance : DecidableRel (forkGraph n).Adj := fun _ _ =>
  decidable_of_iff _ forkGraph_adj_iff.symm

@[expose] def coxeterEntry (i j : Fin n) : ℕ := if (forkGraph n).Adj i j then 3 else 2

theorem even_signed_permutation_data (hn : 4 ≤ n) :
    (∀ v : Fin n → ZMod 2, v ∈ evenSubspace n ↔ ∑ i, v i = 0) ∧
    (∀ (σ : Perm (Fin n)) (i : Fin n), permVec σ (basisVec i) = basisVec (σ i)) ∧
    (∀ (σ : Perm (Fin n)) (v : Fin n → ZMod 2), v ∈ evenSubspace n →
      permVec σ v ∈ evenSubspace n) ∧
    (∀ (v w : Fin n → ZMod 2) (hv : v ∈ evenSubspace n) (hw : w ∈ evenSubspace n)
      (σ τ : Perm (Fin n)), mk v hv σ * mk w hw τ =
        mk (v + permVec σ w) (Submodule.add_mem _ hv (permVec_mem σ hw)) (σ * τ)) ∧
    (∀ x : W n, x = mk (vec x) (vec_mem x) x.right) ∧
    (∀ x : W n, x ∈ signSubgroup n ↔ x.right = 1) ∧
    s (⟨0, by omega⟩ : Fin n) =
      mk (basisVec ⟨0, by omega⟩ + basisVec ⟨1, by omega⟩) (basisVec_add_basisVec_mem _ _)
        (swap ⟨0, by omega⟩ ⟨1, by omega⟩) ∧
    s (⟨1, by omega⟩ : Fin n) =
      mk 0 (Submodule.zero_mem _) (swap ⟨0, by omega⟩ ⟨1, by omega⟩) ∧
    (∀ i : Fin n, ∀ hi : 2 ≤ (i : ℕ),
      s i = mk 0 (Submodule.zero_mem _) (swap ⟨i - 1, by omega⟩ i)) ∧
    (∀ (x : W n) (i : Fin n), signedPermAction ℝ x (Pi.single i 1) =
      negOnePow ℝ (vec x (x.right i)) • Pi.single (x.right i) 1) ∧
    simpleRoot ℝ (⟨0, by omega⟩ : Fin n) =
      -Pi.single ⟨0, by omega⟩ 1 - Pi.single ⟨1, by omega⟩ 1 ∧
    (∀ i : Fin n, ∀ hi : 1 ≤ (i : ℕ),
      simpleRoot ℝ i = Pi.single ⟨i - 1, by omega⟩ 1 - Pi.single i 1) ∧
    (∀ x : Fin n → ℝ, x ∈ roots ℝ ↔ ∃ i j : Fin n, i < j ∧ ∃ ε δ : ℝ, (ε = 1 ∨ ε = -1) ∧
      (δ = 1 ∨ δ = -1) ∧ x = ε • Pi.single i 1 + δ • Pi.single j 1) ∧
    (∀ x : Fin n → ℝ, x ∈ posRoots ℝ ↔ ∃ i j : Fin n, i < j ∧
      (x = Pi.single i 1 - Pi.single j 1 ∨ x = -Pi.single i 1 - Pi.single j 1)) ∧
    (∀ x : Fin n → ℝ, x ∈ negRoots ℝ ↔ -x ∈ posRoots ℝ) ∧
    (∀ i j : Fin n, (forkGraph n).Adj i j ↔
      ((i : ℕ) = 0 ∧ (j : ℕ) = 2) ∨ ((i : ℕ) = 2 ∧ (j : ℕ) = 0) ∨
        ((i : ℕ) = 1 ∧ (j : ℕ) = 2) ∨ ((i : ℕ) = 2 ∧ (j : ℕ) = 1) ∨
        (2 ≤ (i : ℕ) ∧ (j : ℕ) = i + 1) ∨ (2 ≤ (j : ℕ) ∧ (i : ℕ) = j + 1)) ∧
    (∀ i j : Fin n, i ≠ j → (forkGraph n).Adj i j → coxeterEntry i j = 3) ∧
    (∀ i j : Fin n, i ≠ j → ¬ (forkGraph n).Adj i j → coxeterEntry i j = 2) := by
  refine ⟨fun _ => Iff.rfl, permVec_basisVec, fun σ _ hv => permVec_mem σ hv,
    fun _ _ _ _ _ _ => rfl, eq_mk, fun _ => mem_signSubgroup_iff, s_zero (by omega),
    s_of_ne_zero (by simp), fun i hi => s_of_ne_zero (by omega),
    signedPermAction_single ℝ, ?_, fun i hi => ?_, fun _ => Iff.rfl, fun _ => Iff.rfl,
    fun _ => Iff.rfl, fun _ _ => forkGraph_adj_iff, fun i j _ h => ite_eq_left h,
    fun i j _ h => ite_eq_right h⟩
  · rw [simpleRoot, dite_eq_left ⟨rfl, by omega⟩]
  · rw [simpleRoot, dite_eq_right fun h => by omega]

end CFSG.ComponentClassification.PresentationLocal
