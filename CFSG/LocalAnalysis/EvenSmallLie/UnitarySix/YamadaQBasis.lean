module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup
open scoped commutatorElement

section VProd

variable {A : Type*} [CommGroup A] {n : ℕ}

@[expose] def vprod (b : Fin n → A) (v : Fin n → ZMod 2) : A := ∏ i, if v i = 0 then 1 else b i

theorem zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

theorem ite_add_eq {b : A} (hb : b * b = 1) (x y : ZMod 2) :
    (if x + y = 0 then 1 else b) = (if x = 0 then 1 else b) * (if y = 0 then 1 else b) := by
  rcases zmod_two_cases x with rfl | rfl <;> rcases zmod_two_cases y with rfl | rfl <;>
    simp [hb, show (1 : ZMod 2) + 1 = 0 from rfl]

theorem vprod_add {b : Fin n → A} (hb : ∀ i, b i * b i = 1) (v w : Fin n → ZMod 2) :
    vprod b (v + w) = vprod b v * vprod b w := by
  simp only [vprod, ← Finset.prod_mul_distrib, Pi.add_apply, ite_add_eq (hb _)]

theorem vprod_zero (b : Fin n → A) : vprod b 0 = 1 := by simp [vprod]

theorem vprod_sum {b : Fin n → A} (hb : ∀ i, b i * b i = 1) {ι : Type*} (s : Finset ι)
    (f : ι → Fin n → ZMod 2) : vprod b (∑ j ∈ s, f j) = ∏ j ∈ s, vprod b (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vprod_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, vprod_add hb, ih]

theorem vprod_smul (b : Fin n → A) (c : ZMod 2) (v : Fin n → ZMod 2) :
    vprod b (c • v) = if c = 0 then 1 else vprod b v := by
  rcases zmod_two_cases c with rfl | rfl
  · simp [vprod]
  · simp [vprod]

theorem vprod_single [DecidableEq (Fin n)] (b : Fin n → A) (i : Fin n) :
    vprod b (Pi.single i 1) = b i := by
  simp only [vprod]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem map_vprod {B : Type*} [CommGroup B] (f : A →* B) (b : Fin n → A) (v : Fin n → ZMod 2) :
    f (vprod b v) = vprod (fun i => f (b i)) v := by
  simp only [vprod, map_prod]
  exact Finset.prod_congr rfl fun i _ => by split_ifs <;> simp

theorem mulVec_eq_sum (M : Matrix (Fin n) (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    M.mulVec v = ∑ j, v j • (fun i => M i j) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem vprod_mulVec {b c : Fin n → A} (hb : ∀ i, b i * b i = 1)
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (hc : ∀ j, c j = vprod b (fun i => M i j))
    (v : Fin n → ZMod 2) : vprod c v = vprod b (M.mulVec v) := by
  rw [mulVec_eq_sum, vprod_sum hb]
  simp only [vprod_smul, ← hc]
  rfl

end VProd

section Commutator

variable {G : Type*} [Group G]

theorem commutator_closure_le {S T : Set G} {V : Subgroup G}
    (hS : ∀ s ∈ S, s ∈ normalizer (V : Set G)) (hT : ∀ m ∈ T, m ∈ normalizer (V : Set G))
    (h : ∀ m ∈ T, ∀ s ∈ S, ⁅m, s⁆ ∈ V) : ⁅closure T, closure S⁆ ≤ V := by
  have hTN : closure T ≤ normalizer (V : Set G) := (closure_le _).mpr hT
  have hSN : closure S ≤ normalizer (V : Set G) := (closure_le _).mpr hS
  have hV : ∀ {g v : G}, g ∈ normalizer (V : Set G) → v ∈ V → g * v * g⁻¹ ∈ V :=
    fun hg hv => (mem_normalizer_iff.mp hg _).mp hv
  have step1 : ∀ s ∈ S, ∀ m ∈ closure T, ⁅m, s⁆ ∈ V := by
    intro s hs m hm
    induction hm using closure_induction with
    | mem x hx => exact h x hx s hs
    | one => simp
    | mul x y hx hy ihx ihy =>
      have e : ⁅x * y, s⁆ = x * ⁅y, s⁆ * x⁻¹ * ⁅x, s⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem (hV (hTN hx) ihy) ihx
    | inv x hx ihx =>
      have e : ⁅x⁻¹, s⁆ = x⁻¹ * ⁅x, s⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hV (inv_mem (hTN hx)) (inv_mem ihx)
  rw [commutator_le]
  intro m hm q hq
  induction hq using closure_induction with
  | mem x hx => exact step1 x hx m hm
  | one => simp
  | mul x y hx hy ihx ihy =>
    have e : ⁅m, x * y⁆ = ⁅m, x⁆ * (x * ⁅m, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem ihx (hV (hSN hx) ihy)
  | inv x hx ihx =>
    have e : ⁅m, x⁻¹⁆ = x⁻¹ * ⁅m, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hV (inv_mem (hSN hx)) (inv_mem ihx)

end Commutator

section KProd

variable {G : Type*} [Group G] {K : Subgroup G}

@[expose, reducible] def commGroupOf (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) : CommGroup K :=
  { (inferInstance : Group K) with mul_comm := fun a b => Subtype.ext (hK _ a.2 _ b.2) }

@[expose] def kprod (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) {n : ℕ} (b : Fin n → K)
    (v : Fin n → ZMod 2) : G :=
  ((@vprod K (commGroupOf hK) n b v : K) : G)

variable {hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a} {n : ℕ} {b : Fin n → K}

theorem kprod_mem (v : Fin n → ZMod 2) : kprod hK b v ∈ K := (@vprod K (commGroupOf hK) n b v).2

theorem kprod_add (hb : ∀ i, (b i : G) * b i = 1) (v w : Fin n → ZMod 2) :
    kprod hK b (v + w) = kprod hK b v * kprod hK b w := by
  let _ := commGroupOf hK
  have hb' : ∀ i, b i * b i = 1 := fun i => Subtype.ext (hb i)
  simp only [kprod]
  rw [vprod_add hb']
  rfl

theorem kprod_zero : kprod hK b 0 = 1 := by
  let _ := commGroupOf hK
  simp only [kprod]
  rw [vprod_zero]
  rfl

theorem kprod_single [DecidableEq (Fin n)] (i : Fin n) : kprod hK b (Pi.single i 1) = b i := by
  let _ := commGroupOf hK
  simp only [kprod]
  rw [vprod_single]

theorem kprod_mul_self (hb : ∀ i, (b i : G) * b i = 1) (v : Fin n → ZMod 2) :
    kprod hK b v * kprod hK b v = 1 := by
  rw [← kprod_add hb, show v + v = 0 by ext i; simp [← two_mul, show (2 : ZMod 2) = 0 from rfl],
    kprod_zero]

theorem kprod_conj (hb : ∀ i, (b i : G) * b i = 1) {g : G} (hg : g ∈ normalizer (K : Set G))
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hM : ∀ j, g * (b j : G) * g⁻¹ = kprod hK b (fun i => M i j)) (v : Fin n → ZMod 2) :
    g * kprod hK b v * g⁻¹ = kprod hK b (M.mulVec v) := by
  let _ := commGroupOf hK
  have hb' : ∀ i, b i * b i = 1 := fun i => Subtype.ext (hb i)
  let f : K →* K :=
    { toFun := fun k => ⟨g * k * g⁻¹, (mem_normalizer_iff.mp hg k).mp k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have h1 : g * kprod hK b v * g⁻¹ = (f (vprod b v) : G) := rfl
  rw [h1, map_vprod f, vprod_mulVec hb' M (fun j => Subtype.ext (hM j))]
  rfl

end KProd

end CFSG.EvenSmallLie.UnitarySix.YamadaD
