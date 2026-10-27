module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Group
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LieType.D4Small

open Matrix
open scoped commutatorElement

@[expose] def IsD4Root (α : Fin 4 → ℤ) : Prop := α ⬝ᵥ α = 2

theorem IsD4Root.neg {α : Fin 4 → ℤ} (h : IsD4Root α) : IsD4Root (-α) := by
  rwa [IsD4Root, neg_dotProduct, dotProduct_neg, neg_neg]

theorem IsD4Root.add {α β : Fin 4 → ℤ} (hα : IsD4Root α) (hβ : IsD4Root β)
    (h : α ⬝ᵥ β = -1) : IsD4Root (α + β) := by
  have h' : β ⬝ᵥ α = -1 := by rw [dotProduct_comm]; exact h
  unfold IsD4Root at *
  rw [add_dotProduct, dotProduct_add, dotProduct_add, hα, hβ, h, h']
  norm_num

theorem isD4Root_single_add_single {i j : Fin 4} (hij : i ≠ j) {s t : ℤ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) : IsD4Root (Pi.single i s + Pi.single j t) := by
  rw [IsD4Root]
  simp only [add_dotProduct, single_dotProduct, Pi.add_apply, Pi.single_apply, if_pos rfl,
    if_neg hij, if_neg hij.symm]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num

theorem isD4Root_iff {α : Fin 4 → ℤ} :
    IsD4Root α ↔ ∃ i j : Fin 4, i ≠ j ∧ (α i = 1 ∨ α i = -1) ∧ (α j = 1 ∨ α j = -1) ∧
      α = Pi.single i (α i) + Pi.single j (α j) := by
  constructor
  · intro h
    have hle : ∀ k, α k * α k ≤ 2 := fun k => by
      rw [← h]
      exact Finset.single_le_sum (f := fun k => α k * α k) (fun k _ => mul_self_nonneg (α k))
        (Finset.mem_univ k)
    have h1 : ∀ k, α k = -1 ∨ α k = 0 ∨ α k = 1 := fun k => by
      have := hle k
      have : -1 ≤ α k ∧ α k ≤ 1 := by constructor <;> nlinarith
      omega
    have hcard : (Finset.univ.filter fun k => α k ≠ 0).card = 2 := by
      have hT : α ⬝ᵥ α = ((Finset.univ.filter fun k => α k ≠ 0).card : ℤ) := by
        rw [dotProduct, Finset.card_filter]
        push_cast
        refine Finset.sum_congr rfl fun k _ => ?_
        rcases h1 k with hk | hk | hk <;> simp [hk]
      rw [show α ⬝ᵥ α = 2 from h] at hT
      exact_mod_cast hT.symm
    obtain ⟨i, j, hij, hTij⟩ := Finset.card_eq_two.mp hcard
    have hunit : ∀ k, α k ≠ 0 → α k = 1 ∨ α k = -1 := fun k hk => by
      rcases h1 k with h' | h' | h'
      · exact Or.inr h'
      · exact absurd h' hk
      · exact Or.inl h'
    have hmem : ∀ k, α k ≠ 0 ↔ k = i ∨ k = j := fun k => by
      have := congrArg (k ∈ ·) hTij
      simpa using this
    refine ⟨i, j, hij, hunit i ((hmem i).2 (Or.inl rfl)), hunit j ((hmem j).2 (Or.inr rfl)), ?_⟩
    funext k
    simp only [Pi.add_apply, Pi.single_apply]
    by_cases hki : k = i
    · subst hki
      simp [hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [hki]
      · have hk0 : α k = 0 := by
          by_contra hk
          rcases (hmem k).1 hk with h' | h'
          · exact hki h'
          · exact hkj h'
        simp [hki, hkj, hk0]
  · rintro ⟨i, j, hij, hi, hj, hα⟩
    rw [hα]
    exact isD4Root_single_add_single hij hi hj

variable {M : Type*} [CommGroup M]

@[expose] def torusChar (α : Fin 4 → ℤ) : (Fin 4 → M) →* M where
  toFun t := ∏ k, t k ^ α k
  map_one' := by simp
  map_mul' s t := by simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem torusChar_apply (α : Fin 4 → ℤ) (t : Fin 4 → M) : torusChar α t = ∏ k, t k ^ α k :=
  rfl

@[expose] def reflTorus (β : Fin 4 → ℤ) (t : Fin 4 → M) : Fin 4 → M :=
  fun k => t k * torusChar β t ^ (-β k)

@[expose] def castW (N : ℕ) (α : Fin 4 → ℤ) : Fin 4 → ZMod N := fun k => (α k : ZMod N)

@[expose] def reflW {N : ℕ} (β : Fin 4 → ℤ) (a : Fin 4 → ZMod N) : Fin 4 → ZMod N :=
  a - (a ⬝ᵥ castW N β) • castW N β

structure D4Datum (G : Type*) [Group G] (K : Type*) [Field K] where
  x : (Fin 4 → ℤ) → K → G
  h : (Fin 4 → Kˣ) →* G
  x_add : ∀ α, IsD4Root α → ∀ c d : K, x α (c + d) = x α c * x α d
  h_conj : ∀ α, IsD4Root α → ∀ (t : Fin 4 → Kˣ) (c : K),
    h t * x α c * (h t)⁻¹ = x α (((torusChar α t : Kˣ) : K) * c)
  weyl_conj : ∀ β, IsD4Root β → ∀ t : Fin 4 → Kˣ,
    x β 1 * x (-β) 1 * x β 1 * h t * (x β 1 * x (-β) 1 * x β 1)⁻¹ = h (reflTorus β t)
  comm_eq : ∀ α β, IsD4Root α → IsD4Root β → α ⬝ᵥ β = -1 → ∀ c d : K,
    ⁅x α c, x β d⁆ = x (α + β) (c * d)
  commute : ∀ α β, IsD4Root α → IsD4Root β → 0 ≤ α ⬝ᵥ β → ∀ c d : K,
    Commute (x α c) (x β d)
  closure_eq : Subgroup.closure {g | ∃ α, IsD4Root α ∧ ∃ c, x α c = g} = ⊤

namespace D4Datum

variable {K : Type*} [Field K] {G : Type*} [Group G] (D : D4Datum G K)

@[expose] def n (β : Fin 4 → ℤ) : G := D.x β 1 * D.x (-β) 1 * D.x β 1

theorem n_conj {β : Fin 4 → ℤ} (hβ : IsD4Root β) (t : Fin 4 → Kˣ) :
    D.n β * D.h t * (D.n β)⁻¹ = D.h (reflTorus β t) :=
  D.weyl_conj β hβ t

theorem x_zero {α : Fin 4 → ℤ} (hα : IsD4Root α) : D.x α 0 = 1 := by
  have h := D.x_add α hα 0 0
  rw [add_zero] at h
  calc D.x α 0 = (D.x α 0)⁻¹ * (D.x α 0 * D.x α 0) := by group
    _ = 1 := by rw [← h, inv_mul_cancel]

theorem x_neg {α : Fin 4 → ℤ} (hα : IsD4Root α) (c : K) : D.x α (-c) = (D.x α c)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← D.x_add α hα, add_neg_cancel, D.x_zero hα])

end D4Datum

end CFSG.LieType.D4Small
