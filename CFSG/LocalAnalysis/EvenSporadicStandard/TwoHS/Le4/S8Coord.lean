module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Data
public import Mathlib.Tactic.Group
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

structure ECoord (G : Type*) [Group G] where
  E : Subgroup G
  φ : E ≃* Multiplicative V4

namespace ECoord

variable {G : Type*} [Group G] (C : ECoord G)

@[expose] def elt (v : V4) : G := (C.φ.symm (Multiplicative.ofAdd v) : G)

open Classical in
@[expose] noncomputable def vec (x : G) : V4 :=
  if h : x ∈ C.E then Multiplicative.toAdd (C.φ ⟨x, h⟩) else 0

theorem elt_mem (v : V4) : C.elt v ∈ C.E := (C.φ.symm (Multiplicative.ofAdd v)).2

theorem vec_elt (v : V4) : C.vec (C.elt v) = v := by
  have h := C.elt_mem v
  simp only [vec, h, ↓reduceDIte]
  have : (⟨C.elt v, h⟩ : C.E) = C.φ.symm (Multiplicative.ofAdd v) := rfl
  rw [this, MulEquiv.apply_symm_apply]
  rfl

theorem elt_vec {x : G} (hx : x ∈ C.E) : C.elt (C.vec x) = x := by
  simp only [vec, hx, ↓reduceDIte, elt]
  have : Multiplicative.ofAdd (Multiplicative.toAdd (C.φ ⟨x, hx⟩)) = C.φ ⟨x, hx⟩ := rfl
  rw [this, MulEquiv.symm_apply_apply]

theorem elt_add (v w : V4) : C.elt (v + w) = C.elt v * C.elt w := by
  have : Multiplicative.ofAdd (v + w) = Multiplicative.ofAdd v * Multiplicative.ofAdd w := rfl
  simp only [elt, this, map_mul, Subgroup.coe_mul]

theorem elt_zero : C.elt 0 = 1 := by
  have : Multiplicative.ofAdd (0 : V4) = 1 := rfl
  simp only [elt, this, map_one, Subgroup.coe_one]

theorem elt_neg (v : V4) : C.elt (-v) = (C.elt v)⁻¹ := by
  have : Multiplicative.ofAdd (-v) = (Multiplicative.ofAdd v)⁻¹ := rfl
  simp only [elt, this, map_inv, Subgroup.coe_inv]

theorem elt_sub (v w : V4) : C.elt (v - w) = C.elt v * (C.elt w)⁻¹ := by
  rw [sub_eq_add_neg, C.elt_add, C.elt_neg]

theorem elt_nsmul (k : ℕ) (v : V4) : C.elt (k • v) = C.elt v ^ k := by
  induction k with
  | zero => simp [C.elt_zero]
  | succ k ih => rw [succ_nsmul, C.elt_add, ih, pow_succ]

theorem elt_injective : Function.Injective C.elt := fun v w h => by
  have := congrArg C.vec h
  rwa [C.vec_elt, C.vec_elt] at this

theorem vec_mul {x y : G} (hx : x ∈ C.E) (hy : y ∈ C.E) : C.vec (x * y) = C.vec x + C.vec y := by
  apply C.elt_injective
  rw [C.elt_vec (C.E.mul_mem hx hy), C.elt_add, C.elt_vec hx, C.elt_vec hy]

theorem vec_one : C.vec 1 = 0 := by
  apply C.elt_injective
  rw [C.elt_vec C.E.one_mem, C.elt_zero]

theorem comm {x y : G} (hx : x ∈ C.E) (hy : y ∈ C.E) : x * y = y * x := by
  rw [← C.elt_vec hx, ← C.elt_vec hy, ← C.elt_add, ← C.elt_add, add_comm]

theorem pow_four {x : G} (hx : x ∈ C.E) : x ^ 4 = 1 := by
  rw [← C.elt_vec hx, ← C.elt_nsmul, ← C.elt_zero]
  congr 1
  funext i
  have : ∀ a : ZMod 4, 4 • a = 0 := by decide
  exact this _

@[expose] noncomputable def act (m : G) (v : V4) : V4 := C.vec (m * C.elt v * m⁻¹)

variable {C} {m : G}

theorem act_spec (hm : m ∈ normalizer (C.E : Set G)) (v : V4) :
    C.elt (C.act m v) = m * C.elt v * m⁻¹ := by
  have h := (mem_normalizer_iff.1 hm (C.elt v)).1 (C.elt_mem v)
  exact C.elt_vec h

theorem act_add (hm : m ∈ normalizer (C.E : Set G)) (v w : V4) :
    C.act m (v + w) = C.act m v + C.act m w := by
  apply C.elt_injective
  rw [C.elt_add, C.act_spec hm, C.act_spec hm, C.act_spec hm, C.elt_add]
  group

theorem act_zero (hm : m ∈ normalizer (C.E : Set G)) : C.act m 0 = 0 := by
  apply C.elt_injective
  rw [C.act_spec hm, C.elt_zero]
  group

theorem act_nsmul (hm : m ∈ normalizer (C.E : Set G)) (k : ℕ) (v : V4) :
    C.act m (k • v) = k • C.act m v := by
  induction k with
  | zero => simp [C.act_zero hm]
  | succ k ih => rw [succ_nsmul, C.act_add hm, ih, succ_nsmul]

@[expose] noncomputable def mat (m : G) : M4 := Matrix.of fun i j => C.act m (Pi.single j 1) i

theorem act_eq_mulVec (hm : m ∈ normalizer (C.E : Set G)) (v : V4) :
    C.act m v = C.mat m *ᵥ v := by
  let f : V4 →+ V4 :=
    { toFun := C.act m, map_zero' := C.act_zero hm, map_add' := C.act_add hm }
  have hv : v = ∑ j, Pi.single j (v j) := (Finset.univ_sum_single v).symm
  have hs : ∀ (j : Fin 4) (c : ZMod 4), Pi.single j c = c.val • (Pi.single j 1 : V4) := by
    intro j c
    funext i
    by_cases h : i = j
    · subst h
      simp [nsmul_eq_mul]
    · simp [h]
  funext i
  have e1 : C.act m v = ∑ j, C.act m (Pi.single j (v j)) := by
    show f v = ∑ j, f (Pi.single j (v j))
    rw [← map_sum, ← hv]
  rw [e1]
  simp only [Finset.sum_apply, mulVec, dotProduct, mat, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hs j (v j)]
  have h2 : C.act m ((v j).val • (Pi.single j 1 : V4)) =
      (v j).val • C.act m (Pi.single j 1) := C.act_nsmul hm _ _
  rw [h2]
  simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]
  exact mul_comm _ _

theorem act_mul (hm : m ∈ normalizer (C.E : Set G)) {m' : G}
    (hm' : m' ∈ normalizer (C.E : Set G)) (v : V4) : C.act (m * m') v = C.act m (C.act m' v) := by
  apply C.elt_injective
  rw [C.act_spec (mul_mem hm hm'), C.act_spec hm, C.act_spec hm']
  group

theorem mat_mul (hm : m ∈ normalizer (C.E : Set G)) {m' : G}
    (hm' : m' ∈ normalizer (C.E : Set G)) : C.mat (m * m') = C.mat m * C.mat m' := by
  ext i j
  have h1 := C.act_eq_mulVec (mul_mem hm hm') (Pi.single j 1)
  have h2 : C.act (m * m') (Pi.single j 1) = C.mat m *ᵥ (C.mat m' *ᵥ Pi.single j 1) := by
    rw [C.act_mul hm hm', C.act_eq_mulVec hm', C.act_eq_mulVec hm]
  have h3 := congrFun h2 i
  simp only [mat, Matrix.of_apply, mulVec_mulVec] at h3 ⊢
  rw [h3]
  simp

theorem mat_one : C.mat (1 : G) = 1 := by
  ext i j
  have : C.act (1 : G) (Pi.single j 1) = Pi.single j 1 := by
    apply C.elt_injective
    rw [C.act_spec (one_mem _)]
    group
  simp only [mat, Matrix.of_apply, this]
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem mat_eq_one_iff (hm : m ∈ normalizer (C.E : Set G)) :
    C.mat m = 1 ↔ ∀ e ∈ C.E, m * e = e * m := by
  constructor
  · intro h e he
    have h1 := C.act_eq_mulVec hm (C.vec e)
    rw [h, one_mulVec] at h1
    have h2 := C.act_spec hm (C.vec e)
    rw [h1, C.elt_vec he] at h2
    calc m * e = (m * e * m⁻¹) * m := by group
      _ = e * m := by rw [← h2]
  · intro h
    have key : ∀ v, C.mat m *ᵥ v = v := by
      intro v
      rw [← C.act_eq_mulVec hm]
      apply C.elt_injective
      rw [C.act_spec hm]
      have := h _ (C.elt_mem v)
      calc m * C.elt v * m⁻¹ = (C.elt v * m) * m⁻¹ := by rw [this]
        _ = C.elt v := by group
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    rw [mulVec_single_one] at this
    by_cases hij : i = j <;> simp_all [Matrix.one_apply]

theorem vec_conj (hm : m ∈ normalizer (C.E : Set G)) {x : G} (hx : x ∈ C.E) :
    C.vec (m * x * m⁻¹) = C.mat m *ᵥ C.vec x := by
  rw [← C.act_eq_mulVec hm, act, C.elt_vec hx]

theorem conj_elt (hm : m ∈ normalizer (C.E : Set G)) (v : V4) :
    m * C.elt v * m⁻¹ = C.elt (C.mat m *ᵥ v) := by
  rw [← C.act_eq_mulVec hm, C.act_spec hm]

end ECoord

end CFSG.EvenSporadicStandard.TwoHS
