module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Combinatorics.AperiodicSixteenGraph

@[expose] def form (v w : Fin 3 → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, if j < i then v i * w j else 0

theorem form_eq (v w : Fin 3 → ZMod 2) : form v w = v 1 * w 0 + v 2 * w 0 + v 2 * w 1 := by
  simp [form, Fin.sum_univ_three, add_assoc]

@[ext] structure K where
  vec : Fin 3 → ZMod 2
  cen : ZMod 2

namespace K

instance : DecidableEq K := fun g h =>
  decidable_of_iff (g.vec = h.vec ∧ g.cen = h.cen) K.ext_iff.symm

@[expose] def equivCoords : K ≃ ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 where
  toFun g := (g.vec 0, g.vec 1, g.vec 2, g.cen)
  invFun p := ⟨![p.1, p.2.1, p.2.2.1], p.2.2.2⟩
  left_inv g := by
    ext i
    · fin_cases i <;> rfl
    · rfl
  right_inv _ := rfl

instance : Fintype K :=
  Fintype.ofEquiv _ equivCoords.symm

instance : Group K where
  mul g h := ⟨g.vec + h.vec, g.cen + h.cen + form g.vec h.vec⟩
  one := ⟨0, 0⟩
  inv g := ⟨g.vec, g.cen + form g.vec g.vec⟩
  mul_assoc g h k := K.ext (add_assoc _ _ _) (show g.cen + h.cen + form g.vec h.vec + k.cen +
      form (g.vec + h.vec) k.vec = g.cen + (h.cen + k.cen + form h.vec k.vec) +
        form g.vec (h.vec + k.vec) by
    simp only [form_eq, Pi.add_apply]
    ring)
  one_mul g := K.ext (zero_add _) (show 0 + g.cen + form 0 g.vec = g.cen by simp [form_eq])
  mul_one g := K.ext (add_zero _) (show g.cen + 0 + form g.vec 0 = g.cen by simp [form_eq])
  inv_mul_cancel g := K.ext (funext fun i => (by decide : ∀ x : ZMod 2, x + x = 0) (g.vec i))
    ((by decide : ∀ x y : ZMod 2, x + y + x + y = 0) _ _)

@[simp] theorem mul_vec (g h : K) : (g * h).vec = g.vec + h.vec := rfl

@[simp] theorem mul_cen (g h : K) : (g * h).cen = g.cen + h.cen + form g.vec h.vec := rfl

@[simp] theorem one_vec : (1 : K).vec = 0 := rfl

@[simp] theorem one_cen : (1 : K).cen = 0 := rfl

theorem card : Fintype.card K = 16 := by
  rw [Fintype.card_congr equivCoords]
  rfl

end K

@[expose] def s (i : Fin 3) : K :=
  ⟨Pi.single i 1, 0⟩

@[expose] def z : K :=
  ⟨0, 1⟩

@[expose] def o : K :=
  1

@[expose] def τ (g : K) : K :=
  g * z

theorem s_mul_self (i : Fin 3) : s i * s i = 1 := by
  revert i
  decide

theorem s_ne_one (i : Fin 3) : s i ≠ 1 := by
  revert i
  decide

theorem s_injective : Function.Injective s := by
  intro i j
  revert i j
  decide

theorem z_mul (g : K) : z * g = g * z := by
  revert g
  decide

theorem z_mul_self : z * z = 1 := by
  decide

theorem z_ne_one : z ≠ 1 := by
  decide

theorem s_mul_s {i j : Fin 3} (hij : i ≠ j) : s i * s j = z * (s j * s i) := by
  revert i j
  decide

@[expose] def T : SimpleGraph K where
  Adj g h := ∃ i, h = g * s i
  symm := ⟨by
    rintro g h ⟨i, rfl⟩
    exact ⟨i, by rw [mul_assoc, s_mul_self, mul_one]⟩⟩
  loopless := ⟨by
    rintro g ⟨i, h⟩
    exact s_ne_one i (mul_eq_left.mp h.symm)⟩

instance : DecidableRel T.Adj := fun g h =>
  inferInstanceAs (Decidable (∃ i, h = g * s i))

theorem adj_iff {g h : K} : T.Adj g h ↔ ∃ i, h = g * s i :=
  Iff.rfl

theorem adj_mul_s (g : K) (i : Fin 3) : T.Adj g (g * s i) :=
  ⟨i, rfl⟩

theorem neighborFinset_eq (g : K) :
    T.neighborFinset g = Finset.univ.image fun i => g * s i := by
  ext h
  simp only [SimpleGraph.mem_neighborFinset, adj_iff, Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_congr fun i => eq_comm

theorem degree_eq (g : K) : T.degree g = 3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_eq,
    Finset.card_image_of_injective (f := fun i => g * s i) _
      fun i j h => s_injective (mul_left_cancel h)]
  rfl

end CFSG.Combinatorics.AperiodicSixteenGraph
