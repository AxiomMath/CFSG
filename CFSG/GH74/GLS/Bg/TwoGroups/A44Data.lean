module

public import CFSG.GH74.GLS.Bg.TwoGroups.A44Facts

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace A44

open M4

@[expose] def ord3list : List M4 :=
  [⟨0, 1, 3, 3⟩,
    ⟨0, 3, 1, 3⟩,
    ⟨1, 1, 1, 2⟩,
    ⟨1, 3, 3, 2⟩,
    ⟨2, 1, 1, 1⟩,
    ⟨2, 3, 3, 1⟩,
    ⟨3, 1, 3, 0⟩,
    ⟨3, 3, 1, 0⟩]

@[expose] def K0list : List M4 :=
  [⟨0, 1, 3, 3⟩,
    ⟨0, 3, 1, 3⟩,
    ⟨1, 0, 0, 1⟩,
    ⟨1, 1, 1, 2⟩,
    ⟨1, 2, 2, 1⟩,
    ⟨1, 3, 3, 2⟩,
    ⟨2, 1, 1, 1⟩,
    ⟨2, 3, 3, 1⟩,
    ⟨3, 0, 2, 3⟩,
    ⟨3, 1, 3, 0⟩,
    ⟨3, 2, 0, 3⟩,
    ⟨3, 3, 1, 0⟩]

@[expose] def S4list1 : List M4 :=
  [⟨0, 1, 1, 0⟩,
    ⟨0, 1, 3, 3⟩,
    ⟨0, 3, 1, 3⟩,
    ⟨0, 3, 3, 2⟩,
    ⟨1, 0, 0, 1⟩,
    ⟨1, 0, 3, 3⟩,
    ⟨1, 1, 1, 2⟩,
    ⟨1, 1, 2, 1⟩,
    ⟨1, 2, 1, 1⟩,
    ⟨1, 2, 2, 1⟩,
    ⟨1, 3, 0, 3⟩,
    ⟨1, 3, 3, 2⟩,
    ⟨2, 1, 1, 1⟩,
    ⟨2, 1, 1, 2⟩,
    ⟨2, 3, 3, 0⟩,
    ⟨2, 3, 3, 1⟩,
    ⟨3, 0, 2, 3⟩,
    ⟨3, 0, 3, 1⟩,
    ⟨3, 1, 2, 3⟩,
    ⟨3, 1, 3, 0⟩,
    ⟨3, 2, 0, 3⟩,
    ⟨3, 2, 1, 3⟩,
    ⟨3, 3, 0, 1⟩,
    ⟨3, 3, 1, 0⟩]

@[expose] def S4list2 : List M4 :=
  [⟨0, 1, 1, 2⟩,
    ⟨0, 1, 3, 3⟩,
    ⟨0, 3, 1, 3⟩,
    ⟨0, 3, 3, 0⟩,
    ⟨1, 0, 0, 1⟩,
    ⟨1, 0, 1, 3⟩,
    ⟨1, 1, 0, 3⟩,
    ⟨1, 1, 1, 2⟩,
    ⟨1, 2, 2, 1⟩,
    ⟨1, 2, 3, 1⟩,
    ⟨1, 3, 2, 1⟩,
    ⟨1, 3, 3, 2⟩,
    ⟨2, 1, 1, 0⟩,
    ⟨2, 1, 1, 1⟩,
    ⟨2, 3, 3, 1⟩,
    ⟨2, 3, 3, 2⟩,
    ⟨3, 0, 1, 1⟩,
    ⟨3, 0, 2, 3⟩,
    ⟨3, 1, 0, 1⟩,
    ⟨3, 1, 3, 0⟩,
    ⟨3, 2, 0, 3⟩,
    ⟨3, 2, 3, 3⟩,
    ⟨3, 3, 1, 0⟩,
    ⟨3, 3, 2, 3⟩]

@[expose] def iota : M4 := ⟨3, 0, 0, 3⟩

@[expose] def dd : M4 := ⟨1, 2, 2, 3⟩

@[expose] def C4list : List M4 := [one, iota, dd, mul iota dd]

@[expose] def V4list : List M4 := [⟨1, 0, 0, 1⟩, ⟨1, 2, 2, 1⟩, ⟨3, 0, 2, 3⟩, ⟨3, 2, 0, 3⟩]

@[expose] def ClosedList (l : List M4) : Prop :=
  (∀ x ∈ l, x.IsInv) ∧ one ∈ l ∧ (∀ x ∈ l, ∀ y ∈ l, mul x y ∈ l) ∧ (∀ x ∈ l, x.inv ∈ l)

instance (l : List M4) : Decidable (ClosedList l) := by unfold ClosedList; infer_instance

theorem ord3_iff : ∀ x : M4, x.IsInv → ((mul (mul x x) x = one ∧ x ≠ one) ↔ x ∈ ord3list) := by
  decide +kernel

theorem K0_closed : ClosedList K0list := by decide +kernel
theorem S4_1_closed : ClosedList S4list1 := by decide +kernel
theorem S4_2_closed : ClosedList S4list2 := by decide +kernel

@[expose] def subOfList (l : List M4) (h : ClosedList l) : Subgroup G96 where
  carrier := {x | x.1 ∈ l}
  mul_mem' := fun {x y} hx hy => h.2.2.1 x.1 hx y.1 hy
  one_mem' := h.2.1
  inv_mem' := fun {x} hx => h.2.2.2 x.1 hx

theorem mem_subOfList {l : List M4} (h : ClosedList l) (x : G96) : x ∈ subOfList l h ↔ x.1 ∈ l :=
  Iff.rfl

@[expose] def Pgen (j : Fin 4) : M4 :=
  [(⟨0, 1, 3, 3⟩ : M4), ⟨1, 1, 1, 2⟩, ⟨2, 1, 1, 1⟩, ⟨3, 1, 3, 0⟩].getD j.val one

@[expose] def idx4 (y : M4) : Fin 4 :=
  if y = Pgen 0 ∨ y = (Pgen 0).inv then 0
  else if y = Pgen 1 ∨ y = (Pgen 1).inv then 1
  else if y = Pgen 2 ∨ y = (Pgen 2).inv then 2 else 3

@[expose] def act4 (x : M4) (j : Fin 4) : Fin 4 := idx4 (M4.conj x (Pgen j))

theorem Pgen_mem : ∀ j : Fin 4, Pgen j ∈ ord3list := by decide +kernel

theorem idx4_spec : ∀ w ∈ ord3list, Pgen (idx4 w) = w ∨ Pgen (idx4 w) = w.inv := by
  decide +kernel

theorem idx4_inv : ∀ v : M4, v.IsInv → idx4 v.inv = idx4 v := by decide +kernel

theorem conj_ord3 : ∀ x : M4, x.IsInv → ∀ w ∈ ord3list, M4.conj x w ∈ ord3list := by
  decide +kernel

theorem Pgen_isInv (j : Fin 4) : (Pgen j).IsInv := by
  have := Pgen_mem j
  revert this
  revert j
  decide +kernel

theorem conj_eq (g w : G96) : M4.conj g.1 w.1 = (g * w * g⁻¹).1 := rfl

theorem act4_mul : ∀ x y : G96, ∀ j : Fin 4, act4 (x * y).1 j = act4 x.1 (act4 y.1 j) := by
  intro x y j
  let p : G96 := ⟨Pgen j, Pgen_isInv j⟩
  let w : G96 := y * p * y⁻¹
  have hw : w.1 ∈ ord3list := conj_ord3 y.1 y.2 _ (Pgen_mem j)
  have e1 : M4.conj (x * y).1 p.1 = (x * w * x⁻¹).1 := by
    rw [conj_eq]
    congr 1
    show x * y * p * (x * y)⁻¹ = x * (y * p * y⁻¹) * x⁻¹
    group
  show idx4 (M4.conj (x * y).1 p.1) = idx4 (M4.conj x.1 (Pgen (idx4 w.1)))
  rcases idx4_spec _ hw with h | h
  · rw [h, e1, conj_eq]
  · rw [h]
    have e2 : M4.conj x.1 w.1.inv = ((x * w * x⁻¹).1).inv := by
      have h2 := conj_eq x w⁻¹
      rw [show (w⁻¹).1 = w.1.inv from rfl] at h2
      rw [h2, show x * w⁻¹ * x⁻¹ = (x * w * x⁻¹)⁻¹ by group]
      rfl
    rw [e2, e1, idx4_inv _ (x * w * x⁻¹).2]

theorem act4_one : ∀ j : Fin 4, act4 one j = j := by decide +kernel

instance : MulAction G96 (Fin 4) where
  smul x j := act4 x.1 j
  one_smul j := act4_one j
  mul_smul x y j := act4_mul x y j

@[expose] def vec3 (i : Fin 3) : ZMod 4 × ZMod 4 :=
  if i = 0 then (1, 0) else if i = 1 then (0, 1) else (1, 1)

@[expose] def idx3 (v : ZMod 4 × ZMod 4) : Fin 3 :=
  if v.1.val % 2 = 1 ∧ v.2.val % 2 = 0 then 0
  else if v.1.val % 2 = 0 ∧ v.2.val % 2 = 1 then 1 else 2

@[expose] def act3 (x : M4) (i : Fin 3) : Fin 3 := idx3 (x.act (vec3 i))

@[expose] def par (v : ZMod 4 × ZMod 4) : ℕ × ℕ := (v.1.val % 2, v.2.val % 2)

theorem idx3_congr : ∀ v w : ZMod 4 × ZMod 4, par v = par w → idx3 v = idx3 w := by
  decide +kernel

theorem par_act : ∀ x : M4, ∀ v w : ZMod 4 × ZMod 4, par v = par w →
    par (x.act v) = par (x.act w) := by decide +kernel

theorem par_vec3_idx3 : ∀ u : ZMod 4 × ZMod 4, par u ≠ (0, 0) → par (vec3 (idx3 u)) = par u := by
  decide +kernel

theorem par_act_ne : ∀ y : M4, y.IsInv → ∀ i : Fin 3, par (y.act (vec3 i)) ≠ (0, 0) := by
  decide +kernel

theorem act3_mul : ∀ x y : G96, ∀ i : Fin 3, act3 (x * y).1 i = act3 x.1 (act3 y.1 i) := by
  intro x y i
  show idx3 ((M4.mul x.1 y.1).act (vec3 i)) = idx3 (x.1.act (vec3 (idx3 (y.1.act (vec3 i)))))
  rw [M4.act_mul]
  apply (idx3_congr _ _ _).symm
  exact (par_act x.1 _ _ (par_vec3_idx3 _ (par_act_ne y.1 y.2 i)))

theorem act3_one : ∀ i : Fin 3, act3 one i = i := by decide +kernel

instance : MulAction G96 (Fin 3) where
  smul x i := act3 x.1 i
  one_smul i := act3_one i
  mul_smul x y i := act3_mul x y i

theorem act3_ker : ∀ x : M4, x.IsInv → ((∀ i : Fin 3, act3 x i = i) ↔ x.IsA0) := by
  decide +kernel

theorem act3_surj : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
    ∃ x : G96, act3 x.1 0 = a ∧ act3 x.1 1 = b ∧ act3 x.1 2 = c := by
  decide +kernel

theorem card_K0 : Fintype.card {x : G96 // x.1 ∈ K0list} = 12 := by decide +kernel

theorem K0_conj : ∀ g : M4, g.IsInv → ∀ x ∈ K0list, conj g x ∈ K0list := by decide +kernel

theorem K0_two : ∀ x ∈ K0list, pow32 x = one → x ∈ V4list := by decide +kernel

theorem ord3_sub_K0 : ∀ x ∈ ord3list, x ∈ K0list := by decide +kernel

end A44

end CFSG.GH74.GLS.Bg.TwoGroups
