module

public import CFSG.GH74.SectionalRank

public section

namespace CFSG.GH74.QTGen4.Leaves.SL5Rank

open CFSG.Open

def pos (x : Fin 2 × Fin 3) : Fin 5 × Fin 5 :=
  (⟨x.1.val, by have := x.1.isLt; omega⟩, ⟨x.2.val + 2, by have := x.2.isLt; omega⟩)

theorem pos_injective : Function.Injective pos := by
  intro x y h
  have h1 : x.1.val = y.1.val := congrArg (fun p : Fin 5 × Fin 5 => p.1.val) h
  have h2 : x.2.val = y.2.val := by
    have : x.2.val + 2 = y.2.val + 2 := congrArg (fun p : Fin 5 × Fin 5 => p.2.val) h
    omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

def U (v : Fin 2 × Fin 3 → ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun i j => ∑ x : Fin 2 × Fin 3, if pos x = (i, j) then v x else 0

theorem U_zero : U 0 = 0 := by
  ext i j
  simp [U]

theorem U_add (v w : Fin 2 × Fin 3 → ZMod 2) : U (v + w) = U v + U w := by
  ext i j
  simp only [U, Matrix.add_apply, Matrix.of_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem U_apply_pos (v : Fin 2 × Fin 3 → ZMod 2) (x : Fin 2 × Fin 3) :
    U v (pos x).1 (pos x).2 = v x := by
  simp [U, pos_injective.eq_iff]

theorem U_injective : Function.Injective U := by
  intro v w h
  funext x
  exact (U_apply_pos v x).symm.trans ((congrFun (congrFun h _) _).trans (U_apply_pos w x))

theorem U_row_ge (v : Fin 2 × Fin 3 → ZMod 2) (i : Fin 5) (hi : 2 ≤ i.val) (k : Fin 5) :
    U v i k = 0 := by
  unfold U
  simp only [Matrix.of_apply]
  apply Finset.sum_eq_zero
  intro x _
  have hne : pos x ≠ (i, k) := fun h => by
    have h1 : x.1.val = i.val := congrArg (fun p : Fin 5 × Fin 5 => p.1.val) h
    have := x.1.isLt
    omega
  simp [hne]

theorem U_col_lt (v : Fin 2 × Fin 3 → ZMod 2) (i : Fin 5) (k : Fin 5) (hk : k.val < 2) :
    U v i k = 0 := by
  unfold U
  simp only [Matrix.of_apply]
  apply Finset.sum_eq_zero
  intro x _
  have hne : pos x ≠ (i, k) := fun h => by
    have h1 : x.2.val + 2 = k.val := congrArg (fun p : Fin 5 × Fin 5 => p.2.val) h
    omega
  simp [hne]

theorem U_mul (v w : Fin 2 × Fin 3 → ZMod 2) : U v * U w = 0 := by
  ext i k
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j.val < 2
  · rw [U_col_lt v i j hj, zero_mul]
  · rw [U_row_ge w j (by omega) k, mul_zero]

theorem unip_mul (v w : Fin 2 × Fin 3 → ZMod 2) :
    (1 + U v) * (1 + U w) = 1 + U (v + w) := by
  simp only [add_mul, mul_add, one_mul, mul_one, U_mul, add_zero, U_add]
  abel

theorem add_self_fun (v : Fin 2 × Fin 3 → ZMod 2) : v + v = 0 :=
  funext fun x => (by decide : ∀ a : ZMod 2, a + a = 0) (v x)

theorem det_unip (v : Fin 2 × Fin 3 → ZMod 2) : (1 + U v).det = 1 := by
  have hsq : (1 + U v) * (1 + U v) = 1 := by
    rw [unip_mul, add_self_fun, U_zero, add_zero]
  have hdet : (1 + U v).det * (1 + U v).det = 1 := by
    rw [← Matrix.det_mul, hsq, Matrix.det_one]
  exact (by decide : ∀ a : ZMod 2, a * a = 1 → a = 1) _ hdet

def blkUnit (v : Fin 2 × Fin 3 → ZMod 2) : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨1 + U v, det_unip v⟩

def blkHom : Multiplicative (Fin 2 × Fin 3 → ZMod 2) →* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
    where
  toFun x := blkUnit x.toAdd
  map_one' := by
    apply Subtype.ext
    show 1 + U 0 = 1
    rw [U_zero, add_zero]
  map_mul' x y := by
    apply Subtype.ext
    show 1 + U (x.toAdd + y.toAdd) = (1 + U x.toAdd) * (1 + U y.toAdd)
    exact (unip_mul _ _).symm

theorem blkHom_injective : Function.Injective blkHom := by
  intro x y h
  have h1 : 1 + U x.toAdd = 1 + U y.toAdd := congrArg Subtype.val h
  exact Multiplicative.toAdd.injective (U_injective (add_left_cancel h1))

theorem mul_self_eq_one' (u : Multiplicative (Fin 2 × Fin 3 → ZMod 2)) : u * u = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_one, add_self_fun]

theorem map_top_elemAbelian {X : Type} [Group X]
    (f : Multiplicative (Fin 2 × Fin 3 → ZMod 2) →* X) :
    IsElemAbelian 2 ((⊤ : Subgroup (Multiplicative (Fin 2 × Fin 3 → ZMod 2))).map f) := by
  refine ⟨?_, ?_⟩
  · rw [isMulCommutative_iff]
    rintro ⟨_, ha⟩ ⟨_, hb⟩
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.mp hb
    apply Subtype.ext
    show f u * f w = f w * f u
    rw [← map_mul, ← map_mul]
    exact congrArg f (mul_comm u w)
  · intro x hx
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hx
    rw [pow_two, ← map_mul, mul_self_eq_one', map_one]

theorem card_map_top {X : Type} [Group X]
    (f : Multiplicative (Fin 2 × Fin 3 → ZMod 2) →* X) (hf : Function.Injective f) :
    Nat.card ((⊤ : Subgroup (Multiplicative (Fin 2 × Fin 3 → ZMod 2))).map f) = 2 ^ 6 := by
  rw [Subgroup.card_map_of_injective hf, Subgroup.card_top, Nat.card_eq_fintype_card]
  simp

theorem not_gen4_of_hom {X : Type} [Group X]
    (f : Multiplicative (Fin 2 × Fin 3 → ZMod 2) →* X) (hf : Function.Injective f) :
    ¬ CFSG.GH74.Gen4 X := by
  intro h
  have h' : CFSG.GH74.SectionalTwoRankLE X 4 := h
  have hle := CFSG.GH74.SectionalTwoRankLE.card_le_of_elementary h' _ (map_top_elemAbelian f)
  rw [card_map_top f hf] at hle
  norm_num at hle

theorem single_mul_U (v : Fin 2 × Fin 3 → ZMod 2) :
    Matrix.single (0 : Fin 5) (4 : Fin 5) (1 : ZMod 2) * U v = 0 := by
  ext i k
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j = 4
  · subst hj
    rw [U_row_ge v 4 (by decide) k, mul_zero]
  · simp [Ne.symm hj]

theorem U_mul_single (v : Fin 2 × Fin 3 → ZMod 2) :
    U v * Matrix.single (0 : Fin 5) (4 : Fin 5) (1 : ZMod 2) = 0 := by
  ext i k
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j = 0
  · subst hj
    rw [U_col_lt v i 0 (by decide), zero_mul]
  · simp [Ne.symm hj]

theorem commute_single (v : Fin 2 × Fin 3 → ZMod 2) :
    (1 + Matrix.single (0 : Fin 5) (4 : Fin 5) (1 : ZMod 2)) * (1 + U v) =
      (1 + U v) * (1 + Matrix.single (0 : Fin 5) (4 : Fin 5) (1 : ZMod 2)) := by
  simp only [add_mul, mul_add, one_mul, mul_one, single_mul_U, U_mul_single, add_zero]
  abel

abbrev tvec : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 5) ≠ 4 by decide) 1

theorem blkHom_mem_centralizer (x : Multiplicative (Fin 2 × Fin 3 → ZMod 2)) :
    blkHom x ∈ Subgroup.centralizer ({tvec} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  apply Subtype.ext
  show (1 + Matrix.single (0 : Fin 5) (4 : Fin 5) (1 : ZMod 2)) * (1 + U x.toAdd) =
    (1 + U x.toAdd) * (1 + Matrix.single (0 : Fin 5) (4 : Fin 5) (1 : ZMod 2))
  exact commute_single _

def blkCent : Multiplicative (Fin 2 × Fin 3 → ZMod 2) →*
    ↥(Subgroup.centralizer ({tvec} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))) where
  toFun x := ⟨blkHom x, blkHom_mem_centralizer x⟩
  map_one' := Subtype.ext (map_one blkHom)
  map_mul' x y := Subtype.ext (map_mul blkHom x y)

theorem blkCent_injective : Function.Injective blkCent :=
  fun _ _ h => blkHom_injective (congrArg Subtype.val h)

theorem not_gen4_of_centralizer_tvec {X : Type} [Group X]
    (f : ↥(Subgroup.centralizer ({tvec} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))) →*
      X) (hf : Function.Injective f) : ¬ CFSG.GH74.Gen4 X :=
  not_gen4_of_hom (f.comp blkCent) (hf.comp blkCent_injective)

end CFSG.GH74.QTGen4.Leaves.SL5Rank
