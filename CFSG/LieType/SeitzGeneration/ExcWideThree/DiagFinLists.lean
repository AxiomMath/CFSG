module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagFinCheck
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

private theorem rfDotL_cons_cons (a b : ℤ) (as bs : List ℤ) :
    rfDotL (a :: as) (b :: bs) = a * b + rfDotL as bs := rfl

private theorem rfDotN_cons_cons (a b : ℕ) (as bs : List ℕ) :
    rfDotN (a :: as) (b :: bs) = a * b + rfDotN as bs := rfl

private theorem rfRes3_cast (y : ℤ) : ((rfRes3 y : ℕ) : ℤ) = y % 3 := by
  unfold rfRes3
  exact Int.toNat_of_nonneg (Int.emod_nonneg y (by norm_num))

theorem rfDotL_ofFn {n : ℕ} (a b : Fin n → ℤ) :
    rfDotL (List.ofFn a) (List.ofFn b) = ∑ i, a i * b i := by
  induction n with
  | zero => simp only [List.ofFn_zero, Fin.sum_univ_zero]; rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, Fin.sum_univ_succ, rfDotL_cons_cons, ih]

theorem rfDotN_comm (a b : List ℕ) : rfDotN a b = rfDotN b a := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x as ih =>
    cases b with
    | nil => rfl
    | cons y bs => rw [rfDotN_cons_cons, rfDotN_cons_cons, ih bs, mul_comm]

theorem rfDotN_res3 (c : List ℕ) (a : List ℤ) :
    ((rfDotN c (a.map rfRes3) : ℕ) : ℤ) % 3 = rfDotL (c.map (fun x : ℕ => (x : ℤ))) a % 3 := by
  induction c generalizing a with
  | nil => cases a <;> rfl
  | cons x c ih =>
    cases a with
    | nil => rfl
    | cons y as =>
      have key : ((x * rfRes3 y + rfDotN c (as.map rfRes3) : ℕ) : ℤ) ≡
          (x : ℤ) * y + rfDotL (c.map fun k : ℕ => (k : ℤ)) as [ZMOD 3] := by
        rw [Nat.cast_add, Nat.cast_mul, rfRes3_cast]
        exact Int.ModEq.add (Int.ModEq.mul_left _ (Int.mod_modEq y 3)) (ih as)
      exact key

theorem rfModEq3_iff (u v : List ℕ) (h : u.length = v.length) :
    rfModEq3 u v = true ↔ ∀ i, u.getD i 0 % 3 = v.getD i 0 % 3 := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => simp [rfModEq3]
    | cons y v => simp at h
  | cons x u ih =>
    cases v with
    | nil => simp at h
    | cons y v =>
      have hl : u.length = v.length := by simpa using h
      have e : rfModEq3 (x :: u) (y :: v) = true ↔ x % 3 = y % 3 ∧ rfModEq3 u v = true := by
        simp [rfModEq3]
      rw [e, ih v hl]
      constructor
      · rintro ⟨h0, hr⟩ i
        cases i with
        | zero => simpa using h0
        | succ i => simpa using hr i
      · intro hall
        exact ⟨by simpa using hall 0, fun i => by simpa using hall (i + 1)⟩

theorem rfCartanL_eq : rfCartanL =
    List.ofFn (fun i : Fin Tag.E6.rank =>
      List.ofFn (fun j : Fin Tag.E6.rank => Tag.E6.cartan i j)) := by
  decide +kernel

theorem rfCartanMod3_eq : rfCartanMod3 = rfCartanL.map (·.map rfRes3) := by
  decide +kernel

theorem rfIform_ofFn (x y : Fin Tag.E6.rank → ℤ) :
    rfIform (List.ofFn x) (List.ofFn y) = iform (τ := Tag.E6) x y := by
  have hB : ∀ i j : Fin Tag.E6.rank, Tag.E6.symmetrizedCartan i j = Tag.E6.cartan i j := by
    intro i j
    simp [Tag.symmetrizedCartan, Tag.symmetrizer]
  simp only [iform, hB, rfIform, rfCartanL_eq, List.map_ofFn, Function.comp_def, rfDotL_ofFn,
    Finset.mul_sum, mul_assoc]

end CFSG.LieType.SeitzGeneration.ExcWideThree
