module

public import CFSG.LieType.Universal.Spin.Structure.Entries
public import CFSG.LieType.Universal.Spin.Chevalley.Plus

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.LieType.Universal.Spin

@[expose] def kap {n : ℕ} (m : Fin n) : Bool → Fin n ⊕ Fin n
  | true => .inl m
  | false => .inr m

theorem isCoord_plusFrame' {n : ℕ} {F : Type} [Field F] (hn : 3 ≤ n) :
    (plusFrame n F hn).IsCoord (kap (n := n)) where
  idx_inj {m r m' r'} h := by
    cases r <;> cases r' <;> simp_all [kap]
  vec_eq m r := by cases r <;> rfl
  polar_vec v m r := by
    cases r
    · exact polar_quadPlus_single_inr n F v m
    · exact polar_quadPlus_single_inl n F v m

theorem kap_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) (s t : Bool) : kap i s ≠ kap j t := by
  intro h
  cases s <;> cases t <;> simp_all [kap]

theorem kap_not_ne_self {n : ℕ} (i : Fin n) (s : Bool) : kap i s ≠ kap i (!s) := by
  cases s <;> simp [kap]

theorem kap_inj {n : ℕ} {i j : Fin n} {s t : Bool} (h : kap i s = kap j t) : i = j ∧ s = t := by
  cases s <;> cases t <;> simp_all [kap]

theorem comm_entries {n : ℕ} {F : Type} [Field F] (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b)
    (s t : Bool) (k : spinGroup (quadPlus n F))
    (hk : k * (plusFrame n F hn).longRoot hab s t (Multiplicative.ofAdd 1) =
      (plusFrame n F hn).longRoot hab s t (Multiplicative.ofAdd 1) * k)
    (x y : Fin n ⊕ Fin n) :
    spinMat (quadPlus n F) k x (kap a s) * (if y = kap b (!t) then 1 else 0) -
        spinMat (quadPlus n F) k x (kap b t) * (if y = kap a (!s) then 1 else 0) =
      (if x = kap a s then 1 else 0) * spinMat (quadPlus n F) k (kap b (!t)) y -
        (if x = kap b t then 1 else 0) * spinMat (quadPlus n F) k (kap a (!s)) y := by
  have h := congrArg (fun g => spinMat (quadPlus n F) g x y) hk
  simp only [map_mul, Matrix.mul_apply,
    (isCoord_plusFrame' (F := F) hn).spinMat_longRoot hab s t 1] at h
  simp only [mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Matrix.one_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  by_cases hxp : x = kap a s <;> by_cases hxr : x = kap b t <;>
    by_cases hyr : y = kap b (!t) <;> by_cases hyp : y = kap a (!s) <;>
    simp [hxp, hxr, hyr, hyp] at h ⊢ <;> first | done | linear_combination h

theorem spinMat_eq_coe {n : ℕ} {F : Type} [Field F] (x : spinGroup (quadPlus n F)) :
    spinMat (quadPlus n F) x = (spinMatrix (quadPlus n F) x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  ext a b
  rw [spinMat_apply, coe_spinMatrix, LinearMap.toMatrix'_apply]
  rfl

end CFSG.HardMathSupport.Cooperstein.StructureLie
