module

public import CFSG.LieType.Universal.Spin.Chevalley.Plus

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ}

namespace HypFrame

variable (F : HypFrame Q n)

@[expose] noncomputable def planeMap (idx : Fin 3 → Fin n) : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] V :=
  ∑ a : Fin 3, ((LinearMap.proj (Sum.inl a)).smulRight (F.vec (idx a) true) +
    (LinearMap.proj (Sum.inr a)).smulRight (F.vec (idx a) false))

theorem planeMap_apply (idx : Fin 3 → Fin n) (x : Fin 3 ⊕ Fin 3 → K) :
    F.planeMap idx x =
      ∑ a : Fin 3, (x (Sum.inl a) • F.vec (idx a) true + x (Sum.inr a) • F.vec (idx a) false) := by
  simp [planeMap, LinearMap.sum_apply]

theorem planeMap_plusVec (idx : Fin 3 → Fin n) (a : Fin 3) (r : Bool) :
    F.planeMap idx (plusVec 3 K a r) = F.vec (idx a) r := by
  rw [planeMap_apply]
  cases r
  · simp only [plusVec_false]
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ a) h)]
    simp
  · simp only [plusVec_true]
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ a) h)]
    simp

theorem map_smul_vec_add_smul_vec (m : Fin n) (c d : K) :
    Q (c • F.vec m true + d • F.vec m false) = c * d := by
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, F.map_vec, F.map_vec,
    polar_smul_left, polar_smul_right]
  have h := F.polar_vec_not m true
  simp only [Bool.not_true] at h
  rw [h]
  simp

theorem polar_smul_vec_add_smul_vec {m m' : Fin n} (hm : m ≠ m') (c d c' d' : K) :
    polar Q (c • F.vec m true + d • F.vec m false) (c' • F.vec m' true + d' • F.vec m' false) = 0 := by
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
    F.polar_vec_of_ne hm, smul_zero, add_zero]

omit F in
theorem map_add_add_of_polar (a b c : V) (hab : polar Q a b = 0) (hac : polar Q a c = 0)
    (hbc : polar Q b c = 0) : Q (a + b + c) = Q a + Q b + Q c := by
  rw [QuadraticMap.map_add Q (a + b) c, QuadraticMap.map_add Q a b, polar_add_left, hab, hac, hbc]
  ring

@[expose] noncomputable def planeIsometry (idx : Fin 3 → Fin n) (hidx : Function.Injective idx) :
    (quadPlus 3 K).Isometry Q where
  toLinearMap := F.planeMap idx
  map_app' x := by
    change Q (F.planeMap idx x) = quadPlus 3 K x
    have h01 : idx 0 ≠ idx 1 := hidx.ne (by decide)
    have h02 : idx 0 ≠ idx 2 := hidx.ne (by decide)
    have h12 : idx 1 ≠ idx 2 := hidx.ne (by decide)
    rw [planeMap_apply, quadPlus_apply, Fin.sum_univ_three, Fin.sum_univ_three,
      map_add_add_of_polar _ _ _ (F.polar_smul_vec_add_smul_vec h01 _ _ _ _)
        (F.polar_smul_vec_add_smul_vec h02 _ _ _ _) (F.polar_smul_vec_add_smul_vec h12 _ _ _ _),
      F.map_smul_vec_add_smul_vec, F.map_smul_vec_add_smul_vec, F.map_smul_vec_add_smul_vec]

theorem planeIsometry_plusVec (idx : Fin 3 → Fin n) (hidx : Function.Injective idx) (a : Fin 3)
    (r : Bool) : F.planeIsometry idx hidx (plusVec 3 K a r) = F.vec (idx a) r :=
  F.planeMap_plusVec idx a r

theorem map_coe_longWeyl (idx : Fin 3 → Fin n) (hidx : Function.Injective idx) {a b : Fin 3}
    (hab : a ≠ b) (s t : Bool) :
    CliffordAlgebra.map (F.planeIsometry idx hidx)
        ((plusFrame 3 K le_rfl).longWeyl hab s t : CliffordAlgebra (quadPlus 3 K)) =
      (F.longWeyl (hidx.ne hab) s t : CliffordAlgebra Q) := by
  rw [longWeyl, longWeyl, coe_longSL2, coe_longSL2]
  refine SL2Pair.map_toFun _ _ _ ?_ ?_ _
  · simp only [longPair, map_mul, map_apply_ι, plusFrame_vec, planeIsometry_plusVec]
  · simp only [longPair, map_mul, map_apply_ι, plusFrame_vec, planeIsometry_plusVec]

theorem longWeyl_braid' {i j l : Fin n} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (s t u : Bool) :
    F.longWeyl hij s t * F.longWeyl hjl (!t) u * F.longWeyl hij s t =
      F.longWeyl hjl (!t) u * F.longWeyl hij s t * F.longWeyl hjl (!t) u := by
  set idx : Fin 3 → Fin n := ![i, j, l]
  have hidx : Function.Injective idx := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [idx, Ne.symm hij, Ne.symm hjl, Ne.symm hil]
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h3 := (plusFrame 3 K le_rfl).longWeyl_braid h01 h12 h02 s t u
    (eq_one_or_eq_neg_one_of_spinAction_eq_one 3 K)
  have h := congrArg (fun g : spinGroup (quadPlus 3 K) =>
    CliffordAlgebra.map (F.planeIsometry idx hidx) (g : CliffordAlgebra (quadPlus 3 K))) h3
  simp only [Submonoid.coe_mul, map_mul, F.map_coe_longWeyl idx hidx] at h
  apply Subtype.ext
  simp only [Submonoid.coe_mul]
  exact h

end HypFrame

end CFSG.LieType.Universal.Spin
