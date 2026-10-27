module

public import CFSG.LieType.Steinberg.Classical.SpinFrame.Basic

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinFrame

open CFSG.LieType.Universal.Spin CliffordAlgebra QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ} (F : HypFrame Q n)

theorem conj_rootElt_of_signedPerm (g : spinGroup Q) (π : Equiv.Perm (Fin n))
    (β : Fin n → Bool → Bool) (w : Fin n → Bool → ℤ) (hw : ∀ m r, w m r = 1 ∨ w m r = -1)
    (hg : ∀ m r, spinAction Q g (F.vec m r) = (w m r : K) • F.vec (π m) (β m r))
    {e : Fin n → ℤ} {k l : Fin n} (hkl : k ≠ l) {u v : Bool}
    (he : e = Pi.single k (boolSign u) + Pi.single l (boolSign v)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      g * rootElt F e c * g⁻¹ =
        rootElt F (Pi.single (π k) (boolSign (β k u)) + Pi.single (π l) (boolSign (β l v)))
          ((ε : K) * c) := by
  have hkl' : π k ≠ π l := π.injective.ne hkl
  refine ⟨repSign (π k) (π l) (β k u) (β l v) * w k u * w l v * repSign k l u v, ?_, fun c => ?_⟩
  · rcases repSign_eq_one_or_eq_neg_one (π k) (π l) (β k u) (β l v) with h1 | h1 <;>
      rcases hw k u with h2 | h2 <;> rcases hw l v with h3 | h3 <;>
      rcases repSign_eq_one_or_eq_neg_one k l u v with h4 | h4 <;>
      rw [h1, h2, h3, h4] <;> simp
  · rw [rootElt_eq F hkl he, F.conj_longRoot g hkl u v hkl' (β k u) (β l v) (hg k u) (hg l v),
      longRoot_eq_rootElt F hkl' rfl]
    congr 1
    push_cast
    ring

theorem conj_rootElt_of_diag (g : spinGroup Q) (w : Fin n → Bool → K)
    (hg : ∀ m r, spinAction Q g (F.vec m r) = w m r • F.vec m r) {e : Fin n → ℤ} {k l : Fin n}
    (hkl : k ≠ l) {u v : Bool} (he : e = Pi.single k (boolSign u) + Pi.single l (boolSign v))
    (c : K) : g * rootElt F e c * g⁻¹ = rootElt F e (w k u * w l v * c) := by
  rw [rootElt_eq F hkl he, F.conj_longRoot g hkl u v hkl u v (hg k u) (hg l v),
    rootElt_eq F hkl he]
  congr 2
  ring

theorem longCoroot_eq (i j : Fin n) (s t : Bool) (m : Fin n) (r : Bool) :
    longCoroot i j s t m r =
      boolSign r * (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin n → ℤ) m := by
  simp only [longCoroot, Pi.add_apply, Pi.single_apply, mul_add, mul_ite, mul_zero]
  congr 1 <;> split_ifs <;> subst_vars <;> first | rfl | (cases r <;> cases s <;> simp_all) |
    (cases r <;> cases t <;> simp_all)

theorem longCoroot_add_longCoroot {e : Fin n → ℤ} (i j : Fin n) (s t : Bool) {k l : Fin n}
    {u v : Bool} (he : e = Pi.single k (boolSign u) + Pi.single l (boolSign v)) :
    longCoroot i j s t k u + longCoroot i j s t l v =
      e ⬝ᵥ (Pi.single i (boolSign s) + Pi.single j (boolSign t)) := by
  rw [longCoroot_eq, longCoroot_eq, he, add_dotProduct, single_dotProduct, single_dotProduct]

theorem longTorus_conj_rootElt {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ)
    {e : Fin n → ℤ} (he : IsLong e) (c : K) :
    F.longTorus hij s t τ * rootElt F e c * (F.longTorus hij s t τ)⁻¹ =
      rootElt F e
        (((τ ^ (e ⬝ᵥ (Pi.single i (boolSign s) + Pi.single j (boolSign t))) : Kˣ) : K) * c) := by
  obtain ⟨k, l, hkl, u, v, he⟩ := he
  rw [conj_rootElt_of_diag F _ _ (F.spinAction_longTorus_vec hij s t τ) hkl he,
    ← longCoroot_add_longCoroot i j s t he, zpow_add, Units.val_mul]

theorem longWeyl_conj_rootElt {i j : Fin n} (hij : i ≠ j) (s t : Bool) {e : Fin n → ℤ}
    {k l : Fin n} (hkl : k ≠ l) {u v : Bool}
    (he : e = Pi.single k (boolSign u) + Pi.single l (boolSign v)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      F.longWeyl hij s t * rootElt F e c * (F.longWeyl hij s t)⁻¹ =
        rootElt F (Pi.single (Equiv.swap i j k) (boolSign (longWeylBool i j s t k u)) +
          Pi.single (Equiv.swap i j l) (boolSign (longWeylBool i j s t l v))) ((ε : K) * c) := by
  refine conj_rootElt_of_signedPerm F _ _ (longWeylBool i j s t)
    (fun m _ => if m = i then -1 else 1) (fun _ m => by split_ifs <;> simp) (fun m r => ?_) hkl he
  rw [F.spinAction_longWeyl_vec hij s t m r]
  congr 1
  simp only [longWeylSign]
  split_ifs <;> simp

section SL2Pair

variable {A : Type*} [Ring A] [Algebra K A] (P : SL2Pair A)

theorem sl2Pair_eq_zero_of_smul_add (hX : P.X ≠ 0) (hY : P.Y ≠ 0) {p q r w : K}
    (h : p • (P.X * P.Y) + q • P.X + r • P.Y + w • (P.Y * P.X) = 0) :
    p = 0 ∧ q = 0 ∧ r = 0 ∧ w = 0 := by
  have hXYX : P.X * P.Y * P.X = P.X := by rw [mul_assoc, P.X_mul_Y_mul_X]
  have hYXY : P.Y * P.X * P.Y = P.Y := by rw [mul_assoc, P.Y_mul_X_mul_Y]
  have h1 : r • (P.X * P.Y) + w • P.X = 0 := by
    have := congrArg (P.X * ·) h
    simp only [mul_add, mul_smul_comm, mul_zero, P.X_mul_X_mul, P.X_mul_X, P.X_mul_Y_mul_X,
      smul_zero, zero_add] at this
    exact this
  have hr : r = 0 := by
    have := congrArg (· * P.X) h1
    simp only [add_mul, smul_mul_assoc, zero_mul, hXYX, P.X_mul_X, smul_zero, add_zero] at this
    exact (smul_eq_zero.mp this).resolve_right hX
  have hw : w = 0 := by
    rw [hr, zero_smul, zero_add] at h1
    exact (smul_eq_zero.mp h1).resolve_right hX
  have h2 : p • P.Y + q • (P.Y * P.X) = 0 := by
    have := congrArg (P.Y * ·) h
    simp only [mul_add, mul_smul_comm, mul_zero, P.Y_mul_X_mul_Y, hr, hw, zero_smul,
      add_zero] at this
    exact this
  have hq : q = 0 := by
    have := congrArg (· * P.Y) h2
    simp only [add_mul, smul_mul_assoc, zero_mul, hYXY, P.Y_mul_Y, smul_zero, zero_add] at this
    exact (smul_eq_zero.mp this).resolve_right hY
  have hp : p = 0 := by
    rw [hq, zero_smul, add_zero] at h2
    exact (smul_eq_zero.mp h2).resolve_right hY
  exact ⟨hp, hq, hr, hw⟩

theorem sl2Pair_toFun_injective (hX : P.X ≠ 0) (hY : P.Y ≠ 0) :
    Function.Injective (P.toFun (K := K)) := by
  intro M N h
  have key := sl2Pair_eq_zero_of_smul_add P hX hY (p := M 0 0 - N 0 0) (q := M 0 1 - N 0 1)
    (r := M 1 0 - N 1 0) (w := M 1 1 - N 1 1) (by
      rw [← sub_eq_zero] at h
      rw [← h]
      simp only [SL2Pair.toFun, sub_smul]
      abel)
  obtain ⟨h1, h2, h3, h4⟩ := key
  ext a b
  fin_cases a <;> fin_cases b
  · exact sub_eq_zero.mp h1
  · exact sub_eq_zero.mp h2
  · exact sub_eq_zero.mp h3
  · exact sub_eq_zero.mp h4

end SL2Pair

theorem longSL2_injective {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    Function.Injective (F.longSL2 hij s t) := by
  intro M N h
  have hX : (F.longPair hij s t).X ≠ 0 :=
    ι_mul_ι_ne_zero Q (F.linearIndependent_vec_pair hij s t)
  have hY : (F.longPair hij s t).Y ≠ 0 :=
    ι_mul_ι_ne_zero Q (F.linearIndependent_vec_pair hij.symm (!t) (!s))
  have h' := congrArg (fun g : spinGroup Q => (g : CliffordAlgebra Q)) h
  simp only [HypFrame.coe_longSL2] at h'
  exact Subtype.ext (sl2Pair_toFun_injective _ hX hY h')

theorem longSL2_upperSL2_eq_rootElt {i j : Fin n} (hij : i < j) (t : Bool) {e : Fin n → ℤ}
    (he : e = Pi.single i (boolSign true) + Pi.single j (boolSign t)) (c : K) :
    F.longSL2 hij.ne true t (upperSL2 c) = rootElt F e c := by
  rw [HypFrame.longSL2_upperSL2, rootElt_eq_of_lt F hij he, boolSign_true, Int.cast_one, one_mul]

theorem longSL2_lowerSL2_eq_rootElt {i j : Fin n} (hij : i < j) (t : Bool) {e : Fin n → ℤ}
    (he : e = Pi.single i (boolSign true) + Pi.single j (boolSign t)) (c : K) :
    F.longSL2 hij.ne true t (lowerSL2 c) = rootElt F (-e) c := by
  have he' : -e = Pi.single j (boolSign (!t)) + Pi.single i (boolSign (!true)) := by
    rw [he, neg_add, ← Pi.single_neg, ← Pi.single_neg, boolSign_not, boolSign_not, add_comm]
  rw [HypFrame.longSL2_lowerSL2, rootElt_eq F hij.ne.symm he', repSign_of_not_lt (lt_asymm hij),
    Bool.not_true, boolSign_false, neg_neg, Int.cast_one, one_mul]

theorem weylSL2_eq_diagSL2_mul (τ : Kˣ) : weylSL2 τ = diagSL2 τ * weylSL2 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem longSL2_weylSL2 {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ) :
    F.longSL2 hij s t (weylSL2 τ) = F.longTorus hij s t τ * F.longWeyl hij s t := by
  rw [weylSL2_eq_diagSL2_mul, map_mul, HypFrame.longTorus_apply, HypFrame.longWeyl]

end CFSG.LieType.Steinberg.SpinFrame
