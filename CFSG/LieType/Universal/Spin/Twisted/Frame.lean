module

public import CFSG.LieType.Universal.Spin.Twisted.RankOne
public import CFSG.LieType.Universal.Spin.Chevalley.ShortRankOne

public section

namespace CFSG.LieType.Universal.Spin.Twisted

open CliffordAlgebra QuadraticMap
open scoped commutatorElement

variable (n : ℕ) {K : Type*} [Field K] (b c : K)

@[expose] def minusVec (i : Fin (n - 1)) : Bool → Vm n K
  | true => eVec n i
  | false => fVec n i

@[simp] theorem minusVec_true (i : Fin (n - 1)) : minusVec n (K := K) i true = eVec n i := rfl

@[simp] theorem minusVec_false (i : Fin (n - 1)) : minusVec n (K := K) i false = fVec n i := rfl

theorem quadMinus_minusVec (i : Fin (n - 1)) (s : Bool) :
    quadMinus n K b c (minusVec n i s) = 0 := by
  cases s
  · exact quadMinus_fVec n b c i
  · exact quadMinus_eVec n b c i

theorem polar_minusVec_minusVec (i j : Fin (n - 1)) (s t : Bool) :
    polar (quadMinus n K b c) (minusVec n i s) (minusVec n j t) =
      if i = j ∧ s = !t then 1 else 0 := by
  cases s <;> cases t
  · simp [polar_fVec_fVec]
  · rw [minusVec_false, minusVec_true, polar_fVec_eVec]
    simp
  · rw [minusVec_true, minusVec_false, polar_eVec_fVec]
    simp
  · simp [polar_eVec_eVec]

theorem polar_minusVec_planeVec (i : Fin (n - 1)) (s : Bool) (w : Fin 2 → K) :
    polar (quadMinus n K b c) (minusVec n i s) (planeVec n w) = 0 := by
  cases s
  · exact polar_fVec_planeVec n b c i w
  · exact polar_eVec_planeVec n b c i w

theorem polar_planeVec_minusVec (w : Fin 2 → K) (i : Fin (n - 1)) (s : Bool) :
    polar (quadMinus n K b c) (planeVec n w) (minusVec n i s) = 0 := by
  rw [polar_comm, polar_minusVec_planeVec]

theorem quadMinus_planeOne : quadMinus n K b c (planeVec n planeOne) = 1 := by
  rw [quadMinus_planeVec', planeNorm_planeOne]

@[expose] noncomputable def minusFrame : OddFrame (quadMinus n K b c) (n - 1) :=
  OddFrame.ofZ (minusVec n) (quadMinus_minusVec n b c)
    (fun i j hij s t => by rw [polar_minusVec_minusVec, ite_eq_right fun h => hij h.1])
    (fun i s => by rw [polar_minusVec_minusVec, ite_eq_left ⟨rfl, by rw [Bool.not_not]⟩])
    (planeVec n planeOne) (quadMinus_planeOne n b c)
    (fun i s => polar_minusVec_planeVec n b c i s planeOne)

@[simp] theorem minusFrame_vec : (minusFrame n b c).vec = minusVec n := rfl

@[simp] theorem minusFrame_z : (minusFrame n b c).z = planeVec n planeOne := rfl

theorem eq_planeVec_of_polar_minusVec {v : Vm n K}
    (hv : ∀ k r, polar (quadMinus n K b c) v (minusVec n k r) = 0) :
    v = planeVec n (fun t => v (.inr (.inr t))) := by
  funext x
  rcases x with k | k | t
  · have h := hv k false
    rw [minusVec_false, fVec, polar_quadMinus_single_inr_inl] at h
    simp [planeVec, h]
  · have h := hv k true
    rw [minusVec_true, eVec, polar_quadMinus_single_inl] at h
    simp [planeVec, h]
  · simp [planeVec]

variable {b c} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def twShortRoot (i : Fin (n - 1)) :
    Bool → Multiplicative (Fin 2 → K) →* spinGroup (quadMinus n K b c)
  | true => shortPosHom n hirr i
  | false => shortNegHom n hirr i

@[simp] theorem twShortRoot_true (i : Fin (n - 1)) :
    twShortRoot n hirr i true = shortPosHom n hirr i := rfl

@[simp] theorem twShortRoot_false (i : Fin (n - 1)) :
    twShortRoot n hirr i false = shortNegHom n hirr i := rfl

theorem coe_twShortRoot (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K) :
    (twShortRoot n hirr i s (.ofAdd p) : CliffordAlgebra (quadMinus n K b c)) =
      1 + ι (quadMinus n K b c) (planeVec n p) * ι (quadMinus n K b c) (minusVec n i s) := by
  cases s <;> rfl

theorem twShortRoot_injective (i : Fin (n - 1)) (s : Bool) :
    Function.Injective (twShortRoot n hirr i s) := by
  cases s
  · exact shortNegHom_injective n hirr i
  · exact shortPosHom_injective n hirr i

theorem twShortRoot_ofAdd_zero (i : Fin (n - 1)) (s : Bool) :
    twShortRoot n hirr i s (.ofAdd 0) = 1 := by
  rw [ofAdd_zero, map_one]

theorem spinAction_twShortRoot (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K) (v : Vm n K) :
    spinAction (quadMinus n K b c) (twShortRoot n hirr i s (.ofAdd p)) v =
      v + polar (quadMinus n K b c) v (minusVec n i s) • planeVec n p -
        polar (quadMinus n K b c) v (planeVec n p) • minusVec n i s -
        (planeNorm b c p * polar (quadMinus n K b c) v (minusVec n i s)) • minusVec n i s := by
  rw [spinAction_apply_of_coe_eq _ (quadMinus_minusVec n b c i s)
    (polar_minusVec_planeVec n b c i s p) (coe_twShortRoot n hirr i s p) v, quadMinus_planeVec']

theorem spinAction_twShortRoot_of_polar (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K) {v : Vm n K}
    (h1 : polar (quadMinus n K b c) v (minusVec n i s) = 0)
    (h2 : polar (quadMinus n K b c) v (planeVec n p) = 0) :
    spinAction (quadMinus n K b c) (twShortRoot n hirr i s (.ofAdd p)) v = v := by
  rw [spinAction_twShortRoot, h1, h2]
  simp

theorem spinAction_twShortRoot_vec_of_ne {i k : Fin (n - 1)} (hki : k ≠ i) (s : Bool)
    (p : Fin 2 → K) (u : Bool) :
    spinAction (quadMinus n K b c) (twShortRoot n hirr i s (.ofAdd p)) (minusVec n k u) =
      minusVec n k u :=
  spinAction_twShortRoot_of_polar n hirr i s p
    (by rw [polar_minusVec_minusVec, ite_eq_right fun h => hki h.1])
    (polar_minusVec_planeVec n b c k u p)

@[simp]
theorem spinAction_twShortRoot_vec_self (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K) :
    spinAction (quadMinus n K b c) (twShortRoot n hirr i s (.ofAdd p)) (minusVec n i s) =
      minusVec n i s :=
  spinAction_twShortRoot_of_polar n hirr i s p
    (by rw [polar_minusVec_minusVec]; cases s <;> simp)
    (polar_minusVec_planeVec n b c i s p)

@[simp]
theorem spinAction_twShortRoot_vec_not (i : Fin (n - 1)) (s : Bool) (p : Fin 2 → K) :
    spinAction (quadMinus n K b c) (twShortRoot n hirr i s (.ofAdd p)) (minusVec n i (!s)) =
      minusVec n i (!s) + planeVec n p - planeNorm b c p • minusVec n i s := by
  rw [spinAction_twShortRoot, polar_minusVec_minusVec, ite_eq_left ⟨rfl, rfl⟩,
    polar_minusVec_planeVec]
  simp

theorem spinAction_twShortRoot_planeVec (i : Fin (n - 1)) (s : Bool) (p q : Fin 2 → K) :
    spinAction (quadMinus n K b c) (twShortRoot n hirr i s (.ofAdd p)) (planeVec n q) =
      planeVec n q - polarPlane b c q p • minusVec n i s := by
  rw [spinAction_twShortRoot, polar_planeVec_minusVec, polar_planeVec_planeVec]
  simp

theorem conj_twShortRoot (g : spinGroup (quadMinus n K b c)) (i : Fin (n - 1)) (s : Bool)
    {i' : Fin (n - 1)} {s' : Bool} {p q : Fin 2 → K} {r : K}
    (hv : spinAction (quadMinus n K b c) g (minusVec n i s) = r • minusVec n i' s')
    (hp : spinAction (quadMinus n K b c) g (planeVec n p) = planeVec n q) :
    g * twShortRoot n hirr i s (.ofAdd p) * g⁻¹ = twShortRoot n hirr i' s' (.ofAdd (r • q)) := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_twShortRoot, coe_conj_one_add_ι_mul_ι, hv, hp,
    coe_twShortRoot, planeVec_smul, map_smul, map_smul, smul_mul_assoc, mul_smul_comm]

theorem minusFrame_shortRoot (i : Fin (n - 1)) (s : Bool) (a : K) :
    (minusFrame n b c).shortRoot i s (.ofAdd a) =
      twShortRoot n hirr i s (.ofAdd (a • planeOne)) := by
  apply Subtype.ext
  rw [OddFrame.coe_shortRoot, coe_twShortRoot, planeVec_smul, map_smul, smul_mul_assoc]
  rfl

theorem shortWeyl_eq_minusFrame (i : Fin (n - 1)) :
    shortWeyl n hirr i = (minusFrame n b c).shortWeyl i true := by
  rw [OddFrame.shortWeyl_eq, minusFrame_shortRoot n hirr, minusFrame_shortRoot n hirr, one_smul,
    shortWeyl_eq, twShortRoot_true, Bool.not_true, twShortRoot_false]

theorem minusFrame_shortTorus_eq (i : Fin (n - 1)) (μ : Kˣ) :
    (minusFrame n b c).shortTorus i true μ = shortTorusElt n hirr i ((μ : K) • planeOne) := by
  have hμ : (μ : K) ≠ 0 := μ.ne_zero
  rw [OddFrame.shortTorus_apply, diagSL2_eq, map_mul, shortTorusElt, shortWeyl,
    ← shortWeylElt_neg n hirr]
  congr 1
  · rw [weylSL2_eq, map_mul, map_mul, OddFrame.shortSL2_upperSL2, OddFrame.shortSL2_lowerSL2,
      minusFrame_shortRoot n hirr, minusFrame_shortRoot n hirr, Bool.not_true, neg_neg,
      shortWeylElt, twShortRoot_true, twShortRoot_false, planeNorm_smul, planeNorm_planeOne,
      mul_one, smul_smul]
    congr 3
    rw [Units.val_inv_eq_inv_val]
    field_simp
  · rw [weylSL2_eq, map_mul, map_mul, OddFrame.shortSL2_upperSL2, OddFrame.shortSL2_lowerSL2,
      minusFrame_shortRoot n hirr, minusFrame_shortRoot n hirr, Bool.not_true, shortWeylElt,
      twShortRoot_true, twShortRoot_false, planeNorm_neg, planeNorm_planeOne, inv_one, one_smul]
    simp

theorem spinAction_longWeyl_planeVec {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool)
    (p : Fin 2 → K) :
    spinAction (quadMinus n K b c) ((minusFrame n b c).longWeyl hij s t) (planeVec n p) =
      planeVec n p :=
  (minusFrame n b c).spinAction_longWeyl_of_polar hij s t
    (fun r => polar_planeVec_minusVec n b c p i r) (fun r => polar_planeVec_minusVec n b c p j r)

theorem spinAction_longTorus_planeVec {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (τ : Kˣ)
    (p : Fin 2 → K) :
    spinAction (quadMinus n K b c) ((minusFrame n b c).longTorus hij s t τ) (planeVec n p) =
      planeVec n p := by
  rw [HypFrame.spinAction_longTorus]
  simp [polar_planeVec_minusVec]

theorem spinAction_longRoot_planeVec {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (a : K)
    (p : Fin 2 → K) :
    spinAction (quadMinus n K b c) ((minusFrame n b c).longRoot hij s t (.ofAdd a))
      (planeVec n p) = planeVec n p :=
  (minusFrame n b c).spinAction_longRoot_of_polar hij s t a (polar_planeVec_minusVec n b c p i s)
    (polar_planeVec_minusVec n b c p j t)

theorem longWeyl_conj_twShortRoot {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (k : Fin (n - 1))
    (u : Bool) (p : Fin 2 → K) :
    (minusFrame n b c).longWeyl hij s t * twShortRoot n hirr k u (.ofAdd p) *
        ((minusFrame n b c).longWeyl hij s t)⁻¹ =
      twShortRoot n hirr (Equiv.swap i j k) (longWeylBool i j s t k u)
        (.ofAdd ((longWeylSign i k : K) • p)) :=
  conj_twShortRoot n hirr _ k u ((minusFrame n b c).spinAction_longWeyl_vec hij s t k u)
    (spinAction_longWeyl_planeVec n hij s t p)

theorem longTorus_conj_twShortRoot {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (τ : Kˣ)
    (k : Fin (n - 1)) (u : Bool) (p : Fin 2 → K) :
    (minusFrame n b c).longTorus hij s t τ * twShortRoot n hirr k u (.ofAdd p) *
        ((minusFrame n b c).longTorus hij s t τ)⁻¹ =
      twShortRoot n hirr k u (.ofAdd (((τ ^ longCoroot i j s t k u : Kˣ) : K) • p)) :=
  conj_twShortRoot n hirr _ k u ((minusFrame n b c).spinAction_longTorus_vec hij s t τ k u)
    (spinAction_longTorus_planeVec n hij s t τ p)

theorem spinAction_shortWeyl_minusVec (i m : Fin (n - 1)) (r : Bool) :
    spinAction (quadMinus n K b c) (shortWeyl n hirr i) (minusVec n m r) =
      (longWeylSign i m : K) • minusVec n m (shortWeylBool i m r) := by
  rw [shortWeyl_eq_minusFrame n hirr]
  exact (minusFrame n b c).spinAction_shortWeyl_vec i true m r

theorem shortWeyl_conj_longRoot (i : Fin (n - 1)) {k l : Fin (n - 1)} (hkl : k ≠ l) (u v : Bool)
    (a : K) :
    shortWeyl n hirr i * (minusFrame n b c).longRoot hkl u v (.ofAdd a) *
        (shortWeyl n hirr i)⁻¹ =
      (minusFrame n b c).longRoot hkl (shortWeylBool i k u) (shortWeylBool i l v)
        (.ofAdd ((longWeylSign i k : K) * longWeylSign i l * a)) := by
  rw [shortWeyl_eq_minusFrame n hirr]
  exact (minusFrame n b c).shortWeyl_conj_longRoot i true hkl u v a

variable (b c) in
@[expose] noncomputable def shortTorusScalar (i : Fin (n - 1)) (a : Fin 2 → K) (m : Fin (n - 1))
    (r : Bool) : K :=
  if m = i then (if r then planeNorm b c a else (planeNorm b c a)⁻¹) else 1

theorem spinAction_shortTorusElt_minusVec (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0)
    (m : Fin (n - 1)) (r : Bool) :
    spinAction (quadMinus n K b c) (shortTorusElt n hirr i a) (minusVec n m r) =
      shortTorusScalar n b c i a m r • minusVec n m r := by
  by_cases hm : m = i
  · subst hm
    cases r
    · rw [minusVec_false, spinAction_shortTorusElt_fVec n hirr m ha]
      simp [shortTorusScalar]
    · rw [minusVec_true, spinAction_shortTorusElt_eVec n hirr m ha]
      simp [shortTorusScalar]
  · rw [shortTorusScalar, ite_eq_right hm, one_smul]
    cases r
    · exact spinAction_shortTorusElt_fVec_of_ne n hirr hm a
    · exact spinAction_shortTorusElt_eVec_of_ne n hirr hm a

theorem shortTorusElt_conj_longRoot (i : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0)
    {k l : Fin (n - 1)} (hkl : k ≠ l) (u v : Bool) (x : K) :
    shortTorusElt n hirr i a * (minusFrame n b c).longRoot hkl u v (.ofAdd x) *
        (shortTorusElt n hirr i a)⁻¹ =
      (minusFrame n b c).longRoot hkl u v
        (.ofAdd (shortTorusScalar n b c i a k u * shortTorusScalar n b c i a l v * x)) :=
  (minusFrame n b c).conj_longRoot _ hkl u v hkl u v
    (spinAction_shortTorusElt_minusVec n hirr i ha k u)
    (spinAction_shortTorusElt_minusVec n hirr i ha l v) x

theorem spinAction_shortWeyl_planeVec' (i : Fin (n - 1)) (p : Fin 2 → K) :
    spinAction (quadMinus n K b c) (shortWeyl n hirr i) (planeVec n p) =
      planeVec n (planeRefl b c planeOne p) :=
  spinAction_shortWeyl_planeVec n hirr i p

theorem shortWeyl_conj_twShortRoot (i k : Fin (n - 1)) (u : Bool) (p : Fin 2 → K) :
    shortWeyl n hirr i * twShortRoot n hirr k u (.ofAdd p) * (shortWeyl n hirr i)⁻¹ =
      twShortRoot n hirr k (shortWeylBool i k u)
        (.ofAdd ((longWeylSign i k : K) • planeRefl b c planeOne p)) :=
  conj_twShortRoot n hirr _ k u (spinAction_shortWeyl_minusVec n hirr i k u)
    (spinAction_shortWeyl_planeVec n hirr i p)

theorem commutator_twShortRoot_twShortRoot {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool)
    (p q : Fin 2 → K) :
    ⁅twShortRoot n hirr i s (.ofAdd p), twShortRoot n hirr j t (.ofAdd q)⁆ =
      (minusFrame n b c).longRoot hij s t (.ofAdd (-polarPlane b c p q)) := by
  apply commutatorElement_eq_of_mul_mul_inv_eq
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul, coe_twShortRoot n hirr j t q,
    coe_conj_one_add_ι_mul_ι, spinAction_twShortRoot_planeVec,
    spinAction_twShortRoot_vec_of_ne n hirr hij.symm, HypFrame.coe_longRoot]
  simp only [minusFrame_vec]
  set A := ι (quadMinus n K b c) (minusVec n i s)
  set B := ι (quadMinus n K b c) (minusVec n j t)
  set Z := ι (quadMinus n K b c) (planeVec n q)
  have h0 : A * B * (Z * B) = 0 := by
    rw [mul_assoc, ← mul_assoc B,
      ι_mul_ι_mul_ι_eq_zero _ (quadMinus_minusVec n b c j t)
        (polar_minusVec_planeVec n b c j t q), mul_zero]
  have key : (1 + (-polarPlane b c p q) • (A * B)) * (1 + Z * B) =
      1 + Z * B + (-polarPlane b c p q) • (A * B) := by
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_assoc, h0, smul_zero,
      add_zero, add_right_comm]
  rw [key, map_sub, map_smul, sub_mul, smul_mul_assoc, polarPlane_comm b c q p, neg_smul]
  abel

theorem commutator_longRoot_twShortRoot {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (a : K)
    (q : Fin 2 → K) :
    ⁅(minusFrame n b c).longRoot hij s t (.ofAdd a), twShortRoot n hirr j (!t) (.ofAdd q)⁆ =
      twShortRoot n hirr i s (.ofAdd (a • q)) *
        (minusFrame n b c).longRoot hij s (!t) (.ofAdd (a * planeNorm b c q)) := by
  apply commutatorElement_eq_of_mul_mul_inv_eq
  apply Subtype.ext
  have hW := (minusFrame n b c).spinAction_longRoot_vec_not_right hij s t a
  simp only [minusFrame_vec] at hW
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
    coe_twShortRoot n hirr j (!t) q, coe_conj_one_add_ι_mul_ι, spinAction_longRoot_planeVec, hW,
    coe_twShortRoot, HypFrame.coe_longRoot, map_add, map_smul]
  simp only [minusFrame_vec]
  set Z := ι (quadMinus n K b c) (planeVec n q)
  set A := ι (quadMinus n K b c) (minusVec n i s)
  set B := ι (quadMinus n K b c) (minusVec n j (!t))
  have hZA : A * Z = -(Z * A) := ι_mul_ι_eq_neg_of_polar_eq_zero _
    (polar_minusVec_planeVec n b c i s q)
  have hBZ : B * Z = -(Z * B) := ι_mul_ι_eq_neg_of_polar_eq_zero _
    (polar_minusVec_planeVec n b c j (!t) q)
  have hAA : A * A = 0 := ι_mul_ι_self_eq_zero _ (quadMinus_minusVec n b c i s)
  have hBB : B * B = 0 := ι_mul_ι_self_eq_zero _ (quadMinus_minusVec n b c j (!t))
  have hZZ : Z * Z = algebraMap K _ (planeNorm b c q) := by
    rw [ι_sq_scalar, quadMinus_planeVec']
  have hsq : ι (quadMinus n K b c) (planeVec n (a • q)) = a • Z := by
    rw [planeVec_smul, map_smul]
  rw [hsq]
  have e1 : Z * A * (A * B) = 0 := by rw [mul_assoc, ← mul_assoc A, hAA, zero_mul, mul_zero]
  have e2 : Z * A * (Z * B) = -(planeNorm b c q • (A * B)) := by
    rw [mul_assoc, ← mul_assoc A, hZA, neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, hZZ,
      ← Algebra.smul_def, smul_mul_assoc]
  have e3 : A * B * (Z * B) = 0 := by
    rw [mul_assoc, ← mul_assoc B, hBZ, neg_mul, mul_assoc, hBB, mul_zero, neg_zero, mul_zero]
  simp only [smul_mul_assoc, add_mul, mul_add, mul_smul_comm, one_mul, mul_one, e1, e2, e3,
    smul_zero, add_zero, smul_neg, smul_smul]
  module

theorem commute_longRoot_twShortRoot_of_ne {i j k : Fin (n - 1)} (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) (s t u : Bool) (a : K) (p : Fin 2 → K) :
    Commute ((minusFrame n b c).longRoot hij s t (.ofAdd a))
      (twShortRoot n hirr k u (.ofAdd p)) := by
  refine commute_of_coe ?_
  rw [HypFrame.coe_longRoot, coe_twShortRoot]
  have h : Commute (ι (quadMinus n K b c) (minusVec n i s) * ι (quadMinus n K b c) (minusVec n j t))
      (ι (quadMinus n K b c) (planeVec n p) * ι (quadMinus n K b c) (minusVec n k u)) :=
    commute_ι_mul_ι _ (polar_minusVec_planeVec n b c i s p)
      (by rw [polar_minusVec_minusVec, ite_eq_right fun h => hki h.1.symm])
      (polar_minusVec_planeVec n b c j t p)
      (by rw [polar_minusVec_minusVec, ite_eq_right fun h => hkj h.1.symm])
  exact (Commute.one_left _).add_left ((Commute.one_right _).add_right (h.smul_left a))

theorem commute_longRoot_twShortRoot_left {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (a : K)
    (p : Fin 2 → K) :
    Commute ((minusFrame n b c).longRoot hij s t (.ofAdd a))
      (twShortRoot n hirr i s (.ofAdd p)) := by
  refine commute_of_coe ?_
  rw [HypFrame.coe_longRoot, coe_twShortRoot]
  set Z := ι (quadMinus n K b c) (planeVec n p)
  set A := ι (quadMinus n K b c) (minusVec n i s)
  set B := ι (quadMinus n K b c) (minusVec n j t)
  have hAA : A * A = 0 := ι_mul_ι_self_eq_zero _ (quadMinus_minusVec n b c i s)
  have hBZ : A * (B * Z) = B * Z * A := ι_mul_ι_mul_ι_comm _
    ((minusFrame n b c).polar_vec_of_ne hij s t) (polar_minusVec_planeVec n b c i s p)
  have hL : A * B * (Z * A) = 0 := by
    rw [mul_assoc, ← mul_assoc B, ← mul_assoc A, hBZ, mul_assoc, hAA, mul_zero]
  have hR : Z * A * (A * B) = 0 := by rw [mul_assoc, ← mul_assoc A, hAA, zero_mul, mul_zero]
  have h : Commute (A * B) (Z * A) := by
    change A * B * (Z * A) = Z * A * (A * B)
    rw [hL, hR]
  exact (Commute.one_left _).add_left ((Commute.one_right _).add_right (h.smul_left a))

theorem commute_longRoot_twShortRoot_right {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (a : K)
    (p : Fin 2 → K) :
    Commute ((minusFrame n b c).longRoot hij s t (.ofAdd a))
      (twShortRoot n hirr j t (.ofAdd p)) := by
  refine commute_of_coe ?_
  rw [HypFrame.coe_longRoot, coe_twShortRoot]
  set Z := ι (quadMinus n K b c) (planeVec n p)
  set A := ι (quadMinus n K b c) (minusVec n i s)
  set B := ι (quadMinus n K b c) (minusVec n j t)
  have hBAB : B * A * B = 0 := ι_mul_ι_mul_ι_eq_zero _ (quadMinus_minusVec n b c j t)
    ((minusFrame n b c).polar_vec_of_ne hij.symm t s)
  have hBZB : B * Z * B = 0 := ι_mul_ι_mul_ι_eq_zero _ (quadMinus_minusVec n b c j t)
    (polar_minusVec_planeVec n b c j t p)
  have hL : A * B * (Z * B) = 0 := by rw [mul_assoc, ← mul_assoc B, hBZB, mul_zero]
  have hR : Z * B * (A * B) = 0 := by rw [mul_assoc, ← mul_assoc B, hBAB, mul_zero]
  have h : Commute (A * B) (Z * B) := by
    change A * B * (Z * B) = Z * B * (A * B)
    rw [hL, hR]
  exact (Commute.one_left _).add_left ((Commute.one_right _).add_right (h.smul_left a))

theorem commute_twShortRoot_twShortRoot_same (i : Fin (n - 1)) (s : Bool) (p q : Fin 2 → K) :
    Commute (twShortRoot n hirr i s (.ofAdd p)) (twShortRoot n hirr i s (.ofAdd q)) := by
  exact (Commute.all (Multiplicative.ofAdd p) (Multiplicative.ofAdd q)).map
    (twShortRoot n hirr i s)

end CFSG.LieType.Universal.Spin.Twisted
