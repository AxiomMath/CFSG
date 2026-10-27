module

public import CFSG.LieType.Universal.Spin.Chevalley.Frame

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap
open scoped commutatorElement

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ}

theorem commutatorElement_eq_of_mul_mul_inv_eq {G : Type*} [Group G] {x y z : G}
    (h : x * y * x⁻¹ = z * y) : ⁅x, y⁆ = z := by
  rw [commutatorElement_def, h, mul_inv_cancel_right]

theorem commute_one_add_smul {A : Type*} [Ring A] [Algebra K A] {X Y : A} (h : Commute X Y)
    (a b : K) : Commute (1 + a • X) (1 + b • Y) :=
  (Commute.one_left _).add_left
    ((Commute.one_right _).add_right ((h.smul_left a).smul_right b))

theorem commute_of_coe {x y : spinGroup Q} (h : Commute (x : CliffordAlgebra Q) y) :
    Commute x y :=
  Subtype.ext (by rw [Submonoid.coe_mul, Submonoid.coe_mul]; exact h.eq)

theorem coe_mul_rootHom_mul_inv (g : spinGroup Q) {u w : V} (hu : Q u = 0)
    (huw : polar Q u w = 0) (hmem : ∀ c : K, 1 + c • (ι Q w * ι Q u) ∈ spinGroup Q) (c : K) :
    ((g * rootHom Q hu huw hmem (.ofAdd c) * g⁻¹ : spinGroup Q) : CliffordAlgebra Q) =
      1 + c • (ι Q (spinAction Q g w) * ι Q (spinAction Q g u)) := by
  rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_rootHom, coe_mul_one_add_smul_mul_coe_inv]

namespace HypFrame

variable (F : HypFrame Q n)

theorem coe_mul_longRoot_mul_inv (g : spinGroup Q) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (c : K) :
    ((g * F.longRoot hij s t (.ofAdd c) * g⁻¹ : spinGroup Q) : CliffordAlgebra Q) =
      1 + c • (ι Q (spinAction Q g (F.vec i s)) * ι Q (spinAction Q g (F.vec j t))) := by
  rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_longRoot, coe_mul_one_add_smul_mul_coe_inv]

theorem conj_longRoot (g : spinGroup Q) {i j : Fin n} (hij : i ≠ j) (s t : Bool) {i' j' : Fin n}
    (hij' : i' ≠ j') (s' t' : Bool) {l m : K}
    (hi : spinAction Q g (F.vec i s) = l • F.vec i' s')
    (hj : spinAction Q g (F.vec j t) = m • F.vec j' t') (c : K) :
    g * F.longRoot hij s t (.ofAdd c) * g⁻¹ = F.longRoot hij' s' t' (.ofAdd (l * m * c)) := by
  apply Subtype.ext
  rw [coe_mul_longRoot_mul_inv, coe_longRoot, hi, hj, map_smul, map_smul, smul_mul_smul_comm,
    smul_smul, mul_comm (l * m)]

theorem commutator_longRoot_longRoot {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (s t u : Bool) (a b : K) :
    ⁅F.longRoot hij s t (.ofAdd a), F.longRoot hjk (!t) u (.ofAdd b)⁆ =
      F.longRoot hik s u (.ofAdd (a * b)) := by
  apply commutatorElement_eq_of_mul_mul_inv_eq
  apply Subtype.ext
  rw [F.coe_mul_longRoot_mul_inv, Submonoid.coe_mul, coe_longRoot, coe_longRoot,
    spinAction_longRoot_vec_not_right, F.spinAction_longRoot_vec_of_ne hij s t a hik.symm hjk.symm]
  have h0 : ι Q (F.vec i s) * ι Q (F.vec k u) * (ι Q (F.vec j (!t)) * ι Q (F.vec k u)) = 0 := by
    rw [mul_assoc, ← mul_assoc (ι Q (F.vec k u)),
      ι_mul_ι_mul_ι_eq_zero Q (F.map_vec k u) (F.polar_vec_of_ne hjk.symm u (!t)), mul_zero]
  simp only [map_add, map_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    h0, smul_zero, add_zero]
  module

theorem commute_longRoot_longRoot_of_disjoint {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (s t u v : Bool) (a b : K) :
    Commute (F.longRoot hij s t (.ofAdd a)) (F.longRoot hkl u v (.ofAdd b)) := by
  refine commute_of_coe ?_
  rw [coe_longRoot, coe_longRoot]
  exact commute_one_add_smul (commute_ι_mul_ι Q (F.polar_vec_of_ne hik s u)
    (F.polar_vec_of_ne hil s v) (F.polar_vec_of_ne hjk t u) (F.polar_vec_of_ne hjl t v)) a b

theorem commute_longRoot_longRoot_left {i j l : Fin n} (hij : i ≠ j) (hil : i ≠ l)
    (s t v : Bool) (a b : K) :
    Commute (F.longRoot hij s t (.ofAdd a)) (F.longRoot hil s v (.ofAdd b)) := by
  refine commute_of_coe ?_
  rw [coe_longRoot, coe_longRoot]
  refine commute_one_add_smul ?_ a b
  have h : ∀ {m : Fin n} (_ : i ≠ m) (w : Bool) (x : CliffordAlgebra Q),
      ι Q (F.vec i s) * ι Q (F.vec m w) * (ι Q (F.vec i s) * x) = 0 := fun hm w x => by
    rw [F.ι_vec_mul_ι_vec_of_ne hm, neg_mul, mul_assoc, F.ι_vec_mul_ι_vec_self_mul, mul_zero,
      neg_zero]
  change _ * _ = _ * _
  rw [h hij, h hil]

theorem commute_longRoot_longRoot_right {i j k : Fin n} (hij : i ≠ j) (hkj : k ≠ j)
    (s t u : Bool) (a b : K) :
    Commute (F.longRoot hij s t (.ofAdd a)) (F.longRoot hkj u t (.ofAdd b)) := by
  refine commute_of_coe ?_
  rw [coe_longRoot, coe_longRoot]
  refine commute_one_add_smul ?_ a b
  have h : ∀ {m : Fin n} (_ : m ≠ j) (w : Bool) (x : CliffordAlgebra Q),
      x * ι Q (F.vec j t) * (ι Q (F.vec m w) * ι Q (F.vec j t)) = 0 := fun hm w x => by
    rw [mul_assoc, ← mul_assoc (ι Q (F.vec j t)),
      ι_mul_ι_mul_ι_eq_zero Q (F.map_vec j t) (F.polar_vec_of_ne hm.symm t w), mul_zero]
  change _ * _ = _ * _
  rw [h hkj, h hij]

end HypFrame

namespace OddFrame

variable (F : OddFrame Q n)

theorem coe_mul_shortRoot_mul_inv (g : spinGroup Q) (i : Fin n) (s : Bool) (c : K) :
    ((g * F.shortRoot i s (.ofAdd c) * g⁻¹ : spinGroup Q) : CliffordAlgebra Q) =
      1 + c • (ι Q (spinAction Q g F.z) * ι Q (spinAction Q g (F.vec i s))) := by
  rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_shortRoot, coe_mul_one_add_smul_mul_coe_inv]

theorem conj_shortRoot (g : spinGroup Q) (i : Fin n) (s : Bool) (i' : Fin n) (s' : Bool) {l m : K}
    (hz : spinAction Q g F.z = l • F.z) (hi : spinAction Q g (F.vec i s) = m • F.vec i' s')
    (c : K) : g * F.shortRoot i s (.ofAdd c) * g⁻¹ = F.shortRoot i' s' (.ofAdd (l * m * c)) := by
  apply Subtype.ext
  rw [coe_mul_shortRoot_mul_inv, coe_shortRoot, hz, hi, map_smul, map_smul, smul_mul_smul_comm,
    smul_smul, mul_comm (l * m)]

theorem commutator_shortRoot_shortRoot {i j : Fin n} (hij : i ≠ j) (s t : Bool) (a b : K) :
    ⁅F.shortRoot i s (.ofAdd a), F.shortRoot j t (.ofAdd b)⁆ =
      F.longRoot hij s t (.ofAdd (-2 * a * b)) := by
  apply commutatorElement_eq_of_mul_mul_inv_eq
  apply Subtype.ext
  rw [F.coe_mul_shortRoot_mul_inv, Submonoid.coe_mul, HypFrame.coe_longRoot, coe_shortRoot,
    spinAction_shortRoot_z, F.spinAction_shortRoot_vec_of_ne i s a hij.symm]
  have h0 : ι Q (F.vec i s) * ι Q (F.vec j t) * (ι Q F.z * ι Q (F.vec j t)) = 0 := by
    rw [mul_assoc, ← mul_assoc (ι Q (F.vec j t)),
      ι_mul_ι_mul_ι_eq_zero Q (F.map_vec j t) (F.polar_vec_z j t), mul_zero]
  simp only [map_sub, map_smul, sub_mul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one, h0, smul_zero, add_zero]
  module

theorem commutator_longRoot_shortRoot {i j : Fin n} (hij : i ≠ j) (s t : Bool) (a b : K) :
    ⁅F.longRoot hij s t (.ofAdd a), F.shortRoot j (!t) (.ofAdd b)⁆ =
      F.shortRoot i s (.ofAdd (a * b)) * F.longRoot hij s (!t) (.ofAdd (a * b ^ 2)) := by
  apply commutatorElement_eq_of_mul_mul_inv_eq
  apply Subtype.ext
  rw [F.coe_mul_shortRoot_mul_inv, Submonoid.coe_mul, Submonoid.coe_mul, HypFrame.coe_longRoot,
    coe_shortRoot, coe_shortRoot, spinAction_longRoot_z, HypFrame.spinAction_longRoot_vec_not_right,
    map_add, map_smul]
  set Z := ι Q F.z
  set A := ι Q (F.vec i s)
  set B := ι Q (F.vec j (!t))
  have hZA : A * Z = -(Z * A) := F.ι_vec_mul_ι_z i s
  have hAA : A * A = 0 := F.ι_vec_mul_ι_vec_self i s
  have hZZ : Z * Z = 1 := F.ι_z_mul_ι_z
  have e1 : Z * A * (A * B) = 0 := by rw [mul_assoc, ← mul_assoc A, hAA, zero_mul, mul_zero]
  have e2 : Z * A * (Z * B) = -(A * B) := by
    rw [mul_assoc, ← mul_assoc A, hZA, neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, hZZ, one_mul]
  have e3 : A * B * (Z * B) = 0 := by
    rw [mul_assoc, ← mul_assoc B,
      ι_mul_ι_mul_ι_eq_zero Q (F.map_vec j (!t)) (F.polar_vec_z j (!t)), mul_zero]
  have e12 : (1 + (a * b) • (Z * A)) * (1 + (a * b ^ 2) • (A * B)) =
      1 + (a * b) • (Z * A) + (a * b ^ 2) • (A * B) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, e1, smul_zero,
      add_zero]
  rw [e12]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, e2, e3, smul_zero,
    add_zero, smul_neg]
  module

theorem commute_longRoot_shortRoot_of_ne {i j k : Fin n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (s t u : Bool) (a b : K) :
    Commute (F.longRoot hij s t (.ofAdd a)) (F.shortRoot k u (.ofAdd b)) := by
  refine commute_of_coe ?_
  rw [HypFrame.coe_longRoot, coe_shortRoot]
  exact commute_one_add_smul (commute_ι_mul_ι Q (F.polar_vec_z i s)
    (F.polar_vec_of_ne hki.symm s u) (F.polar_vec_z j t) (F.polar_vec_of_ne hkj.symm t u)) a b

theorem commute_longRoot_shortRoot_left {i j : Fin n} (hij : i ≠ j) (s t : Bool) (a b : K) :
    Commute (F.longRoot hij s t (.ofAdd a)) (F.shortRoot i s (.ofAdd b)) := by
  refine commute_of_coe ?_
  rw [HypFrame.coe_longRoot, coe_shortRoot]
  refine commute_one_add_smul ?_ a b
  set Z := ι Q F.z
  set A := ι Q (F.vec i s)
  set B := ι Q (F.vec j t)
  have hAA : ∀ x, A * (A * x) = 0 := F.ι_vec_mul_ι_vec_self_mul i s
  have hBZ : A * (B * Z) = B * Z * A :=
    ι_mul_ι_mul_ι_comm Q (F.polar_vec_of_ne hij s t) (F.polar_vec_z i s)
  have hA2 : A * A = 0 := F.ι_vec_mul_ι_vec_self i s
  have hL : A * B * (Z * A) = 0 := by
    rw [mul_assoc, ← mul_assoc B, ← mul_assoc A, hBZ, mul_assoc, hA2, mul_zero]
  have hR : Z * A * (A * B) = 0 := by rw [mul_assoc, hAA, mul_zero]
  change A * B * (Z * A) = Z * A * (A * B)
  rw [hL, hR]

theorem commute_longRoot_shortRoot_right {i j : Fin n} (hij : i ≠ j) (s t : Bool) (a b : K) :
    Commute (F.longRoot hij s t (.ofAdd a)) (F.shortRoot j t (.ofAdd b)) := by
  refine commute_of_coe ?_
  rw [HypFrame.coe_longRoot, coe_shortRoot]
  refine commute_one_add_smul ?_ a b
  set Z := ι Q F.z
  set A := ι Q (F.vec i s)
  set B := ι Q (F.vec j t)
  have hBAB : B * A * B = 0 := ι_mul_ι_mul_ι_eq_zero Q (F.map_vec j t) (F.polar_vec_of_ne hij.symm t s)
  have hBZB : B * Z * B = 0 := ι_mul_ι_mul_ι_eq_zero Q (F.map_vec j t) (F.polar_vec_z j t)
  have hL : A * B * (Z * B) = 0 := by rw [mul_assoc, ← mul_assoc B, hBZB, mul_zero]
  have hR : Z * B * (A * B) = 0 := by rw [mul_assoc, ← mul_assoc B, hBAB, mul_zero]
  change A * B * (Z * B) = Z * B * (A * B)
  rw [hL, hR]

end OddFrame

end CFSG.LieType.Universal.Spin
