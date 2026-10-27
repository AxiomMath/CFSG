module

public import CFSG.Fischer.F4
public import CFSG.LieType.Chevalley.C2E6MinusSixDefs
import all CFSG.Fischer.F4
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def K : Type := F4

instance : Field K := inferInstanceAs (Field F4)

instance : DecidableEq K := inferInstanceAs (DecidableEq F4)

instance : Fintype K := inferInstanceAs (Fintype F4)

instance : CharP K 2 := inferInstanceAs (CharP F4 2)

instance : Algebra (ZMod 2) K := ZMod.algebra K 2

@[expose] def ω : K := F4.ω

@[expose] def bar (a : K) : K := a ^ 2

theorem omega_sq_add_omega_add_one : ω ^ 2 + ω + 1 = 0 := by decide

theorem card_K : Fintype.card K = 4 := by decide

theorem bar_add (a b : K) : bar (a + b) = bar a + bar b := by revert a b; decide

theorem bar_mul (a b : K) : bar (a * b) = bar a * bar b := by
  simp only [bar, mul_pow]

theorem bar_bar (a : K) : bar (bar a) = a := by revert a; decide

theorem bar_zero : bar 0 = 0 := by decide

theorem bar_one : bar 1 = 1 := by decide

theorem irreducible_omega_poly :
    Irreducible (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2)) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2)).natDegree = 2 := by
      compute_degree!
    rw [this]
    decide
  · intro x hx
    rw [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one] at hx
    revert x
    decide

theorem eval₂_omega_poly :
    Polynomial.eval₂ (algebraMap (ZMod 2) K) ω
      (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2)) = 0 := by
  rw [Polynomial.eval₂_add, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_one]
  exact omega_sq_add_omega_add_one

@[expose] def t0 (a : K) : ZMod 2 := ((F4.code a).val : ZMod 2)

@[expose] def t1 (a : K) : ZMod 2 := ((F4.code a).val / 2 : ℕ)

theorem t0_add_t1_omega (a : K) :
    algebraMap (ZMod 2) K (t0 a) + algebraMap (ZMod 2) K (t1 a) * ω = a := by
  revert a; decide

theorem t0_add (a b : K) : t0 (a + b) = t0 a + t0 b := by revert a b; decide

theorem t1_add (a b : K) : t1 (a + b) = t1 a + t1 b := by revert a b; decide

theorem t0_smul (c : ZMod 2) (a : K) : t0 (c • a) = c * t0 a := by revert c a; decide

theorem t1_smul (c : ZMod 2) (a : K) : t1 (c • a) = c * t1 a := by revert c a; decide

theorem t0_coe_add_mul_omega (c d : ZMod 2) :
    t0 (algebraMap (ZMod 2) K c + algebraMap (ZMod 2) K d * ω) = c := by revert c d; decide

theorem t1_coe_add_mul_omega (c d : ZMod 2) :
    t1 (algebraMap (ZMod 2) K c + algebraMap (ZMod 2) K d * ω) = d := by revert c d; decide

theorem t0_coe (c : ZMod 2) : t0 (algebraMap (ZMod 2) K c) = c := by revert c; decide

noncomputable def adjoinRootEquiv :
    AdjoinRoot (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2)) ≃+* K :=
  haveI : Fact (Irreducible (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2))) :=
    ⟨irreducible_omega_poly⟩
  RingEquiv.ofBijective (AdjoinRoot.lift (algebraMap (ZMod 2) K) ω eval₂_omega_poly)
    ⟨RingHom.injective _, fun a => ⟨AdjoinRoot.of _ (t0 a) + AdjoinRoot.of _ (t1 a) *
      AdjoinRoot.root _, by
        rw [map_add, map_mul, AdjoinRoot.lift_of, AdjoinRoot.lift_of, AdjoinRoot.lift_root,
          t0_add_t1_omega]⟩⟩

theorem adjoinRootEquiv_root :
    adjoinRootEquiv (AdjoinRoot.root _) = ω :=
  AdjoinRoot.lift_root eval₂_omega_poly

theorem coe_t0_of_bar_eq (a : K) (h : bar a = a) : algebraMap (ZMod 2) K (t0 a) = a := by
  revert a; decide

theorem bar_coe (c : ZMod 2) : bar (algebraMap (ZMod 2) K c) = algebraMap (ZMod 2) K c := by
  revert c; decide

abbrev V : Type := Fin 4 → K

@[expose] def u (i : Fin 4) : V := Pi.single i 1

@[expose] def herm (v w : V) : K :=
  v 0 * bar (w 3) + v 1 * bar (w 2) + v 2 * bar (w 1) + v 3 * bar (w 0)

theorem herm_eq_sum (v w : V) : herm v w = ∑ i, v i * bar (w (Fin.rev i)) := by
  simp only [herm, Fin.sum_univ_four]
  rfl

theorem herm_add_left (v v' w : V) : herm (v + v') w = herm v w + herm v' w := by
  simp only [herm, Pi.add_apply]; ring

theorem herm_add_right (v w w' : V) : herm v (w + w') = herm v w + herm v w' := by
  simp only [herm, Pi.add_apply, bar_add]; ring

theorem herm_smul_left (c : K) (v w : V) : herm (c • v) w = c * herm v w := by
  simp only [herm, Pi.smul_apply, smul_eq_mul]; ring

theorem herm_smul_right (c : K) (v w : V) : herm v (c • w) = bar c * herm v w := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, bar_mul]; ring

theorem herm_zero_left (w : V) : herm 0 w = 0 := by simp [herm]

theorem herm_zero_right (v : V) : herm v 0 = 0 := by simp [herm, bar_zero]

theorem herm_swap (v w : V) : herm w v = bar (herm v w) := by
  simp only [herm, bar_add, bar_mul, bar_bar]; ring

@[expose] def IsTotallyIsotropic (U : Submodule K V) : Prop :=
  ∀ v ∈ U, ∀ w ∈ U, herm v w = 0

@[expose] def perp (U : Submodule K V) : Submodule K V where
  carrier := {v | ∀ x ∈ U, herm x v = 0}
  add_mem' {v w} hv hw x hx := by rw [herm_add_right, hv x hx, hw x hx, add_zero]
  zero_mem' x _ := herm_zero_right x
  smul_mem' c v hv x hx := by rw [herm_smul_right, hv x hx, mul_zero]

theorem mem_perp {U : Submodule K V} {v : V} : v ∈ perp U ↔ ∀ x ∈ U, herm x v = 0 :=
  Iff.rfl

abbrev W : Type := Fin 6 → K

@[expose] def wedge (v w : V) : W :=
  ![v 0 * w 1 - v 1 * w 0, v 0 * w 2 - v 2 * w 0, v 0 * w 3 - v 3 * w 0,
    v 1 * w 2 - v 2 * w 1, v 1 * w 3 - v 3 * w 1, v 2 * w 3 - v 3 * w 2]

@[expose] def b (p : Fin 6) : W := Pi.single p 1

@[expose] def T : W →+ W where
  toFun a := ![bar (a 0), bar (a 1), bar (a 3), bar (a 2), bar (a 4), bar (a 5)]
  map_zero' := by
    funext p
    fin_cases p <;> simp [bar_zero]
  map_add' a a' := by
    funext p
    fin_cases p <;> simp [bar_add]

theorem T_apply (a : W) :
    T a = ![bar (a 0), bar (a 1), bar (a 3), bar (a 2), bar (a 4), bar (a 5)] := rfl

theorem T_smul (c : K) (a : W) : T (c • a) = bar c • T a := by
  funext p
  fin_cases p <;> simp [T_apply, bar_mul]

theorem T_T (a : W) : T (T a) = a := by
  funext p
  fin_cases p <;> simp [T_apply, bar_bar]

theorem T_smul_zmod (c : ZMod 2) (a : W) : T (c • a) = c • T a := by
  rw [← algebraMap_smul K c a, T_smul, bar_coe, algebraMap_smul]

@[expose] def W₀ : Submodule (ZMod 2) W where
  carrier := {w | T w = w}
  add_mem' {a a'} ha ha' := by
    simp only [Set.mem_ofPred_eq] at ha ha' ⊢
    rw [map_add, ha, ha']
  zero_mem' := map_zero T
  smul_mem' c a ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [T_smul_zmod, ha]

theorem mem_W₀ {w : W} : w ∈ W₀ ↔ T w = w := Iff.rfl

@[expose] def Pf (a : W) : K := a 0 * a 5 + a 1 * a 4 + a 2 * a 3

@[expose] def psiLin : W →ₗ[ZMod 2] X where
  toFun w := ![t0 (w 0), t0 (w 1), t0 (w 5), t0 (w 4), t0 (w 3), t1 (w 3)]
  map_add' a a' := by
    funext i
    fin_cases i <;> simp [t0_add, t1_add]
  map_smul' c a := by
    funext i
    fin_cases i <;> simp [t0_smul, t1_smul]

theorem psiLin_apply (w : W) :
    psiLin w = ![t0 (w 0), t0 (w 1), t0 (w 5), t0 (w 4), t0 (w 3), t1 (w 3)] := rfl

@[expose] def param (x : X) : W :=
  let a := algebraMap (ZMod 2) K (x 4) + algebraMap (ZMod 2) K (x 5) * ω
  ![algebraMap (ZMod 2) K (x 0), algebraMap (ZMod 2) K (x 1), a ^ 2, a,
    algebraMap (ZMod 2) K (x 3), algebraMap (ZMod 2) K (x 2)]

theorem param_mem_W₀ (x : X) : param x ∈ W₀ := by
  have h4 : ∀ a : K, bar (a ^ 2) = a := by decide
  rw [mem_W₀]
  funext p
  fin_cases p <;> first | rfl | simp [T_apply, param, bar_coe, h4]

theorem psiLin_param (x : X) : psiLin (param x) = x := by
  funext i
  fin_cases i <;> simp [psiLin_apply, param, t0_coe, t0_coe_add_mul_omega, t1_coe_add_mul_omega]

theorem param_psiLin {w : W} (hw : w ∈ W₀) : param (psiLin w) = w := by
  rw [mem_W₀] at hw
  have hc : ∀ p : Fin 6, T w p = w p := fun p => congrFun hw p
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h4 := hc 4
  have h5 := hc 5
  simp only [T_apply, Matrix.cons_val] at h0 h1 h2 h4 h5
  funext p
  fin_cases p
  · exact coe_t0_of_bar_eq _ h0
  · exact coe_t0_of_bar_eq _ h1
  · simp only [param, psiLin_apply, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk]
    rw [t0_add_t1_omega, ← h2]
    rfl
  · simp only [param, psiLin_apply, Matrix.cons_val]
    exact t0_add_t1_omega _
  · exact coe_t0_of_bar_eq _ h4
  · exact coe_t0_of_bar_eq _ h5

@[expose] noncomputable def Ψ : W₀ ≃ₗ[ZMod 2] X where
  toFun w := psiLin w.1
  map_add' a a' := map_add psiLin a.1 a'.1
  map_smul' c a := map_smul psiLin c a.1
  invFun x := ⟨param x, param_mem_W₀ x⟩
  left_inv w := Subtype.ext (param_psiLin w.2)
  right_inv x := psiLin_param x

theorem Ψ_apply (w : W₀) : Ψ w = psiLin w.1 := rfl

theorem Ψ_param (x : X) : Ψ ⟨param x, param_mem_W₀ x⟩ = x := psiLin_param x

@[expose] def wedgeL (x : V) : V →ₗ[K] W where
  toFun := wedge x
  map_add' v w := by
    funext p
    fin_cases p <;> simp [wedge] <;> ring
  map_smul' c v := by
    funext p
    fin_cases p <;> simp [wedge] <;> ring

theorem wedgeL_apply (x v : V) : wedgeL x v = wedge x v := rfl

theorem wedge_smul_left (c : K) (x v : V) : wedge (c • x) v = c • wedge x v := by
  funext p
  fin_cases p <;> simp [wedge] <;> ring

theorem wedge_smul_right (c : K) (x v : V) : wedge x (c • v) = c • wedge x v :=
  (wedgeL x).map_smul c v

@[expose] def L (P : Submodule K V) : Submodule K W :=
  Submodule.span K {w | ∃ x ∈ P, ∃ v ∈ P, w = wedge x v}

@[expose] def M (ℓ : Submodule K V) : Submodule K W :=
  Submodule.span K {w | ∃ x ∈ ℓ, ∃ v ∈ perp ℓ, w = wedge x v}

theorem M_eq_map {ℓ : Submodule K V} {x : V} (hℓ : ℓ = K ∙ x) :
    M ℓ = (perp ℓ).map (wedgeL x) := by
  have hset : {w | ∃ y ∈ ℓ, ∃ v ∈ perp ℓ, w = wedge y v} =
      ((perp ℓ).map (wedgeL x) : Set W) := by
    ext w
    simp only [Set.mem_ofPred_eq, Submodule.map_coe, Set.mem_image, SetLike.mem_coe,
      wedgeL_apply]
    constructor
    · rintro ⟨y, hy, v, hv, rfl⟩
      rw [hℓ] at hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      exact ⟨c • v, (perp ℓ).smul_mem c hv, by rw [wedge_smul_left, wedge_smul_right]⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨x, hℓ ▸ Submodule.mem_span_singleton_self x, v, hv, rfl⟩
  rw [M, hset, Submodule.span_eq]

theorem coe_M {ℓ : Submodule K V} (hℓ : finrank K ℓ = 1) :
    (M ℓ : Set W) = {w | ∃ x ∈ ℓ, ∃ v ∈ perp ℓ, w = wedge x v} := by
  have hne : ℓ ≠ ⊥ := by
    rintro rfl
    simp at hℓ
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hℓx := eq_span_singleton_of_mem_of_finrank_eq_one hℓ hx hx0
  rw [M_eq_map hℓx]
  ext w
  simp only [Submodule.map_coe, Set.mem_image, SetLike.mem_coe, wedgeL_apply,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨x, hx, v, hv, rfl⟩
  · rintro ⟨y, hy, v, hv, rfl⟩
    rw [hℓx] at hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨c • v, (perp ℓ).smul_mem c hv, by rw [wedge_smul_left, wedge_smul_right]⟩

abbrev UVertex : Type :=
  {U : Submodule K V // IsTotallyIsotropic U ∧ (finrank K U = 1 ∨ finrank K U = 2)}

@[expose] def UVertex.Incident (x y : UVertex) : Prop :=
  x.1 ≤ y.1 ∨ y.1 ≤ x.1

@[expose] noncomputable def UVertex.type (x : UVertex) : ℕ :=
  finrank K x.1

end CFSG.LieType.Chevalley.C2E6Overlap
