module

public import CFSG.LieType.Universal.Spin.Chevalley.ShortRankOne
import TauCeti.LinearAlgebra.CliffordAlgebra.PBW

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ}

section General

variable (Q)

theorem ι_mul_list_prod_eq_zero {v : V} (hv : Q v = 0) :
    ∀ l : List V, (∀ w ∈ l, polar Q v w = 0) → v ∈ l → ι Q v * (l.map (ι Q)).prod = 0
  | [], _, h => absurd h List.not_mem_nil
  | w :: l, hl, h => by
    rw [List.map_cons, List.prod_cons, ← mul_assoc]
    rcases List.mem_cons.mp h with rfl | h
    · rw [ι_mul_ι_self_eq_zero Q hv, zero_mul]
    · rw [ι_mul_ι_eq_neg_of_polar_eq_zero Q (hl w List.mem_cons_self), neg_mul, mul_assoc,
        ι_mul_list_prod_eq_zero hv l (fun u hu => hl u (List.mem_cons_of_mem w hu)) h, mul_zero,
        neg_zero]

@[expose] def stabSubgroup (ω : CliffordAlgebra Q) : Subgroup (spinGroup Q) where
  carrier := {x | (x : CliffordAlgebra Q) * ω = ω}
  mul_mem' {x y} hx hy := by
    change (x : CliffordAlgebra Q) * ω = ω at hx
    change (y : CliffordAlgebra Q) * ω = ω at hy
    change ((x * y : spinGroup Q) : CliffordAlgebra Q) * ω = ω
    rw [Submonoid.coe_mul, mul_assoc, hy, hx]
  one_mem' := by
    change ((1 : spinGroup Q) : CliffordAlgebra Q) * ω = ω
    rw [Submonoid.coe_one, one_mul]
  inv_mem' {x} hx := by
    change (x : CliffordAlgebra Q) * ω = ω at hx
    change ((x⁻¹ : spinGroup Q) : CliffordAlgebra Q) * ω = ω
    calc ((x⁻¹ : spinGroup Q) : CliffordAlgebra Q) * ω =
        ((x⁻¹ : spinGroup Q) : CliffordAlgebra Q) * ((x : CliffordAlgebra Q) * ω) := by rw [hx]
      _ = ω := coe_inv_mul_coe_mul Q x ω

theorem mem_stabSubgroup {ω : CliffordAlgebra Q} {x : spinGroup Q} :
    x ∈ stabSubgroup Q ω ↔ (x : CliffordAlgebra Q) * ω = ω :=
  Iff.rfl

theorem eq_one_of_mul_eq_self {g : spinGroup Q}
    (hg : (g : CliffordAlgebra Q) = 1 ∨ (g : CliffordAlgebra Q) = -1) {ω : CliffordAlgebra Q}
    (hω : ω ≠ 0) (h : (g : CliffordAlgebra Q) * ω = ω) : g = 1 := by
  apply Subtype.ext
  change (g : CliffordAlgebra Q) = 1
  rcases hg with hg | hg
  · exact hg
  · rw [hg]
    by_cases h2 : (2 : K) = 0
    · have h2' : (1 : CliffordAlgebra Q) + 1 = 0 := by
        rw [one_add_one_eq_two, ← map_ofNat (algebraMap K (CliffordAlgebra Q)) 2, h2, map_zero]
      exact (eq_neg_of_add_eq_zero_left h2').symm
    · exfalso
      rw [hg, neg_one_mul] at h
      have h' : (2 : K) • ω = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← h]
        exact neg_add_cancel ω
      exact hω ((smul_eq_zero.mp h').resolve_left h2)

end General

namespace HypFrame

variable (F : HypFrame Q n)

noncomputable def spinor (τ : Fin n → Bool) : CliffordAlgebra Q :=
  ((List.ofFn fun m => F.vec m (τ m)).map (ι Q)).prod

theorem spinor_ne_zero (τ : Fin n → Bool) : F.spinor τ ≠ 0 := by
  rw [spinor, List.map_ofFn]
  exact prod_map_ι_ofFn_ne_zero Q _ (F.linearIndependent_vec τ)

theorem ι_vec_mul_spinor (τ : Fin n → Bool) (m : Fin n) :
    ι Q (F.vec m (τ m)) * F.spinor τ = 0 := by
  refine ι_mul_list_prod_eq_zero Q (F.map_vec m (τ m)) _ ?_ (List.mem_ofFn.mpr ⟨m, rfl⟩)
  intro w hw
  obtain ⟨m', rfl⟩ := List.mem_ofFn.mp hw
  by_cases h : m = m'
  · subst h
    exact F.polar_vec_self m (τ m)
  · exact F.polar_vec_of_ne h _ _

theorem numOp_mul_spinor_of_ne (τ : Fin n → Bool) {m : Fin n} {r : Bool} (h : r ≠ τ m) :
    F.numOp m r * F.spinor τ = 0 := by
  have hr : (!r) = τ m := by
    cases r <;> cases h' : τ m <;> simp_all
  rw [numOp, mul_assoc, hr, F.ι_vec_mul_spinor, mul_zero]

theorem numOp_mul_spinor_of_eq (τ : Fin n → Bool) {m : Fin n} {r : Bool} (h : r = τ m) :
    F.numOp m r * F.spinor τ = F.spinor τ := by
  have h1 : F.numOp m r + F.numOp m (!r) = 1 := by
    simpa only [numOp, Bool.not_not] using F.ι_vec_mul_ι_vec_not_add m r
  have h2 : F.numOp m (!r) * F.spinor τ = 0 :=
    F.numOp_mul_spinor_of_ne τ (by rw [h]; cases τ m <;> simp)
  calc F.numOp m r * F.spinor τ = (F.numOp m r + F.numOp m (!r)) * F.spinor τ := by
        rw [add_mul, h2, add_zero]
    _ = F.spinor τ := by rw [h1, one_mul]

theorem coe_longTorus_mul_spinor_of_eq (τ : Fin n → Bool) {i j : Fin n} (hij : i ≠ j)
    {s t : Bool} (hs : s = τ i) (ht : t = τ j) (c : Kˣ) :
    (F.longTorus hij s t c : CliffordAlgebra Q) * F.spinor τ = (c : K) • F.spinor τ := by
  rw [coe_longTorus, SL2Pair.toFun_diagSL2, longPair_X_mul_Y, longPair_Y_mul_X]
  have e1 : F.numOp j t * F.numOp i s * F.spinor τ = F.spinor τ := by
    rw [mul_assoc, F.numOp_mul_spinor_of_eq τ hs, F.numOp_mul_spinor_of_eq τ ht]
  have e2 : F.numOp i (!s) * F.numOp j (!t) * F.spinor τ = 0 := by
    rw [mul_assoc, F.numOp_mul_spinor_of_ne τ (r := !t) (by rw [ht]; cases τ j <;> simp),
      mul_zero]
  simp only [add_mul, sub_mul, smul_mul_assoc, one_mul, e1, e2, smul_zero, add_zero, sub_self]

theorem coe_longTorus_mul_spinor_of_ne (τ : Fin n → Bool) {i j : Fin n} (hij : i ≠ j)
    {s t : Bool} (h : (s = τ i ∧ t ≠ τ j) ∨ (s ≠ τ i ∧ t = τ j)) (c : Kˣ) :
    (F.longTorus hij s t c : CliffordAlgebra Q) * F.spinor τ = F.spinor τ := by
  rw [coe_longTorus, SL2Pair.toFun_diagSL2, longPair_X_mul_Y, longPair_Y_mul_X]
  have hnot : ∀ {a b : Bool}, a ≠ b → (!a) = b := fun {a b} hab => by
    cases a <;> cases b <;> simp_all
  have hnot' : ∀ {a b : Bool}, a = b → (!a) ≠ b := fun {a b} hab => by
    cases a <;> cases b <;> simp_all
  have e : F.numOp j t * F.numOp i s * F.spinor τ = 0 ∧
      F.numOp i (!s) * F.numOp j (!t) * F.spinor τ = 0 := by
    rcases h with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · refine ⟨?_, ?_⟩
      · rw [mul_assoc, F.numOp_mul_spinor_of_eq τ hs, F.numOp_mul_spinor_of_ne τ ht]
      · rw [mul_assoc, F.numOp_mul_spinor_of_eq τ (hnot ht), F.numOp_mul_spinor_of_ne τ (hnot' hs)]
    · refine ⟨?_, ?_⟩
      · rw [mul_assoc, F.numOp_mul_spinor_of_ne τ hs, mul_zero]
      · rw [mul_assoc, F.numOp_mul_spinor_of_ne τ (hnot' ht), mul_zero]
  simp only [add_mul, sub_mul, smul_mul_assoc, one_mul, e.1, e.2, smul_zero, add_zero, sub_zero,
    zero_add]

theorem coe_longRoot_mul_spinor (τ : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) {s t : Bool}
    (h : s = τ i ∨ t = τ j) (c : K) :
    (F.longRoot hij s t (.ofAdd c) : CliffordAlgebra Q) * F.spinor τ = F.spinor τ := by
  rw [coe_longRoot, add_mul, one_mul, smul_mul_assoc]
  suffices ι Q (F.vec i s) * ι Q (F.vec j t) * F.spinor τ = 0 by rw [this, smul_zero, add_zero]
  rcases h with rfl | rfl
  · rw [F.ι_vec_mul_ι_vec_of_ne hij, neg_mul, mul_assoc, F.ι_vec_mul_spinor, mul_zero, neg_zero]
  · rw [mul_assoc, F.ι_vec_mul_spinor, mul_zero]

end HypFrame

namespace OddFrame

variable (F : OddFrame Q n)

theorem coe_shortTorus_mul_spinor (τ : Fin n → Bool) {i : Fin n} {s : Bool} (hs : s = τ i)
    (c : Kˣ) :
    (F.shortTorus i s c : CliffordAlgebra Q) * F.spinor τ = (c : K) • F.spinor τ := by
  rw [coe_shortTorus, SL2Pair.toFun_diagSL2, shortPair_X_mul_Y, shortPair_Y_mul_X]
  have e1 : F.numOp i s * F.spinor τ = F.spinor τ := F.numOp_mul_spinor_of_eq τ hs
  have e2 : F.numOp i (!s) * F.spinor τ = 0 :=
    F.numOp_mul_spinor_of_ne τ (by rw [hs]; cases τ i <;> simp)
  simp only [add_mul, sub_mul, smul_mul_assoc, one_mul, e1, e2, smul_zero, add_zero, sub_self]

theorem coe_shortRoot_mul_spinor (τ : Fin n → Bool) {i : Fin n} {s : Bool} (hs : s = τ i)
    (c : K) :
    (F.shortRoot i s (.ofAdd c) : CliffordAlgebra Q) * F.spinor τ = F.spinor τ := by
  rw [coe_shortRoot, add_mul, one_mul, smul_mul_assoc, mul_assoc, hs, F.ι_vec_mul_spinor,
    mul_zero, smul_zero, add_zero]

end OddFrame

end CFSG.LieType.Universal.Spin
