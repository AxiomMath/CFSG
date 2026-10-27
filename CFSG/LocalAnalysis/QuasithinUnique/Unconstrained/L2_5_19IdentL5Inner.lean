module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabL5Basic
public import CFSG.GroupTheory.LocalCores.Components
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.QuasithinUnique.Id2519.Tab.L5

open Matrix
open scoped commutatorElement

theorem M5_add_self (A : M5) : A + A = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem zmod2_sq_eq_one {d : ZMod 2} (h : d * d = 1) : d = 1 := by
  revert d
  decide

theorem M5_ext_mulVec {A B : M5} (h : ∀ x : Fin 5 → ZMod 2, A *ᵥ x = B *ᵥ x) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

@[expose] def slOfSq (A : M5) (h : A * A = 1) : S :=
  ⟨A, by
    have h1 : A.det * A.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
    exact zmod2_sq_eq_one h1⟩

@[simp] theorem coe_slOfSq (A : M5) (h : A * A = 1) : ((slOfSq A h : S) : M5) = A := rfl

section UG

@[expose] def InUG (N u : M5) : Prop :=
  N * (u - 1) = 0 ∧ ∀ x : Fin 5 → ZMod 2, N *ᵥ x = 0 → (u - 1) *ᵥ x = 0

theorem InUG.sq {N u : M5} (h : InUG N u) : (u - 1) * (u - 1) = 0 := by
  apply M5_ext_mulVec
  intro x
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
  apply h.2
  rw [Matrix.mulVec_mulVec, h.1, Matrix.zero_mulVec]

theorem InUG.mul_self {N u : M5} (h : InUG N u) : u * u = 1 := by
  have h1 := h.sq
  have h3 : u * u - 1 = (u - 1) * (u - 1) + (u + u) - (1 + 1) := by noncomm_ring
  rw [h1, M5_add_self u, M5_add_self 1] at h3
  simp only [zero_add] at h3
  exact sub_eq_zero.mp h3

theorem InUG.one (N : M5) : InUG N 1 := by
  refine ⟨by simp, fun x _ => by simp⟩

theorem InUG.mul {N u v : M5} (hu : InUG N u) (hv : InUG N v) : InUG N (u * v) := by
  have h : u * v - 1 = (u - 1) * (v - 1) + (u - 1) + (v - 1) := by noncomm_ring
  refine ⟨?_, fun x hx => ?_⟩
  · rw [h, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, hu.1, hv.1]
    simp
  · rw [h, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv.2 x hx, hu.2 x hx]
    simp

@[expose] def UG (N : M5) : Subgroup S where
  carrier := {u | InUG N (u : M5)}
  mul_mem' := fun {a b} ha hb => by
    show InUG N ((a * b : S) : M5)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact InUG.mul ha hb
  one_mem' := by
    show InUG N ((1 : S) : M5)
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact InUG.one N
  inv_mem' := fun {a} ha => by
    have hsq : a * a = 1 := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
      exact InUG.mul_self ha)
    rw [inv_eq_of_mul_eq_one_right hsq]
    exact ha

theorem mem_UG {N : M5} {u : S} : u ∈ UG N ↔ InUG N (u : M5) := Iff.rfl

theorem UG_comm {N : M5} {u v : S} (hu : u ∈ UG N) (hv : v ∈ UG N) : u * v = v * u := by
  have hprod : ∀ {a b : S}, a ∈ UG N → b ∈ UG N → ((a : M5) - 1) * ((b : M5) - 1) = 0 := by
    intro a b ha hb
    apply M5_ext_mulVec
    intro x
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    apply (mem_UG.mp ha).2
    rw [Matrix.mulVec_mulVec, (mem_UG.mp hb).1, Matrix.zero_mulVec]
  have h1 := hprod hu hv
  have h2 := hprod hv hu
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have e1 : (u : M5) * v = (u - 1) * (v - 1) + (u - 1) + (v - 1) + 1 := by noncomm_ring
  have e2 : (v : M5) * u = (v - 1) * (u - 1) + (v - 1) + (u - 1) + 1 := by noncomm_ring
  rw [e1, e2, h1, h2]
  abel

end UG

section Involution

variable {y : S}

theorem one_add_sub_one (M : M5) : 1 + M - 1 = M := by abel

theorem N_sq (hy2 : (y : M5) * y = 1) : ((y : M5) - 1) * ((y : M5) - 1) = 0 := by
  have h : ((y : M5) - 1) * ((y : M5) - 1) = y * y - (y + y) + 1 := by noncomm_ring
  rw [h, hy2, M5_add_self (y : M5)]
  calc (1 : M5) - 0 + 1 = 1 + 1 := by abel
    _ = 0 := M5_add_self 1

theorem N_ne_zero (hy1 : y ≠ 1) : (y : M5) - 1 ≠ 0 := by
  intro h
  apply hy1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  exact sub_eq_zero.mp h

theorem UG_comm_y {u : S} (hu : u ∈ UG ((y : M5) - 1)) (hy2 : (y : M5) * y = 1) :
    y * u = u * y := by
  have hN := N_sq hy2
  have h1 : ((y : M5) - 1) * ((u : M5) - 1) = 0 := (mem_UG.mp hu).1
  have h2 : ((u : M5) - 1) * ((y : M5) - 1) = 0 := by
    apply M5_ext_mulVec
    intro z
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    apply (mem_UG.mp hu).2
    rw [Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have h3 : (y : M5) * u - u * y =
      ((y : M5) - 1) * ((u : M5) - 1) - ((u : M5) - 1) * ((y : M5) - 1) := by noncomm_ring
  rw [h1, h2] at h3
  exact sub_eq_zero.mp (h3.trans (sub_self (0 : M5)))

end Involution

theorem coe_mul_inv_self (g : S) : (g : M5) * ((g⁻¹ : S) : M5) = 1 := by
  have := congrArg (fun a : S => (a : M5)) (mul_inv_cancel g)
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using this

theorem coe_inv_mul_self (g : S) : ((g⁻¹ : S) : M5) * (g : M5) = 1 := by
  have := congrArg (fun a : S => (a : M5)) (inv_mul_cancel g)
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using this

theorem UG_conj_mem {N : M5} {g : S} (hgN : (g : M5) * N = N * (g : M5)) {u : S}
    (hu : u ∈ UG N) : g * u * g⁻¹ ∈ UG N := by
  have hgg := coe_mul_inv_self g
  have hgg' := coe_inv_mul_self g
  set gi : M5 := ((g⁻¹ : S) : M5) with hgi
  have hgiN : gi * N = N * gi := by
    calc gi * N = gi * N * ((g : M5) * gi) := by rw [hgg, Matrix.mul_one]
      _ = gi * (N * g) * gi := by simp only [Matrix.mul_assoc]
      _ = gi * (g * N) * gi := by rw [← hgN]
      _ = (gi * g) * N * gi := by simp only [Matrix.mul_assoc]
      _ = N * gi := by rw [hgg', Matrix.one_mul]
  have hM : ((g * u * g⁻¹ : S) : M5) - 1 = g * ((u : M5) - 1) * gi := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    calc (g : M5) * u * gi - 1 = g * u * gi - g * gi := by rw [hgg]
      _ = g * ((u : M5) - 1) * gi := by noncomm_ring
  refine ⟨?_, fun x hx => ?_⟩
  · show N * (((g * u * g⁻¹ : S) : M5) - 1) = 0
    rw [hM]
    calc N * (g * ((u : M5) - 1) * gi) = (N * g) * ((u : M5) - 1) * gi := by
          simp only [Matrix.mul_assoc]
      _ = g * (N * ((u : M5) - 1)) * gi := by rw [← hgN]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [(mem_UG.mp hu).1]; simp
  · show (((g * u * g⁻¹ : S) : M5) - 1) *ᵥ x = 0
    rw [hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hx' : N *ᵥ (gi *ᵥ x) = 0 := by
      rw [Matrix.mulVec_mulVec, ← hgiN, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    rw [(mem_UG.mp hu).2 _ hx']
    simp

theorem mulVec_eq_zero_of_coe_inv (g : S) {x : Fin 5 → ZMod 2} (h : (g : M5) *ᵥ x = 0) : x = 0 := by
  calc x = (1 : M5) *ᵥ x := (Matrix.one_mulVec x).symm
    _ = (((g⁻¹ : S) : M5) * (g : M5)) *ᵥ x := by rw [coe_inv_mul_self]
    _ = ((g⁻¹ : S) : M5) *ᵥ ((g : M5) *ᵥ x) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [h, Matrix.mulVec_zero]

theorem mem_UG_of_commute {N : M5} (hN0 : N ≠ 0) (hNN : N * N = 0) {g : S}
    (hg : ∀ u ∈ UG N, g * u = u * g) : g ∈ UG N := by
  have key : ∀ x w : Fin 5 → ZMod 2, N *ᵥ x = 0 →
      vecMulVec ((g : M5) *ᵥ x) (w ᵥ* N) = vecMulVec x ((w ᵥ* N) ᵥ* (g : M5)) := by
    intro x w hx
    have hr : (w ᵥ* N) ⬝ᵥ x = 0 := by
      rw [← Matrix.dotProduct_mulVec, hx, dotProduct_zero]
    have hMM : vecMulVec x (w ᵥ* N) * vecMulVec x (w ᵥ* N) = 0 := by
      rw [Matrix.vecMulVec_mul_vecMulVec, hr, zero_smul, Matrix.vecMulVec_zero]
    have hsq : (1 + vecMulVec x (w ᵥ* N)) * (1 + vecMulVec x (w ᵥ* N)) = 1 := by
      calc (1 + vecMulVec x (w ᵥ* N)) * (1 + vecMulVec x (w ᵥ* N))
          = 1 + (vecMulVec x (w ᵥ* N) + vecMulVec x (w ᵥ* N)) +
              vecMulVec x (w ᵥ* N) * vecMulVec x (w ᵥ* N) := by noncomm_ring
        _ = 1 := by rw [M5_add_self, hMM]; simp
    have hu : slOfSq _ hsq ∈ UG N := by
      refine ⟨?_, fun z hz => ?_⟩
      · show N * (1 + vecMulVec x (w ᵥ* N) - 1) = 0
        rw [one_add_sub_one, Matrix.mul_vecMulVec, hx, Matrix.zero_vecMulVec]
      · show (1 + vecMulVec x (w ᵥ* N) - 1) *ᵥ z = 0
        rw [one_add_sub_one, Matrix.vecMulVec_mulVec, ← Matrix.dotProduct_mulVec, hz,
          dotProduct_zero]
        simp
    have hcomm := congrArg (fun a : S => (a : M5)) (hg _ hu)
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_slOfSq] at hcomm
    have h1 : (g : M5) * vecMulVec x (w ᵥ* N) = vecMulVec x (w ᵥ* N) * g := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at hcomm
      exact add_left_cancel hcomm
    rwa [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul] at h1
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hN0 (by ext a b; exact h a b)
  have hij1 : N i j = 1 := (zmod2_cases (N i j)).resolve_left hij
  have ha1 : ∀ x, N *ᵥ x = 0 → (g : M5) *ᵥ x = x := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0, Matrix.mulVec_zero]
    obtain ⟨r, hr⟩ : ∃ r : Fin 5 → ZMod 2, r = (Pi.single i 1 : Fin 5 → ZMod 2) ᵥ* N :=
      ⟨_, rfl⟩
    have E := key x (Pi.single i 1) hx
    rw [← hr] at E
    have hrj : r j = 1 := by
      rw [hr, Matrix.single_one_vecMul]
      exact hij1
    have hgx : (g : M5) *ᵥ x = ((r ᵥ* (g : M5)) j) • x := by
      funext a
      have h := congrFun (congrFun E a) j
      rw [Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, hrj, mul_one] at h
      show ((g : M5) *ᵥ x) a = (r ᵥ* (g : M5)) j * x a
      rw [mul_comm]
      exact h
    rcases zmod2_cases ((r ᵥ* (g : M5)) j) with h0 | h1
    · exfalso
      rw [h0, zero_smul] at hgx
      exact hx0 (mulVec_eq_zero_of_coe_inv g hgx)
    · rw [h1, one_smul] at hgx
      exact hgx
  have hNg : N * (g : M5) = N := by
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Fin 5 → ZMod 2, x₀ = N *ᵥ (Pi.single j 1 : Fin 5 → ZMod 2) :=
      ⟨_, rfl⟩
    have hx₀N : N *ᵥ x₀ = 0 := by
      rw [hx₀, Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
    have hx₀i : x₀ i = 1 := by
      rw [hx₀, Matrix.mulVec_single_one]
      exact hij1
    ext a b
    have E := key x₀ (Pi.single a 1) hx₀N
    rw [ha1 x₀ hx₀N] at E
    have h := congrFun (congrFun E i) b
    rw [Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, hx₀i, one_mul, one_mul,
      Matrix.vecMul_vecMul, Matrix.single_one_vecMul, Matrix.single_one_vecMul] at h
    exact h.symm
  refine ⟨?_, fun x hx => ?_⟩
  · show N * ((g : M5) - 1) = 0
    rw [Matrix.mul_sub, hNg, Matrix.mul_one, sub_self]
  · show ((g : M5) - 1) *ᵥ x = 0
    rw [Matrix.sub_mulVec, ha1 x hx, Matrix.one_mulVec, sub_self]

theorem involution_centralizer_component_free {y : S} (hy : orderOf y = 2)
    (B : Subgroup ↥(Subgroup.centralizer ({y} : Set S))) : ¬ CFSG.IsComponent B := by
  intro hB
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy, pow_two] at h
    exact h
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    omega
  have hy2' : (y : M5) * y = 1 := by
    have := congrArg (fun a : S => (a : M5)) hy2
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using this
  have hNN : ((y : M5) - 1) * ((y : M5) - 1) = 0 := N_sq hy2'
  have hN0 : (y : M5) - 1 ≠ 0 := N_ne_zero hy1
  have hUC : UG ((y : M5) - 1) ≤ Subgroup.centralizer ({y} : Set S) := fun u hu => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (UG_comm_y hu hy2').symm
  have hUn : ((UG ((y : M5) - 1)).subgroupOf (Subgroup.centralizer ({y} : Set S))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUC]
    intro u c hu hc
    have h := congrArg (fun a : S => (a : M5)) (Subgroup.mem_centralizer_singleton_iff.mp hc)
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    have hcN : (c : M5) * ((y : M5) - 1) = ((y : M5) - 1) * (c : M5) := by
      calc (c : M5) * ((y : M5) - 1) = c * y - c := by noncomm_ring
        _ = y * c - c := by rw [h]
        _ = ((y : M5) - 1) * (c : M5) := by noncomm_ring
    exact UG_conj_mem hcN hu
  have hUs :
      Group.IsSolvable ((UG ((y : M5) - 1)).subgroupOf (Subgroup.centralizer ({y} : Set S))) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext (UG_comm a.2 b.2))
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hUs hUn.isSubnormal).1 B hB
  have hBU : ∀ b : ↥B, ((b : ↥(Subgroup.centralizer ({y} : Set S))) : S) ∈ UG ((y : M5) - 1) := by
    intro b
    apply mem_UG_of_commute hN0 hNN
    intro u hu
    have hmem : ⁅(b : ↥(Subgroup.centralizer ({y} : Set S))),
        (⟨u, hUC hu⟩ : ↥(Subgroup.centralizer ({y} : Set S)))⁆ ∈
        ⁅B, (UG ((y : M5) - 1)).subgroupOf (Subgroup.centralizer ({y} : Set S))⁆ :=
      Subgroup.commutator_mem_commutator b.2 (Subgroup.mem_subgroupOf.mpr hu)
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact congrArg Subtype.val hmem
  have hBsolv : Group.IsSolvable ↥B :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext (UG_comm (hBU a) (hBU b)))
  have : Nontrivial ↥B := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
  have : Group.IsPerfect ↥B := hB.1.1
  exact Group.IsPerfect.not_isSolvable ↥B hBsolv

end CFSG.QuasithinUnique.Id2519.Tab.L5
