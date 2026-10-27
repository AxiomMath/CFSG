module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeFullCosetMiddleSubgroup

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix
open scoped commutatorElement Pointwise

section SymThreeCentralizerAlgebra

@[expose] def symThreeUnit : binarySymMatrices 3 :=
  ⟨vecMulVec ![1, 0, 0] ![1, 0, 0], MatrixExtension.vecMulVec_self_mem_binarySymMatrices _⟩

@[expose] def symThreeSquare (ε : ZMod 2) (w : Fin 3 → ZMod 2) : binarySymMatrices 3 :=
  ⟨ε • vecMulVec w w,
    symThree_smul_mem ε (MatrixExtension.vecMulVec_self_mem_binarySymMatrices w)⟩

@[expose] def symThreeSquarePolar (ε : ZMod 2) (w v : Fin 3 → ZMod 2) : binarySymMatrices 3 :=
  ⟨ε • symThreePolar w v, symThree_smul_mem ε (symThreePolar_mem w v)⟩

theorem coe_symThreeSquare (ε : ZMod 2) (w : Fin 3 → ZMod 2) :
    (symThreeSquare ε w : Matrix (Fin 3) (Fin 3) (ZMod 2)) = ε • vecMulVec w w :=
  rfl

theorem coe_symThreeSquarePolar (ε : ZMod 2) (w v : Fin 3 → ZMod 2) :
    (symThreeSquarePolar ε w v : Matrix (Fin 3) (Fin 3) (ZMod 2)) = ε • symThreePolar w v :=
  rfl

theorem symThreeSquare_zero_right (ε : ZMod 2) : symThreeSquare ε 0 = 0 := by
  apply Subtype.ext
  simp [coe_symThreeSquare]

theorem symThreeSquare_zero_left (w : Fin 3 → ZMod 2) : symThreeSquare 0 w = 0 := by
  apply Subtype.ext
  simp [coe_symThreeSquare]

theorem symThreeSquare_add (ε : ZMod 2) (w v : Fin 3 → ZMod 2) :
    symThreeSquare ε w + symThreeSquare ε v + symThreeSquare ε (w + v) =
      symThreeSquarePolar ε w v := by
  apply Subtype.ext
  ext i j
  simp only [AddSubgroup.coe_add, coe_symThreeSquare, coe_symThreeSquarePolar, symThreePolar,
    Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.add_apply, smul_eq_mul]
  grind

theorem symThreeDiag_vecMulVec_self (w : Fin 3 → ZMod 2) : symThreeDiag (vecMulVec w w) = w := by
  funext k
  exact symThree_zmod_mul_self (w k)

theorem vecMulVec_self_eq_zero_iff (w : Fin 3 → ZMod 2) : vecMulVec w w = 0 ↔ w = 0 := by
  revert w
  decide

theorem symThreeDiag_polar_ne : ∀ w : Fin 3 → ZMod 2, w ≠ 0 →
    ∃ v : Fin 3 → ZMod 2, symThreePolar w v ≠ 0 := by
  decide

@[expose] def symThreeStab : Fin 4 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 0, 0; 0, 1, 0; 0, 1, 1],
    !![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 1; 0, 1, 0; 0, 0, 1]]

theorem symThreeStab_mul_self : ∀ i, symThreeStab i * symThreeStab i = 1 := by
  decide

@[expose] def symThreeStabGL (i : Fin 4) : GL (Fin 3) (ZMod 2) :=
  ⟨symThreeStab i, symThreeStab i, symThreeStab_mul_self i, symThreeStab_mul_self i⟩

theorem symThreeStabGL_mul_self (i : Fin 4) : symThreeStabGL i * symThreeStabGL i = 1 :=
  Units.ext (symThreeStab_mul_self i)

theorem symThreeStab_unit : ∀ i, symThreeStab i * vecMulVec ![1, 0, 0] ![1, 0, 0] *
    (symThreeStab i)ᵀ = vecMulVec ![1, 0, 0] ![1, 0, 0] := by
  decide

theorem symThreeStab_alt : ∀ i, ∀ t : Fin 3 → ZMod 2, t 0 = 0 →
    (symThreeStab i * symThreeAlt t * (symThreeStab i)ᵀ) 1 2 = 0 := by
  decide

theorem symThreeStab_alt_one : ∀ i,
    (symThreeStab i * symThreeAlt ![1, 0, 0] * (symThreeStab i)ᵀ) 1 2 = 1 := by
  decide

theorem symThreeStab_fixed : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), Bᵀ = B →
    (∀ i, symThreeStab i * B * (symThreeStab i)ᵀ = B) →
      B = 0 ∨ B = vecMulVec ![1, 0, 0] ![1, 0, 0] := by
  decide +kernel

@[expose] def symThreeSwap : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def symThreeShear : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, 0, 0; 1, 1, 0; 0, 0, 1]

theorem symThreeSwap_mul_self : symThreeSwap * symThreeSwap = 1 := by
  decide

theorem symThreeShear_mul_self : symThreeShear * symThreeShear = 1 := by
  decide

@[expose] def symThreeSwapGL : GL (Fin 3) (ZMod 2) :=
  ⟨symThreeSwap, symThreeSwap, symThreeSwap_mul_self, symThreeSwap_mul_self⟩

@[expose] def symThreeShearGL : GL (Fin 3) (ZMod 2) :=
  ⟨symThreeShear, symThreeShear, symThreeShear_mul_self, symThreeShear_mul_self⟩

theorem symThreeSwapGL_mul_self : symThreeSwapGL * symThreeSwapGL = 1 :=
  Units.ext symThreeSwap_mul_self

theorem symThreeShearGL_mul_self : symThreeShearGL * symThreeShearGL = 1 :=
  Units.ext symThreeShear_mul_self

theorem symThree_swap_shear_values :
    (symThreeAlt ![0, 0, 1]) 1 2 = 0 ∧
    (symThreeSwap * symThreeAlt ![0, 0, 1] * symThreeSwapᵀ) 1 2 = 0 ∧
    (symThreeShear * symThreeAlt ![0, 0, 1] * symThreeShearᵀ) 1 2 = 0 ∧
    (symThreeAlt ![1, 0, 0]) 1 2 = 1 ∧
    (symThreeSwap * symThreeAlt ![1, 0, 0] * symThreeSwapᵀ) 1 2 = 0 ∧
    (symThreeShear * symThreeAlt ![1, 0, 0] * symThreeShearᵀ) 1 2 = 1 ∧
    vecMulVec ![1, 0, 0] ![1, 0, 0] +
        symThreeSwap * vecMulVec ![1, 0, 0] ![1, 0, 0] * symThreeSwapᵀ +
        symThreeShear * vecMulVec ![1, 0, 0] ![1, 0, 0] * symThreeShearᵀ =
      symThreeAlt ![0, 0, 1] ∧
    vecMulVec ![1, 0, 0] ![1, 0, 0] +
        symThreeShear * vecMulVec ![1, 0, 0] ![1, 0, 0] * symThreeShearᵀ ≠ 0 := by
  decide

@[expose] def symThreeOrbit (k : ℕ) : Fin 3 → ZMod 2 :=
  (symThreeSingerMatrix *ᵥ ·)^[k] ![1, 0, 0]

theorem symThreeOrbit_succ (k : ℕ) :
    symThreeOrbit (k + 1) = symThreeSingerMatrix *ᵥ symThreeOrbit k :=
  Function.iterate_succ_apply' _ _ _

theorem symThreeOrbit_surj : ∀ w : Fin 3 → ZMod 2, w ≠ 0 → ∃ k : Fin 7, symThreeOrbit k = w := by
  decide

theorem symThreeOrbit_span : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), Bᵀ = B →
    ∃ b : Fin 7 → Bool, B = ∑ k : Fin 7,
      if b k then vecMulVec (symThreeOrbit k) (symThreeOrbit k) else 0 := by
  decide +kernel

theorem symThreeAlt_eq_polar : ∀ t : Fin 3 → ZMod 2, symThreeAlt t =
    (if t 0 = 1 then symThreePolar ![0, 1, 0] ![0, 0, 1] else 0) +
      (if t 1 = 1 then symThreePolar ![1, 0, 0] ![0, 0, 1] else 0) +
      (if t 2 = 1 then symThreePolar ![1, 0, 0] ![0, 1, 0] else 0) := by
  decide

theorem symThree_J₀_avoid : ∀ s : Fin 3 → ZMod 2,
    ∃ t : Fin 3 → ZMod 2, t 0 = 0 ∧ t ≠ 0 ∧ t ≠ s := by
  decide

theorem card_symThreeJ :
    Nat.card {B : binarySymMatrices 3 | (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1 = 0 ∧
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 0 ∧
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2 = 0} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem symThreeCongr_iterate_singer_unit (k : ℕ) :
    ((symThreeCongr symThreeSinger)^[k] symThreeUnit : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      vecMulVec (symThreeOrbit k) (symThreeOrbit k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', coe_symThreeCongr, ih, symThreeOrbit_succ]
    exact MatrixExtension.mul_vecMulVec_mul_transpose _ _ _

theorem symThreeCongr_iterate_singer_zero (k : ℕ) :
    (symThreeCongr symThreeSinger)^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, symThreeCongr_zero]

end SymThreeCentralizerAlgebra

theorem symThree_commute_iff {G : Type*} [Group G] {x y : G} : x * y = y * x ↔ ⁅x, y⁆ = 1 :=
  commutatorElement_eq_one_iff_commute.symm

theorem symThree_zpow_of_sq_eq_one {G : Type*} [Group G] {z : G} (hz : z ^ 2 = 1) (k : ℤ) :
    z ^ k = 1 ∨ z ^ k = z := by
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, hz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.mul_ediv_add_emod k 2, h, add_zero, _root_.zpow_mul, h2, _root_.one_zpow]
  · right
    rw [← Int.mul_ediv_add_emod k 2, h, _root_.zpow_add, _root_.zpow_mul, h2, _root_.one_zpow,
      one_mul, zpow_one]

structure SymThreeCentralizerData (D : Type*) [Group D] where
  A : Subgroup D
  central : A ≤ Subgroup.center D
  a : A ≃* Multiplicative (binarySymMatrices 3)
  z : D
  z_sq : z ^ 2 = 1
  z_not_mem : z ∉ A
  sq_mem : ∀ d : D, d ^ 2 ∈ A
  ν : D → binarySymMatrices 3
  ν_spec : ∀ d, (a.symm (.ofAdd (ν d)) : D) = z⁻¹ * d⁻¹ * z * d
  ν_surj : Function.Surjective ν
  ν_ker : ∀ d, ν d = 0 ↔ d ∈ A ⊔ Subgroup.zpowers z
  ρ : GL (Fin 3) (ZMod 2) →* MulAut D
  ρ_z : ∀ g, ρ g z = z
  ρ_a : ∀ g B, ρ g (a.symm (.ofAdd B) : D) = a.symm (.ofAdd (symThreeCongr g B))
  E : Subgroup D
  E_F : ∀ e ∈ E, symThreeDiag (ν e) = 0
  E_ρ : ∀ g, ∀ e ∈ E, ρ g e ∈ E
  E_comm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e
  E_sq : ∀ e ∈ E, e ^ 2 = 1
  E_R : E ⊓ (A ⊔ Subgroup.zpowers z) = A
  F_E : ∀ d, symThreeDiag (ν d) = 0 → d ∈ E ∨ z⁻¹ * d ∈ E
  P : Subgroup D
  P_comm : ∀ p ∈ P, ∀ p' ∈ P, p * p' = p' * p
  A_P : A ≤ P
  P_R : P ⊓ (A ⊔ Subgroup.zpowers z) = A
  P_J : ∀ B : binarySymMatrices 3, ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1 = 0 ∧
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 0 ∧ (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2 = 0) ↔
      ∃ p ∈ P, ν p = B

namespace SymThreeCentralizerData

variable {D : Type*} [Group D] (S : SymThreeCentralizerData D)

@[expose] def aE (B : binarySymMatrices 3) : D := S.a.symm (.ofAdd B)

theorem aE_mem (B : binarySymMatrices 3) : S.aE B ∈ S.A :=
  (S.a.symm _).2

theorem aE_mul (B B' : binarySymMatrices 3) : S.aE B * S.aE B' = S.aE (B + B') := by
  rw [aE, aE, aE, ← Subgroup.coe_mul, ← map_mul, ← ofAdd_add]

theorem aE_injective {B B' : binarySymMatrices 3} (h : S.aE B = S.aE B') : B = B' :=
  Multiplicative.ofAdd.injective (S.a.symm.injective (Subtype.ext h))

theorem aE_zero : S.aE 0 = 1 := by
  rw [aE, ofAdd_zero, map_one, Subgroup.coe_one]

theorem aE_eq_one {B : binarySymMatrices 3} : S.aE B = 1 ↔ B = 0 :=
  ⟨fun h => S.aE_injective (h.trans S.aE_zero.symm), by
    rintro rfl
    exact S.aE_zero⟩

theorem exists_aE {x : D} (hx : x ∈ S.A) : ∃ B, x = S.aE B :=
  ⟨Multiplicative.toAdd (S.a ⟨x, hx⟩), by rw [aE, ofAdd_toAdd, MulEquiv.symm_apply_apply]⟩

theorem aE_ν (d : D) : S.aE (S.ν d) = S.z⁻¹ * d⁻¹ * S.z * d :=
  S.ν_spec d

theorem commute_of_mem_A {x : D} (hx : x ∈ S.A) (y : D) : x * y = y * x :=
  ((Subgroup.mem_center_iff.1 (S.central hx)) y).symm

theorem aE_mul_self (B : binarySymMatrices 3) : S.aE B * S.aE B = 1 := by
  rw [aE_mul, symThree_add_self, aE_zero]

theorem sq_eq_one_of_mem_A {x : D} (hx : x ∈ S.A) : x ^ 2 = 1 := by
  obtain ⟨B, rfl⟩ := S.exists_aE hx
  rw [sq, aE_mul_self]

theorem inv_eq_of_mem_A {x : D} (hx : x ∈ S.A) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact S.sq_eq_one_of_mem_A hx)

theorem A_normal : S.A.Normal :=
  ⟨fun n hn g => by
    rw [← S.commute_of_mem_A hn g, mul_inv_cancel_right]
    exact hn⟩

@[expose] def R : Subgroup D :=
  S.A ⊔ Subgroup.zpowers S.z

theorem A_le_R : S.A ≤ S.R :=
  le_sup_left

theorem z_mem_R : S.z ∈ S.R :=
  le_sup_right (a := S.A) (Subgroup.mem_zpowers S.z)

theorem zpow_z (k : ℤ) : S.z ^ k = 1 ∨ S.z ^ k = S.z :=
  symThree_zpow_of_sq_eq_one S.z_sq k

theorem mem_R_iff {x : D} : x ∈ S.R ↔ x ∈ S.A ∨ S.z⁻¹ * x ∈ S.A := by
  constructor
  · intro hx
    have := S.A_normal
    obtain ⟨y, hy, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    rcases S.zpow_z k with h | h
    · left
      rw [h, mul_one]
      exact hy
    · right
      rw [h, S.commute_of_mem_A hy, inv_mul_cancel_left]
      exact hy
  · rintro (h | h)
    · exact S.A_le_R h
    · have := mul_mem S.z_mem_R (S.A_le_R h)
      rwa [mul_inv_cancel_left] at this

theorem mem_A_of_commute {x : D} (hx : x ∈ S.R) (h : x ∉ S.A) : S.z⁻¹ * x ∈ S.A :=
  (S.mem_R_iff.1 hx).resolve_left h

theorem ν_mul (d d' : D) : S.ν (d * d') = S.ν d + S.ν d' := by
  apply S.aE_injective
  have hc : d'⁻¹ * S.aE (S.ν d) * d' = S.aE (S.ν d) := by
    rw [mul_assoc, S.commute_of_mem_A (S.aE_mem _) d', inv_mul_cancel_left]
  have h : S.z⁻¹ * (d * d')⁻¹ * S.z * (d * d') =
      (S.z⁻¹ * d'⁻¹ * S.z * d') * (d'⁻¹ * (S.z⁻¹ * d⁻¹ * S.z * d) * d') := by
    group
  rw [S.aE_ν, h, ← S.aE_ν, ← S.aE_ν, hc, aE_mul, add_comm]

theorem ν_one : S.ν 1 = 0 :=
  (S.ν_ker 1).2 (one_mem _)

theorem ν_of_mem_R {x : D} (hx : x ∈ S.R) : S.ν x = 0 :=
  (S.ν_ker x).2 hx

theorem mem_R_of_ν_eq_zero {x : D} (hx : S.ν x = 0) : x ∈ S.R :=
  (S.ν_ker x).1 hx

theorem ν_inv (d : D) : S.ν d⁻¹ = S.ν d := by
  have h := S.ν_mul d d⁻¹
  rw [mul_inv_cancel, ν_one] at h
  exact (symThree_eq_of_add_eq_zero h.symm).symm

theorem ν_z : S.ν S.z = 0 :=
  S.ν_of_mem_R S.z_mem_R

theorem ν_eq_iff (x y : D) : S.ν x = S.ν y ↔ x⁻¹ * y ∈ S.R := by
  have h : S.ν (x⁻¹ * y) = S.ν x + S.ν y := by rw [S.ν_mul, ν_inv]
  constructor
  · intro hxy
    apply S.mem_R_of_ν_eq_zero
    rw [h, hxy, symThree_add_self]
  · intro hR
    exact symThree_eq_of_add_eq_zero (h ▸ S.ν_of_mem_R hR)

theorem ν_eq_iff' (x y : D) : S.ν x = S.ν y ↔ y * x⁻¹ ∈ S.R := by
  have h : S.ν (y * x⁻¹) = S.ν x + S.ν y := by rw [S.ν_mul, ν_inv, add_comm]
  constructor
  · intro hxy
    apply S.mem_R_of_ν_eq_zero
    rw [h, hxy, symThree_add_self]
  · intro hR
    exact symThree_eq_of_add_eq_zero (h ▸ S.ν_of_mem_R hR)

@[expose] def νHom : D →* Multiplicative (binarySymMatrices 3) where
  toFun d := .ofAdd (S.ν d)
  map_one' := by
    rw [ν_one]
    rfl
  map_mul' d d' := by
    rw [S.ν_mul, ofAdd_add]

theorem ρ_aE (g : GL (Fin 3) (ZMod 2)) (B : binarySymMatrices 3) :
    S.ρ g (S.aE B) = S.aE (symThreeCongr g B) :=
  S.ρ_a g B

theorem ν_ρ (g : GL (Fin 3) (ZMod 2)) (d : D) : S.ν (S.ρ g d) = symThreeCongr g (S.ν d) := by
  apply S.aE_injective
  rw [S.aE_ν, ← S.ρ_aE, S.aE_ν, map_mul, map_mul, map_mul, map_inv, map_inv, S.ρ_z]

theorem ρ_ρ_of_mul_self {g : GL (Fin 3) (ZMod 2)} (hg : g * g = 1) (x : D) :
    S.ρ g (S.ρ g x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, hg, map_one, MulAut.one_apply]

theorem commutatorElement_mem_A (x y : D) : ⁅x, y⁆ ∈ S.A := by
  rw [symThree_commutatorElement_eq_sq]
  exact mul_mem (mul_mem (S.sq_mem _) (S.sq_mem _)) (S.sq_mem _)

include S in
theorem commutatorElement_mul_right (x y w : D) : ⁅x, y * w⁆ = ⁅x, y⁆ * ⁅x, w⁆ := by
  have h : ⁅x, y * w⁆ = ⁅x, y⁆ * (y * ⁅x, w⁆ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [h, ← S.commute_of_mem_A (S.commutatorElement_mem_A x w) y, mul_inv_cancel_right]

include S in
theorem commutatorElement_comm (x y : D) : ⁅y, x⁆ = ⁅x, y⁆ := by
  rw [← commutatorElement_inv, S.inv_eq_of_mem_A (S.commutatorElement_mem_A x y)]

include S in
theorem commutatorElement_mul_left (x y w : D) : ⁅x * y, w⁆ = ⁅x, w⁆ * ⁅y, w⁆ := by
  rw [S.commutatorElement_comm, S.commutatorElement_mul_right, S.commutatorElement_comm w x,
    S.commutatorElement_comm w y]

include S in
theorem commutatorElement_inv_right' (x y : D) : ⁅x, y⁻¹⁆ = ⁅x, y⁆ := by
  have h := S.commutatorElement_mul_right x y⁻¹ y
  rw [inv_mul_cancel, commutatorElement_one_right] at h
  rw [eq_inv_of_mul_eq_one_left h.symm, S.inv_eq_of_mem_A (S.commutatorElement_mem_A x y)]

include S in
theorem conj_commutator (x y : D) : x⁻¹ * y⁻¹ * x * y = ⁅x, y⁆ := by
  have h1 : x⁻¹ * y⁻¹ * x * y = ⁅x⁻¹, y⁻¹⁆ := by
    rw [commutatorElement_def, inv_inv, inv_inv]
  rw [h1, S.commutatorElement_inv_right', S.commutatorElement_comm, S.commutatorElement_inv_right',
    S.commutatorElement_comm]

theorem commutatorElement_z (d : D) : ⁅S.z, d⁆ = S.aE (S.ν d) := by
  rw [S.aE_ν, S.conj_commutator]

theorem commutatorElement_eq_one_of_mem_A {x a : D} (ha : a ∈ S.A) : ⁅x, a⁆ = 1 :=
  commutatorElement_eq_one_iff_commute.2 (S.commute_of_mem_A ha x).symm

theorem ν_eq_zero_of_commute_z {d : D} (h : S.z * d = d * S.z) : S.ν d = 0 := by
  rw [← S.aE_eq_one, ← commutatorElement_z, commutatorElement_eq_one_iff_commute]
  exact h

theorem commutatorElement_eq_one_of_mem_A_left {a x : D} (ha : a ∈ S.A) : ⁅a, x⁆ = 1 :=
  commutatorElement_eq_one_iff_commute.2 (S.commute_of_mem_A ha x)

theorem ρ_ρ_inv (g : GL (Fin 3) (ZMod 2)) (x : D) : S.ρ g (S.ρ g⁻¹ x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem A_le_E : S.A ≤ S.E :=
  S.E_R.symm.le.trans inf_le_left

theorem mem_A_of_mem_E_R {x : D} (hx : x ∈ S.E) (hxR : x ∈ S.R) : x ∈ S.A := by
  rw [← S.E_R]
  exact Subgroup.mem_inf.2 ⟨hx, hxR⟩

theorem exists_mem_E (C : binarySymMatrices 3) (hC : symThreeDiag C = 0) :
    ∃ e ∈ S.E, S.ν e = C := by
  obtain ⟨d, rfl⟩ := S.ν_surj C
  rcases S.F_E d hC with h | h
  · exact ⟨d, h, rfl⟩
  · exact ⟨S.z⁻¹ * d, h, by rw [S.ν_mul, ν_inv, ν_z, zero_add]⟩

theorem image_E : S.ν '' S.E = {C : binarySymMatrices 3 | symThreeDiag C = 0} := by
  ext C
  constructor
  · rintro ⟨e, he, rfl⟩
    exact S.E_F e he
  · intro hC
    obtain ⟨e, he, rfl⟩ := S.exists_mem_E C hC
    exact ⟨e, he, rfl⟩

theorem card_A : Nat.card S.A = 64 := by
  rw [Nat.card_congr (S.a.toEquiv.trans Multiplicative.toAdd), SymThreeCosetData.card_sym]

theorem card_E : Nat.card S.E = 512 := by
  have h := symThree_card_eq_card_image_mul S.A_le_E S.ν (fun x hx y hy => by
    rw [ν_eq_iff]
    exact ⟨fun h => S.mem_A_of_mem_E_R (mul_mem (inv_mem hx) hy) h, fun h => S.A_le_R h⟩)
  rw [S.image_E, SymThreeCosetData.card_alt, S.card_A] at h
  exact h

theorem mem_A_iff_mem_A {x y : D} (hx : x ∈ S.R) (hy : y ∈ S.R) :
    (x ∈ S.A ↔ y ∈ S.A) ↔ x⁻¹ * y ∈ S.A := by
  constructor
  · intro h
    by_cases hxA : x ∈ S.A
    · exact mul_mem (inv_mem hxA) (h.1 hxA)
    · have hyA : y ∉ S.A := fun hyA => hxA (h.2 hyA)
      have := mul_mem (inv_mem (S.mem_A_of_commute hx hxA)) (S.mem_A_of_commute hy hyA)
      rwa [_root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at this
  · intro h
    constructor
    · intro hxA
      have := mul_mem hxA h
      rwa [mul_inv_cancel_left] at this
    · intro hyA
      have := mul_mem hyA (inv_mem h)
      rwa [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at this

theorem card_R : Nat.card S.R = 128 := by
  have h := symThree_card_eq_card_image_mul S.A_le_R (fun x => x ∈ S.A) (fun x hx y hy => by
    rw [eq_iff_iff]
    exact S.mem_A_iff_mem_A hx hy)
  have himage : (fun x => x ∈ S.A) '' (S.R : Set D) = Set.univ := by
    refine Set.eq_univ_of_forall fun p => ?_
    by_cases hp : p
    · exact ⟨1, one_mem _, by simp only [one_mem, hp]⟩
    · exact ⟨S.z, S.z_mem_R, by simp only [S.z_not_mem, hp]⟩
  rw [himage, Nat.card_univ, Nat.card_congr Equiv.propEquivBool,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, S.card_A] at h
  exact h

include S in
theorem card_eq : Nat.card D = 8192 := by
  have h := symThree_card_eq_card_image_mul (K := ⊤) le_top S.ν
    (fun x _ y _ => S.ν_eq_iff x y)
  rw [Subgroup.card_top, Subgroup.coe_top, Set.image_univ_of_surjective S.ν_surj, Nat.card_univ,
    SymThreeCosetData.card_sym, S.card_R] at h
  exact h

theorem E_normal : S.E.Normal :=
  ⟨fun n hn g => by
    have h : g * n * g⁻¹ = ⁅g, n⁆ * n := by
      rw [commutatorElement_def]
      group
    rw [h]
    exact mul_mem (S.A_le_E (S.commutatorElement_mem_A g n)) hn⟩

theorem ν_eq_zero_of_commute {x y : D} (hxF : symThreeDiag (S.ν x) = 0) (hxE : x ∉ S.E)
    (hy : y ∈ S.E) (hc : x * y = y * x) : S.ν y = 0 := by
  have he : S.z⁻¹ * x ∈ S.E := (S.F_E x hxF).resolve_left hxE
  have h1 : S.z⁻¹ * x * y = y * (S.z⁻¹ * x) := S.E_comm _ he _ hy
  have h2 : S.z⁻¹ * y * x = y * S.z⁻¹ * x := by
    calc S.z⁻¹ * y * x = S.z⁻¹ * (y * x) := mul_assoc _ _ _
      _ = S.z⁻¹ * (x * y) := by rw [hc]
      _ = S.z⁻¹ * x * y := (mul_assoc _ _ _).symm
      _ = y * (S.z⁻¹ * x) := h1
      _ = y * S.z⁻¹ * x := (mul_assoc _ _ _).symm
  have h3 : S.z⁻¹ * y = y * S.z⁻¹ := mul_right_cancel h2
  apply S.ν_eq_zero_of_commute_z
  calc S.z * y = S.z * (y * S.z⁻¹) * S.z := by group
    _ = S.z * (S.z⁻¹ * y) * S.z := by rw [h3]
    _ = y * S.z := by group

theorem mem_A_of_mem_P_R {x : D} (hx : x ∈ S.P) (hxR : x ∈ S.R) : x ∈ S.A := by
  rw [← S.P_R]
  exact Subgroup.mem_inf.2 ⟨hx, hxR⟩

theorem image_P : S.ν '' S.P = {B : binarySymMatrices 3 |
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1 = 0 ∧ (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 0 ∧
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2 = 0} := by
  ext B
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (S.P_J _).2 ⟨p, hp, rfl⟩
  · intro hB
    obtain ⟨p, hp, hpν⟩ := (S.P_J B).1 hB
    exact ⟨p, hp, hpν⟩

theorem card_P : Nat.card S.P = 512 := by
  have h := symThree_card_eq_card_image_mul S.A_P S.ν (fun x hx y hy => by
    rw [ν_eq_iff]
    exact ⟨fun h => S.mem_A_of_mem_P_R (mul_mem (inv_mem hx) hy) h, fun h => S.A_le_R h⟩)
  rw [S.image_P, card_symThreeJ, S.card_A] at h
  exact h

theorem mem_E_of_mem_P {x : D} (hxP : x ∈ S.P) (hxF : symThreeDiag (S.ν x) = 0) : x ∈ S.E := by
  by_contra hxE
  obtain ⟨t, ht0, htne, htx⟩ := symThree_J₀_avoid (symThreeOff (S.ν x))
  have hBJ : ((symThreeAltSym t : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1 = 0 ∧
      ((symThreeAltSym t : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 0 ∧
      ((symThreeAltSym t : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2 = 0 :=
    ⟨rfl, ht0, rfl⟩
  obtain ⟨y, hyP, hyν⟩ := (S.P_J _).1 hBJ
  have hyF : symThreeDiag (S.ν y) = 0 := by
    rw [hyν]
    exact symThreeDiag_alt t
  have hxy : S.ν y ≠ S.ν x := by
    intro h
    apply htx
    rw [eq_symThreeAltSym hxF, ← h, hyν]
    funext k
    fin_cases k <;> rfl
  by_cases hyE : y ∈ S.E
  · have := S.ν_eq_zero_of_commute hxF hxE hyE (S.P_comm x hxP y hyP)
    rw [hyν, symThreeAltSym_eq_zero_iff] at this
    exact htne this
  · have hx' := (S.F_E x hxF).resolve_left hxE
    have hy' := (S.F_E y hyF).resolve_left hyE
    have hxyE : x⁻¹ * y ∈ S.E := by
      have := mul_mem (inv_mem hx') hy'
      rwa [_root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at this
    have hc : x * (x⁻¹ * y) = (x⁻¹ * y) * x := by
      rw [mul_inv_cancel_left, mul_assoc, S.P_comm y hyP x hxP, inv_mul_cancel_left]
    have := S.ν_eq_zero_of_commute hxF hxE hxyE hc
    rw [S.ν_mul, ν_inv] at this
    exact hxy (symThree_eq_of_add_eq_zero this).symm

theorem exists_p₀ : ∃ p ∈ S.P, S.ν p = symThreeUnit :=
  (S.P_J symThreeUnit).1 ⟨by decide, by decide, by decide⟩

@[expose] noncomputable def p₀ : D :=
  Classical.choose S.exists_p₀

theorem p₀_mem : S.p₀ ∈ S.P :=
  (Classical.choose_spec S.exists_p₀).1

theorem ν_p₀ : S.ν S.p₀ = symThreeUnit :=
  (Classical.choose_spec S.exists_p₀).2

theorem p₀_commute {e : D} (he : e ∈ S.E)
    (h12 : (S.ν e : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 0) : S.p₀ * e = e * S.p₀ := by
  have hJ : (S.ν e : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1 = 0 ∧
      (S.ν e : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 0 ∧
      (S.ν e : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2 = 0 :=
    ⟨congrFun (S.E_F e he) 1, h12, congrFun (S.E_F e he) 2⟩
  obtain ⟨p', hp'P, hp'ν⟩ := (S.P_J _).1 hJ
  have hp'E : p' ∈ S.E := S.mem_E_of_mem_P hp'P (by rw [hp'ν]; exact S.E_F e he)
  have hr : p'⁻¹ * e ∈ S.A :=
    S.mem_A_of_mem_E_R (mul_mem (inv_mem hp'E) he) ((S.ν_eq_iff p' e).1 hp'ν)
  rw [symThree_commute_iff, show e = p' * (p'⁻¹ * e) from (mul_inv_cancel_left p' e).symm,
    S.commutatorElement_mul_right, symThree_commute_iff.1 (S.P_comm _ S.p₀_mem _ hp'P),
    S.commutatorElement_eq_one_of_mem_A hr, mul_one]

theorem stab_conj_mem_A (i : Fin 4) : S.p₀⁻¹ * S.ρ (symThreeStabGL i) S.p₀ ∈ S.A := by
  have hR : S.p₀⁻¹ * S.ρ (symThreeStabGL i) S.p₀ ∈ S.R := by
    rw [← ν_eq_iff, ν_ρ, ν_p₀]
    exact Subtype.ext (symThreeStab_unit i).symm
  have hcomm : ∀ e ∈ S.E, (S.ν e : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 0 →
      S.ρ (symThreeStabGL i) S.p₀ * e = e * S.ρ (symThreeStabGL i) S.p₀ := by
    intro e he h12
    have he' : S.ρ (symThreeStabGL i) e ∈ S.E := S.E_ρ _ e he
    have h12' : (S.ν (S.ρ (symThreeStabGL i) e) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 0 := by
      rw [ν_ρ, coe_symThreeCongr, eq_symThreeAlt (S.ν e).2 (S.E_F e he)]
      exact symThreeStab_alt i _ h12
    have h2 := congrArg (S.ρ (symThreeStabGL i)) (S.p₀_commute he' h12')
    rwa [map_mul, map_mul, S.ρ_ρ_of_mul_self (symThreeStabGL_mul_self i)] at h2
  rcases S.mem_R_iff.1 hR with h | h
  · exact h
  · exfalso
    obtain ⟨e, he, heν⟩ := S.exists_mem_E (symThreeAltSym ![0, 0, 1]) (symThreeDiag_alt _)
    have h12 : (S.ν e : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 0 := by
      rw [heν]
      rfl
    have hr1 : ⁅S.p₀⁻¹ * S.ρ (symThreeStabGL i) S.p₀, e⁆ = 1 := by
      rw [S.commutatorElement_mul_left, S.commutatorElement_comm e S.p₀⁻¹,
        S.commutatorElement_inv_right', S.commutatorElement_comm S.p₀ e,
        symThree_commute_iff.1 (S.p₀_commute he h12), symThree_commute_iff.1 (hcomm e he h12),
        mul_one]
    rw [show S.p₀⁻¹ * S.ρ (symThreeStabGL i) S.p₀ =
        S.z * (S.z⁻¹ * (S.p₀⁻¹ * S.ρ (symThreeStabGL i) S.p₀)) from
          (mul_inv_cancel_left _ _).symm, S.commutatorElement_mul_left,
      S.commutatorElement_eq_one_of_mem_A_left h, mul_one, commutatorElement_z, aE_eq_one,
      heν, symThreeAltSym_eq_zero_iff] at hr1
    exact absurd hr1 (by decide)

theorem p₀_commutator_formula : ∃ X : binarySymMatrices 3, (X = 0 ∨ X = symThreeUnit) ∧
    ∀ e ∈ S.E, ⁅S.p₀, e⁆ =
      if (S.ν e : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 0 then 1 else S.aE X := by
  obtain ⟨e₁, he₁, he₁ν⟩ := S.exists_mem_E (symThreeAltSym ![1, 0, 0]) (symThreeDiag_alt _)
  obtain ⟨X, hX⟩ := S.exists_aE (S.commutatorElement_mem_A S.p₀ e₁)
  have he₁12 : (S.ν e₁ : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 1 := by
    rw [he₁ν]
    rfl
  refine ⟨X, ?_, ?_⟩
  · have hfix : ∀ i, symThreeStab i * (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (symThreeStab i)ᵀ = X := by
      intro i
      have hr := S.stab_conj_mem_A i
      have hy : e₁⁻¹ * S.ρ (symThreeStabGL i) e₁ ∈ S.E :=
        mul_mem (inv_mem he₁) (S.E_ρ _ e₁ he₁)
      have hy12 : (S.ν (e₁⁻¹ * S.ρ (symThreeStabGL i) e₁) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 0 := by
        rw [S.ν_mul, ν_inv, ν_ρ, AddSubgroup.coe_add, Matrix.add_apply, coe_symThreeCongr, he₁ν]
        change (1 : ZMod 2) + (symThreeStab i * symThreeAlt ![1, 0, 0] * (symThreeStab i)ᵀ) 1 2 = 0
        rw [symThreeStab_alt_one i]
        rfl
      have key : S.ρ (symThreeStabGL i) ⁅S.p₀, e₁⁆ = ⁅S.p₀, e₁⁆ := by
        rw [map_commutatorElement, show S.ρ (symThreeStabGL i) S.p₀ =
            S.p₀ * (S.p₀⁻¹ * S.ρ (symThreeStabGL i) S.p₀) from (mul_inv_cancel_left _ _).symm,
          S.commutatorElement_mul_left, S.commutatorElement_eq_one_of_mem_A_left hr, mul_one,
          show S.ρ (symThreeStabGL i) e₁ = e₁ * (e₁⁻¹ * S.ρ (symThreeStabGL i) e₁) from
            (mul_inv_cancel_left _ _).symm,
          S.commutatorElement_mul_right, symThree_commute_iff.1 (S.p₀_commute hy hy12), mul_one]
      rw [hX, ρ_aE] at key
      exact congrArg Subtype.val (S.aE_injective key)
    rcases symThreeStab_fixed X X.2 hfix with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · intro e he
    split_ifs with h12
    · exact symThree_commute_iff.1 (S.p₀_commute he h12)
    · have h12' : (S.ν e : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 1 :=
        (MatrixExtension.zmod_two_eq_zero_or_one _).resolve_left h12
      have hy : e₁⁻¹ * e ∈ S.E := mul_mem (inv_mem he₁) he
      have hy12 : (S.ν (e₁⁻¹ * e) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 0 := by
        rw [S.ν_mul, ν_inv, AddSubgroup.coe_add, Matrix.add_apply, he₁12, h12']
        rfl
      rw [show e = e₁ * (e₁⁻¹ * e) from (mul_inv_cancel_left _ _).symm,
        S.commutatorElement_mul_right, symThree_commute_iff.1 (S.p₀_commute hy hy12), mul_one, hX]

theorem p₀_commutator_eq_one : ∀ e ∈ S.E, ⁅S.p₀, e⁆ = 1 := by
  obtain ⟨X, hX01, hXe⟩ := S.p₀_commutator_formula
  suffices hX0 : X = 0 by
    intro e he
    rw [hXe e he]
    split_ifs
    · rfl
    · rw [hX0, aE_zero]
  rcases hX01 with h | h
  · exact h
  exfalso
  obtain ⟨-, -, -, -, -, -, v7, v8⟩ := symThree_swap_shear_values
  obtain ⟨e₂, he₂, he₂ν⟩ := S.exists_mem_E (symThreeAltSym ![0, 0, 1]) (symThreeDiag_alt _)
  obtain ⟨e₁, he₁, he₁ν⟩ := S.exists_mem_E (symThreeAltSym ![1, 0, 0]) (symThreeDiag_alt _)
  have hconj : ∀ g : GL (Fin 3) (ZMod 2), g * g = 1 → ∀ e : D,
      ⁅S.ρ g S.p₀, e⁆ = S.ρ g ⁅S.p₀, S.ρ g e⁆ := by
    intro g hg e
    rw [map_commutatorElement, S.ρ_ρ_of_mul_self hg]
  have hlab : ∀ (g : GL (Fin 3) (ZMod 2)) (e : D),
      (S.ν (S.ρ g e) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 =
        ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (S.ν e : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ) 1 2 := by
    intro g e
    rw [ν_ρ, coe_symThreeCongr]
  have hyν : symThreeDiag (S.ν (S.p₀ * S.ρ symThreeSwapGL S.p₀ * S.ρ symThreeShearGL S.p₀)) =
      0 := by
    rw [S.ν_mul, S.ν_mul, ν_ρ, ν_ρ, ν_p₀]
    change symThreeDiag (vecMulVec ![1, 0, 0] ![1, 0, 0] +
        symThreeSwap * vecMulVec ![1, 0, 0] ![1, 0, 0] * symThreeSwapᵀ +
        symThreeShear * vecMulVec ![1, 0, 0] ![1, 0, 0] * symThreeShearᵀ) = 0
    rw [v7]
    exact symThreeDiag_alt _
  have hye₂ : ⁅S.p₀ * S.ρ symThreeSwapGL S.p₀ * S.ρ symThreeShearGL S.p₀, e₂⁆ = 1 := by
    rw [S.commutatorElement_mul_left, S.commutatorElement_mul_left,
      hconj _ symThreeSwapGL_mul_self, hconj _ symThreeShearGL_mul_self, hXe e₂ he₂,
      hXe _ (S.E_ρ symThreeSwapGL e₂ he₂), hXe _ (S.E_ρ symThreeShearGL e₂ he₂),
      ite_eq_left (by rw [he₂ν]; decide), ite_eq_left (by rw [hlab, he₂ν]; decide),
      ite_eq_left (by rw [hlab, he₂ν]; decide), map_one, map_one, one_mul, one_mul]
  have hyE : S.p₀ * S.ρ symThreeSwapGL S.p₀ * S.ρ symThreeShearGL S.p₀ ∈ S.E := by
    rcases S.F_E _ hyν with h' | h'
    · exact h'
    · exfalso
      rw [show S.p₀ * S.ρ symThreeSwapGL S.p₀ * S.ρ symThreeShearGL S.p₀ =
          S.z * (S.z⁻¹ * (S.p₀ * S.ρ symThreeSwapGL S.p₀ * S.ρ symThreeShearGL S.p₀)) from
            (mul_inv_cancel_left _ _).symm, S.commutatorElement_mul_left,
        symThree_commute_iff.1 (S.E_comm _ h' _ he₂), mul_one, commutatorElement_z, aE_eq_one, he₂ν,
        symThreeAltSym_eq_zero_iff] at hye₂
      exact absurd hye₂ (by decide)
  have hye₁ := symThree_commute_iff.1 (S.E_comm _ hyE _ he₁)
  rw [S.commutatorElement_mul_left, S.commutatorElement_mul_left,
    hconj _ symThreeSwapGL_mul_self, hconj _ symThreeShearGL_mul_self, hXe e₁ he₁,
    hXe _ (S.E_ρ symThreeSwapGL e₁ he₁), hXe _ (S.E_ρ symThreeShearGL e₁ he₁),
    ite_eq_right (by rw [he₁ν]; decide), ite_eq_left (by rw [hlab, he₁ν]; decide),
    ite_eq_right (by rw [hlab, he₁ν]; decide), map_one, mul_one, ρ_aE, aE_mul, aE_eq_one, h] at hye₁
  exact v8 (congrArg Subtype.val hye₁)

@[expose] def C : Subgroup D :=
  Subgroup.centralizer (S.E : Set D)

theorem mem_C {x : D} : x ∈ S.C ↔ ∀ e ∈ S.E, e * x = x * e :=
  Subgroup.mem_centralizer_iff

theorem p₀_mem_C : S.p₀ ∈ S.C :=
  S.mem_C.2 fun e he => (symThree_commute_iff.2 (S.p₀_commutator_eq_one e he)).symm

theorem ρ_mem_C (g : GL (Fin 3) (ZMod 2)) {x : D} (hx : x ∈ S.C) : S.ρ g x ∈ S.C := by
  rw [mem_C] at hx ⊢
  intro e he
  have h := congrArg (S.ρ g) (hx _ (S.E_ρ g⁻¹ e he))
  rwa [map_mul, map_mul, S.ρ_ρ_inv] at h

theorem A_le_C : S.A ≤ S.C :=
  fun _ ha => S.mem_C.2 fun e _ => (S.commute_of_mem_A ha e).symm

theorem E_le_C : S.E ≤ S.C :=
  fun x hx => S.mem_C.2 fun e he => S.E_comm e he x hx

theorem z_not_mem_C : S.z ∉ S.C := by
  intro hz
  obtain ⟨e, he, heν⟩ := S.exists_mem_E (symThreeAltSym ![0, 0, 1]) (symThreeDiag_alt _)
  have := S.ν_eq_zero_of_commute_z (S.mem_C.1 hz e he).symm
  rw [heν, symThreeAltSym_eq_zero_iff] at this
  exact absurd this (by decide)

theorem mem_A_of_mem_C_R {x : D} (hx : x ∈ S.C) (hxR : x ∈ S.R) : x ∈ S.A := by
  rcases S.mem_R_iff.1 hxR with h | h
  · exact h
  · exfalso
    apply S.z_not_mem_C
    have := mul_mem hx (inv_mem (S.A_le_C h))
    rwa [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at this

theorem C_inf_R : S.C ⊓ S.R = S.A :=
  le_antisymm (fun _ hx => S.mem_A_of_mem_C_R (Subgroup.mem_inf.1 hx).1 (Subgroup.mem_inf.1 hx).2)
    (le_inf S.A_le_C S.A_le_R)

theorem iterate_mem_C (k : ℕ) : (S.ρ symThreeSinger)^[k] S.p₀ ∈ S.C := by
  induction k with
  | zero => exact S.p₀_mem_C
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact S.ρ_mem_C _ ih

theorem ν_iterate (k : ℕ) :
    S.ν ((S.ρ symThreeSinger)^[k] S.p₀) = (symThreeCongr symThreeSinger)^[k] symThreeUnit := by
  induction k with
  | zero => exact S.ν_p₀
  | succ k ih => rw [Function.iterate_succ_apply', ν_ρ, ih, Function.iterate_succ_apply']

theorem iterate_aE (k : ℕ) (B : binarySymMatrices 3) :
    (S.ρ symThreeSinger)^[k] (S.aE B) = S.aE ((symThreeCongr symThreeSinger)^[k] B) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, ρ_aE, Function.iterate_succ_apply']

theorem iterate_sq (k : ℕ) (x : D) :
    (S.ρ symThreeSinger)^[k] (x ^ 2) = ((S.ρ symThreeSinger)^[k] x) ^ 2 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, map_pow, Function.iterate_succ_apply']

theorem ν_iterate_coe (k : ℕ) :
    (S.ν ((S.ρ symThreeSinger)^[k] S.p₀) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      vecMulVec (symThreeOrbit k) (symThreeOrbit k) := by
  rw [S.ν_iterate, symThreeCongr_iterate_singer_unit]

theorem exists_mem_C (B : binarySymMatrices 3) : ∃ c ∈ S.C, S.ν c = B := by
  obtain ⟨b, hb⟩ := symThreeOrbit_span B B.2
  let f : Fin 7 → D := fun k => if b k then (S.ρ symThreeSinger)^[k] S.p₀ else 1
  have hfC : ∀ k, f k ∈ S.C := by
    intro k
    simp only [f]
    split_ifs
    · exact S.iterate_mem_C k
    · exact S.C.one_mem
  have hfν : ∀ k, (S.ν (f k) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      if b k then vecMulVec (symThreeOrbit k) (symThreeOrbit k) else 0 := by
    intro k
    simp only [f]
    split_ifs
    · exact S.ν_iterate_coe k
    · rw [ν_one]
      rfl
  refine ⟨f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6, ?_, ?_⟩
  · exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (hfC 0) (hfC 1)) (hfC 2))
      (hfC 3)) (hfC 4)) (hfC 5)) (hfC 6)
  · apply Subtype.ext
    simp only [S.ν_mul, AddSubgroup.coe_add, hfν]
    rw [hb, Fin.sum_univ_seven]

theorem card_C : Nat.card S.C = 4096 := by
  have h := symThree_card_eq_card_image_mul S.A_le_C S.ν (fun x hx y hy => by
    rw [ν_eq_iff]
    exact ⟨fun h => S.mem_A_of_mem_C_R (mul_mem (inv_mem hx) hy) h, fun h => S.A_le_R h⟩)
  have himage : S.ν '' S.C = Set.univ := Set.eq_univ_of_forall fun B => by
    obtain ⟨c, hc, hcν⟩ := S.exists_mem_C B
    exact ⟨c, hc, hcν⟩
  rw [himage, Nat.card_univ, SymThreeCosetData.card_sym, S.card_A] at h
  exact h

theorem univ_eq : (Set.univ : Set D) = (Subgroup.zpowers S.z : Set D) * (S.C : Set D) := by
  refine (Set.eq_univ_of_forall fun d => ?_).symm
  obtain ⟨c, hc, hcν⟩ := S.exists_mem_C (S.ν d)
  have hR : d * c⁻¹ ∈ S.R := (S.ν_eq_iff' c d).1 hcν
  rw [Set.mem_mul]
  rcases S.mem_R_iff.1 hR with h | h
  · refine ⟨1, Subgroup.one_mem _, d, ?_, one_mul d⟩
    have := mul_mem (S.A_le_C h) hc
    rwa [inv_mul_cancel_right] at this
  · refine ⟨S.z, Subgroup.mem_zpowers _, S.z⁻¹ * d, ?_, mul_inv_cancel_left _ _⟩
    have := mul_mem (S.A_le_C h) hc
    rwa [mul_assoc, inv_mul_cancel_right] at this

theorem C_normal : S.C.Normal := by
  have := S.E_normal
  exact Subgroup.normal_centralizer

theorem C_map_ρ (g : GL (Fin 3) (ZMod 2)) : S.C.map (S.ρ g).toMonoidHom = S.C := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact S.ρ_mem_C g hx
  · intro x hx
    exact ⟨S.ρ g⁻¹ x, S.ρ_mem_C g⁻¹ hx, S.ρ_ρ_inv g x⟩

theorem mem_E_iff (c : D) : (c ∈ S.C ∧ symThreeDiag (S.ν c) = 0) ↔ c ∈ S.E := by
  constructor
  · rintro ⟨hc, hcF⟩
    rcases S.F_E c hcF with h | h
    · exact h
    · exfalso
      apply S.z_not_mem_C
      have := mul_mem hc (inv_mem (S.E_le_C h))
      rwa [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
  · intro h
    exact ⟨S.E_le_C h, S.E_F c h⟩

theorem P_le_C : S.P ≤ S.C := by
  intro x hx
  have hxJ := (S.P_J (S.ν x)).2 ⟨x, hx, rfl⟩
  rcases MatrixExtension.zmod_two_eq_zero_or_one ((S.ν x : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0)
    with h0 | h0
  · have hF : symThreeDiag (S.ν x) = 0 := by
      funext k
      fin_cases k
      · exact h0
      · exact hxJ.1
      · exact hxJ.2.2
    exact S.E_le_C (S.mem_E_of_mem_P hx hF)
  · have hy : S.p₀⁻¹ * x ∈ S.P := mul_mem (inv_mem S.p₀_mem) hx
    have hF : symThreeDiag (S.ν (S.p₀⁻¹ * x)) = 0 := by
      rw [S.ν_mul, ν_inv, ν_p₀]
      funext k
      fin_cases k
      · change (1 : ZMod 2) * 1 + (S.ν x : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 0
        rw [h0]
        rfl
      · change (0 : ZMod 2) * 0 + (S.ν x : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1 = 0
        rw [hxJ.1]
        rfl
      · change (0 : ZMod 2) * 0 + (S.ν x : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2 = 0
        rw [hxJ.2.2]
        rfl
    have := mul_mem S.p₀_mem_C (S.E_le_C (S.mem_E_of_mem_P hy hF))
    rwa [mul_inv_cancel_left] at this

theorem E_le_center : S.E ≤ (Subgroup.center S.C).map S.C.subtype := by
  intro e he
  refine ⟨⟨e, S.E_le_C he⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro c
  exact Subtype.ext (S.mem_C.1 c.2 e he).symm

@[expose] def diagHom : D →* Multiplicative (Fin 3 → ZMod 2) where
  toFun d := .ofAdd (symThreeDiag (S.ν d))
  map_one' := by
    rw [ν_one]
    rfl
  map_mul' d d' := by
    rw [S.ν_mul, AddSubgroup.coe_add, symThreeDiag_add, ofAdd_add]

theorem νHom_C_ker : (S.νHom.comp S.C.subtype).ker = S.A.subgroupOf S.C := by
  ext c
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change Multiplicative.ofAdd (S.ν c) = 1 ↔ (c : D) ∈ S.A
  rw [ofAdd_eq_one]
  exact ⟨fun h => S.mem_A_of_mem_C_R c.2 (S.mem_R_of_ν_eq_zero h),
    fun h => S.ν_of_mem_R (S.A_le_R h)⟩

theorem νHom_C_surj : Function.Surjective (S.νHom.comp S.C.subtype) := fun B => by
  obtain ⟨c, hc, hcν⟩ := S.exists_mem_C (Multiplicative.toAdd B)
  exact ⟨⟨c, hc⟩, by
    change Multiplicative.ofAdd (S.ν c) = B
    rw [hcν, ofAdd_toAdd]⟩

theorem diagHom_C_ker : (S.diagHom.comp S.C.subtype).ker = S.E.subgroupOf S.C := by
  ext c
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change Multiplicative.ofAdd (symThreeDiag (S.ν c)) = 1 ↔ (c : D) ∈ S.E
  rw [ofAdd_eq_one, ← S.mem_E_iff]
  exact ⟨fun h => ⟨c.2, h⟩, fun h => h.2⟩

theorem diagHom_C_surj : Function.Surjective (S.diagHom.comp S.C.subtype) := fun w => by
  obtain ⟨c, hc, hcν⟩ := S.exists_mem_C ⟨diagonal (Multiplicative.toAdd w), by
    rw [mem_binarySymMatrices, diagonal_transpose]⟩
  refine ⟨⟨c, hc⟩, ?_⟩
  change Multiplicative.ofAdd (symThreeDiag (S.ν c)) = w
  rw [hcν]
  apply Multiplicative.toAdd.injective
  funext k
  simp [symThreeDiag]

theorem exists_quotient_A : ∃ (_ : (S.A.subgroupOf S.C).Normal)
    (ψ : S.C ⧸ S.A.subgroupOf S.C ≃* Multiplicative (binarySymMatrices 3)),
      ∀ c : S.C, ψ c = Multiplicative.ofAdd (S.ν c) := by
  have := S.A_normal
  exact ⟨inferInstance, (QuotientGroup.quotientMulEquivOfEq S.νHom_C_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ S.νHom_C_surj), fun c => rfl⟩

theorem exists_quotient_E : ∃ (_ : (S.E.subgroupOf S.C).Normal)
    (ψ : S.C ⧸ S.E.subgroupOf S.C ≃* Multiplicative (Fin 3 → ZMod 2)),
      ∀ c : S.C, ψ c = Multiplicative.ofAdd (symThreeDiag (S.ν c)) := by
  have := S.E_normal
  exact ⟨inferInstance, (QuotientGroup.quotientMulEquivOfEq S.diagHom_C_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ S.diagHom_C_surj), fun c => rfl⟩

theorem exists_ε : ∃ ε : ZMod 2, S.p₀ ^ 2 = S.aE (symThreeSquare ε ![1, 0, 0]) := by
  obtain ⟨s, hs⟩ := S.exists_aE (S.sq_mem S.p₀)
  have hfix : ∀ i, symThreeStab i * (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      (symThreeStab i)ᵀ = s := by
    intro i
    have hr := S.stab_conj_mem_A i
    have h : S.ρ (symThreeStabGL i) (S.p₀ ^ 2) = S.p₀ ^ 2 := by
      rw [map_pow, show S.ρ (symThreeStabGL i) S.p₀ =
          S.p₀ * (S.p₀⁻¹ * S.ρ (symThreeStabGL i) S.p₀) from (mul_inv_cancel_left _ _).symm,
        (show Commute S.p₀ (S.p₀⁻¹ * S.ρ (symThreeStabGL i) S.p₀) from
          (S.commute_of_mem_A hr S.p₀).symm).mul_pow, S.sq_eq_one_of_mem_A hr, mul_one]
    rw [hs, ρ_aE] at h
    exact congrArg Subtype.val (S.aE_injective h)
  refine ⟨(s : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0, ?_⟩
  rw [hs]
  congr 1
  apply Subtype.ext
  rw [coe_symThreeSquare]
  rcases symThreeStab_fixed s s.2 hfix with h | h
  · rw [h]
    simp
  · rw [h]
    decide

theorem sq_formula {ε : ZMod 2} (hε : S.p₀ ^ 2 = S.aE (symThreeSquare ε ![1, 0, 0])) {c : D}
    (hc : c ∈ S.C) : c ^ 2 = S.aE (symThreeSquare ε (symThreeDiag (S.ν c))) := by
  by_cases hw : symThreeDiag (S.ν c) = 0
  · rw [hw, symThreeSquare_zero_right, aE_zero]
    exact S.E_sq c ((S.mem_E_iff c).1 ⟨hc, hw⟩)
  · obtain ⟨k, hk⟩ := symThreeOrbit_surj _ hw
    have hxC := S.iterate_mem_C k
    have hxν : symThreeDiag (S.ν ((S.ρ symThreeSinger)^[k] S.p₀)) = symThreeDiag (S.ν c) := by
      rw [S.ν_iterate_coe, symThreeDiag_vecMulVec_self, hk]
    have hy : ((S.ρ symThreeSinger)^[k] S.p₀)⁻¹ * c ∈ S.E := by
      refine (S.mem_E_iff _).1 ⟨mul_mem (inv_mem hxC) hc, ?_⟩
      rw [S.ν_mul, ν_inv, AddSubgroup.coe_add, symThreeDiag_add, hxν]
      funext j
      exact symThree_zmod_add_self _
    have h1 : c ^ 2 = ((S.ρ symThreeSinger)^[k] S.p₀) ^ 2 := by
      conv_lhs => rw [show c = (S.ρ symThreeSinger)^[k] S.p₀ *
        (((S.ρ symThreeSinger)^[k] S.p₀)⁻¹ * c) from (mul_inv_cancel_left _ _).symm]
      rw [(show Commute ((S.ρ symThreeSinger)^[k] S.p₀)
          (((S.ρ symThreeSinger)^[k] S.p₀)⁻¹ * c) from (S.mem_C.1 hxC _ hy).symm).mul_pow,
        S.E_sq _ hy, mul_one]
    rw [h1, ← S.iterate_sq, hε, S.iterate_aE]
    congr 1
    apply Subtype.ext
    rcases MatrixExtension.zmod_two_eq_zero_or_one ε with rfl | rfl
    · rw [symThreeSquare_zero_left, symThreeSquare_zero_left, symThreeCongr_iterate_singer_zero]
    · rw [show symThreeSquare 1 ![1, 0, 0] = symThreeUnit from Subtype.ext (one_smul _ _),
        symThreeCongr_iterate_singer_unit, coe_symThreeSquare, one_smul, ← hk]

theorem commutator_formula {ε : ZMod 2} (hε : S.p₀ ^ 2 = S.aE (symThreeSquare ε ![1, 0, 0]))
    {c d : D} (hc : c ∈ S.C) (hd : d ∈ S.C) :
    c⁻¹ * d⁻¹ * c * d =
      S.aE (symThreeSquarePolar ε (symThreeDiag (S.ν c)) (symThreeDiag (S.ν d))) := by
  have hcd := S.sq_formula hε (mul_mem hc hd)
  have h1 := S.sq_formula hε hc
  have h2 := S.sq_formula hε hd
  have hu : (d ^ 2)⁻¹ ∈ S.A := inv_mem (S.sq_mem d)
  have hid : c⁻¹ * d⁻¹ * c * d = (c ^ 2 * d ^ 2)⁻¹ * (c * d) ^ 2 := by
    calc c⁻¹ * d⁻¹ * c * d = c⁻¹ * ((d ^ 2)⁻¹ * (d * c * d)) := by
          simp only [sq]
          group
      _ = (d ^ 2)⁻¹ * (c⁻¹ * (d * c * d)) := by
          rw [← mul_assoc, ← S.commute_of_mem_A hu c⁻¹, mul_assoc]
      _ = (c ^ 2 * d ^ 2)⁻¹ * (c * d) ^ 2 := by
          simp only [sq]
          group
  rw [hid, hcd, h1, h2, S.ν_mul, AddSubgroup.coe_add, symThreeDiag_add, aE_mul,
    S.inv_eq_of_mem_A (S.aE_mem _), aE_mul, symThreeSquare_add]

@[expose] def Ia : Subgroup D where
  carrier := {x | ∃ B : binarySymMatrices 3, symThreeDiag B = 0 ∧ x = S.aE B}
  mul_mem' := by
    rintro _ _ ⟨B, hB, rfl⟩ ⟨B', hB', rfl⟩
    refine ⟨B + B', ?_, (S.aE_mul B B')⟩
    rw [AddSubgroup.coe_add, symThreeDiag_add, hB, hB', add_zero]
  one_mem' := ⟨0, symThreeDiag_zero, S.aE_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨B, hB, S.inv_eq_of_mem_A (S.aE_mem B)⟩

theorem eps_zero (hε : S.p₀ ^ 2 = S.aE (symThreeSquare 0 ![1, 0, 0])) :
    (IsMulCommutative S.C ∧ ∀ c ∈ S.C, c ^ 2 = 1) ∧ Subgroup.center S.C = ⊤ := by
  have hsq : ∀ c ∈ S.C, c ^ 2 = 1 := fun c hc => by
    rw [S.sq_formula hε hc, symThreeSquare_zero_left, aE_zero]
  have hcomm : ∀ c ∈ S.C, ∀ d ∈ S.C, c * d = d * c := fun c hc d hd => by
    have h := S.commutator_formula hε hc hd
    rw [show symThreeSquarePolar 0 (symThreeDiag (S.ν c)) (symThreeDiag (S.ν d)) = 0 from
      Subtype.ext (zero_smul _ _), aE_zero] at h
    calc c * d = d * c * (c⁻¹ * d⁻¹ * c * d) := by group
      _ = d * c := by rw [h, mul_one]
  refine ⟨⟨IsMulCommutative.of_setLike_mul_comm hcomm, hsq⟩, ?_⟩
  rw [eq_top_iff]
  intro x _
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (hcomm _ y.2 _ x.2)

theorem eps_one (hε : S.p₀ ^ 2 = S.aE (symThreeSquare 1 ![1, 0, 0])) :
    Monoid.exponent S.C = 4 ∧ Subgroup.closure {x | ∃ c ∈ S.C, c ^ 2 = x} = S.A ∧
      ⁅S.C, S.C⁆ = S.Ia ∧ (Subgroup.center S.C).map S.C.subtype = S.E ∧
      (∀ c ∈ S.C, c ^ 2 = 1 ↔ c ∈ S.E) := by
  have hsq1 : ∀ c ∈ S.C, (c ^ 2 = 1 ↔ c ∈ S.E) := by
    intro c hc
    rw [S.sq_formula hε hc, aE_eq_one, ← S.mem_E_iff]
    constructor
    · intro h
      refine ⟨hc, ?_⟩
      have h' := congrArg Subtype.val h
      rw [coe_symThreeSquare, one_smul] at h'
      exact (vecMulVec_self_eq_zero_iff _).1 h'
    · rintro ⟨-, h⟩
      rw [h, symThreeSquare_zero_right]
  refine ⟨?_, ?_, ?_, ?_, hsq1⟩
  · have h4 : ∀ c : S.C, c ^ 4 = 1 := fun c => Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
        S.sq_eq_one_of_mem_A (S.sq_mem _)])
    have hp : ¬ (⟨S.p₀, S.p₀_mem_C⟩ : S.C) ^ 2 = 1 := by
      intro h
      have h' : S.p₀ ^ 2 = 1 := congrArg Subtype.val h
      rw [hsq1 _ S.p₀_mem_C] at h'
      have := S.E_F _ h'
      rw [ν_p₀] at this
      exact absurd (congrFun this 0) (by decide)
    have hdvd : Monoid.exponent S.C ∣ 4 := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 h4
    have hndvd : ¬ Monoid.exponent S.C ∣ 2 := fun h =>
      hp (Monoid.exponent_dvd_iff_forall_pow_eq_one.1 h _)
    have hle : Monoid.exponent S.C ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Monoid.exponent S.C
    · exact absurd hdvd (by decide)
    · exact absurd (one_dvd 2) hndvd
    · exact absurd (dvd_refl 2) hndvd
    · exact absurd hdvd (by decide)
    · rfl
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨c, -, rfl⟩
      exact S.sq_mem c
    · intro x hx
      obtain ⟨B, rfl⟩ := S.exists_aE hx
      obtain ⟨b, hb⟩ := symThreeOrbit_span B B.2
      let T : Fin 7 → binarySymMatrices 3 := fun k => if b k then
        ⟨vecMulVec (symThreeOrbit k) (symThreeOrbit k),
          MatrixExtension.vecMulVec_self_mem_binarySymMatrices _⟩ else 0
      have hBT : B = T 0 + T 1 + T 2 + T 3 + T 4 + T 5 + T 6 := by
        apply Subtype.ext
        rw [hb, Fin.sum_univ_seven]
        simp only [AddSubgroup.coe_add, T]
        congr 1 <;> (try congr 1) <;> (try congr 1) <;> (try congr 1) <;> (try congr 1) <;>
          (try congr 1) <;> split_ifs <;> rfl
      have hT : ∀ k, S.aE (T k) ∈ Subgroup.closure {x | ∃ c ∈ S.C, c ^ 2 = x} := by
        intro k
        simp only [T]
        split_ifs
        · refine Subgroup.subset_closure ⟨_, S.iterate_mem_C k, ?_⟩
          rw [S.sq_formula hε (S.iterate_mem_C k)]
          congr 1
          apply Subtype.ext
          rw [coe_symThreeSquare, one_smul, S.ν_iterate_coe, symThreeDiag_vecMulVec_self]
        · rw [aE_zero]
          exact Subgroup.one_mem _
      rw [hBT, ← aE_mul, ← aE_mul, ← aE_mul, ← aE_mul, ← aE_mul, ← aE_mul]
      exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (hT 0) (hT 1)) (hT 2)) (hT 3))
        (hT 4)) (hT 5)) (hT 6)
  · apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro c hc d hd
      rw [← S.conj_commutator, S.commutator_formula hε hc hd]
      refine ⟨_, ?_, rfl⟩
      rw [coe_symThreeSquarePolar, symThreeDiag_smul, symThreeDiag_polar, smul_zero]
    · rintro _ ⟨B, hB, rfl⟩
      have hc : ∀ w : Fin 3 → ZMod 2, ∃ c ∈ S.C, symThreeDiag (S.ν c) = w := by
        intro w
        obtain ⟨c, hc, hcν⟩ := S.exists_mem_C ⟨diagonal w, by
          rw [mem_binarySymMatrices, diagonal_transpose]⟩
        refine ⟨c, hc, ?_⟩
        rw [hcν]
        funext k
        simp [symThreeDiag]
      obtain ⟨c₀, hc₀, hc₀ν⟩ := hc ![1, 0, 0]
      obtain ⟨c₁, hc₁, hc₁ν⟩ := hc ![0, 1, 0]
      obtain ⟨c₂, hc₂, hc₂ν⟩ := hc ![0, 0, 1]
      have hcomm : ∀ {x y : D}, x ∈ S.C → y ∈ S.C →
          S.aE (symThreeSquarePolar 1 (symThreeDiag (S.ν x)) (symThreeDiag (S.ν y))) ∈
            ⁅S.C, S.C⁆ := by
        intro x y hx hy
        rw [← S.commutator_formula hε hx hy, S.conj_commutator]
        exact Subgroup.commutator_mem_commutator hx hy
      have h12 := hcomm hc₁ hc₂
      have h02 := hcomm hc₀ hc₂
      have h01 := hcomm hc₀ hc₁
      rw [hc₁ν, hc₂ν] at h12
      rw [hc₀ν, hc₂ν] at h02
      rw [hc₀ν, hc₁ν] at h01
      have hsel : ∀ (p : Prop) [Decidable p] (X : binarySymMatrices 3),
          S.aE X ∈ ⁅S.C, S.C⁆ → S.aE (if p then X else 0) ∈ ⁅S.C, S.C⁆ := by
        intro p _ X hX
        split_ifs
        · exact hX
        · rw [aE_zero]
          exact Subgroup.one_mem _
      have hBsum : B = (if symThreeOff B 0 = 1 then symThreeSquarePolar 1 ![0, 1, 0] ![0, 0, 1]
            else 0) + (if symThreeOff B 1 = 1 then symThreeSquarePolar 1 ![1, 0, 0] ![0, 0, 1]
            else 0) + (if symThreeOff B 2 = 1 then symThreeSquarePolar 1 ![1, 0, 0] ![0, 1, 0]
            else 0) := by
        have hBt : (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) = symThreeAlt (symThreeOff B) :=
          eq_symThreeAlt B.2 hB
        apply Subtype.ext
        rw [AddSubgroup.coe_add, AddSubgroup.coe_add]
        conv_lhs => rw [hBt, symThreeAlt_eq_polar]
        split_ifs <;> simp [coe_symThreeSquarePolar]
      rw [hBsum, ← aE_mul, ← aE_mul]
      exact mul_mem (mul_mem (hsel _ _ h12) (hsel _ _ h02)) (hsel _ _ h01)
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hx
      refine (S.mem_E_iff x).1 ⟨x.2, ?_⟩
      by_contra hw
      obtain ⟨v, hv⟩ := symThreeDiag_polar_ne _ hw
      obtain ⟨d, hd, hdν⟩ := S.exists_mem_C ⟨diagonal v, by
        rw [mem_binarySymMatrices, diagonal_transpose]⟩
      have hdv : symThreeDiag (S.ν d) = v := by
        rw [hdν]
        funext k
        simp [symThreeDiag]
      have hc : (x : D) * d = d * x := congrArg Subtype.val (hx ⟨d, hd⟩).symm
      have h := S.commutator_formula hε x.2 hd
      have h1 : (x : D)⁻¹ * d⁻¹ * x * d = 1 := by
        calc (x : D)⁻¹ * d⁻¹ * x * d = (x : D)⁻¹ * d⁻¹ * (x * d) := by rw [mul_assoc]
          _ = (x : D)⁻¹ * d⁻¹ * (d * x) := by rw [hc]
          _ = 1 := by group
      rw [h1, eq_comm, aE_eq_one, hdv] at h
      apply hv
      have h' := congrArg Subtype.val h
      rwa [coe_symThreeSquarePolar, one_smul] at h'
    · exact S.E_le_center

end SymThreeCentralizerData

theorem symThree_mem_alt_iff (B : binarySymMatrices 3) :
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ binaryAltMatrices 3 ↔ symThreeDiag B = 0 := by
  rw [mem_binaryAltMatrices]
  exact ⟨fun h => funext h.2, fun h => ⟨B.2, fun i => congrFun h i⟩⟩

theorem binary_symmetric_three_centralizer_complement_and_square_map
    {D : Type*} [Group D] (A : Subgroup D) (hAc : A ≤ Subgroup.center D)
    (a : A ≃* Multiplicative (binarySymMatrices 3)) (z : D) (hz2 : z ^ 2 = 1) (hzA : z ∉ A)
    (R : Subgroup D) (hR : R = A ⊔ Subgroup.zpowers z) (hsq : ∀ d : D, d ^ 2 ∈ A)
    (ν : D → binarySymMatrices 3)
    (hν : ∀ d : D, (a.symm (.ofAdd (ν d)) : D) = z⁻¹ * d⁻¹ * z * d)
    (hνs : Function.Surjective ν) (hνk : ∀ d : D, ν d = 0 ↔ d ∈ R)
    (ρ : GL (Fin 3) (ZMod 2) →* MulAut D) (hρz : ∀ g : GL (Fin 3) (ZMod 2), ρ g z = z)
    (hρa : ∀ (g : GL (Fin 3) (ZMod 2)) (B : binarySymMatrices 3),
      ρ g (a.symm (.ofAdd B) : D) = a.symm (.ofAdd (symThreeCongr g B)))
    (E : Subgroup D)
    (hEF : ∀ e ∈ E, (ν e : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ binaryAltMatrices 3)
    (hEρ : ∀ (g : GL (Fin 3) (ZMod 2)), ∀ e ∈ E, ρ g e ∈ E) [IsMulCommutative E]
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) (hER : E ⊓ R = A)
    (hFE : ∀ d : D, (ν d : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ binaryAltMatrices 3 ↔
      d ∈ (Subgroup.zpowers z : Set D) * (E : Set D))
    (P : Subgroup D) [IsMulCommutative P] (hAP : A ≤ P) (hPR : P ⊓ R = A)
    (hPJ : ∀ B : binarySymMatrices 3,
      (∀ i j : Fin 3, i ≠ 0 → j ≠ 0 → (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j = 0) ↔
        ∃ p ∈ P, ν p = B)
    (C : Subgroup D) (hC : C = Subgroup.centralizer (E : Set D)) :
    C.Normal ∧ (∀ g : GL (Fin 3) (ZMod 2), C.map (ρ g).toMonoidHom = C) ∧
    Nat.card D = 8192 ∧ Nat.card E = 512 ∧ Nat.card P = 512 ∧ Nat.card C = 4096 ∧
    (Set.univ : Set D) = (Subgroup.zpowers z : Set D) * (C : Set D) ∧ C ⊓ R = A ∧
    (∀ c : D, (c ∈ C ∧ (ν c : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ binaryAltMatrices 3) ↔
      c ∈ E) ∧
    P ≤ C ∧ E ≤ (Subgroup.center C).map C.subtype ∧
    (∃ (_ : (A.subgroupOf C).Normal)
      (ψ : C ⧸ A.subgroupOf C ≃* Multiplicative (binarySymMatrices 3)),
        ∀ c : C, ψ c = .ofAdd (ν c)) ∧
    (∀ (g : GL (Fin 3) (ZMod 2)) (d : D), ν (ρ g d) = symThreeCongr g (ν d)) ∧
    (∃ (_ : (E.subgroupOf C).Normal)
      (ψ : C ⧸ E.subgroupOf C ≃* Multiplicative (Fin 3 → ZMod 2)),
        ∀ c : C, ψ c = .ofAdd (symThreeDiag (ν c))) ∧
    (∀ (g : GL (Fin 3) (ZMod 2)) (d : D),
      symThreeDiag (ν (ρ g d)) = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ symThreeDiag (ν d)) ∧
    ∃ ε : ZMod 2,
      (∀ c ∈ C, ∀ d ∈ C,
        c ^ 2 = a.symm (.ofAdd (symThreeSquare ε (symThreeDiag (ν c)))) ∧
        c⁻¹ * d⁻¹ * c * d =
          a.symm (.ofAdd (symThreeSquarePolar ε (symThreeDiag (ν c)) (symThreeDiag (ν d))))) ∧
      (ε = 0 → (IsMulCommutative C ∧ ∀ c ∈ C, c ^ 2 = 1) ∧ Nat.card C = 4096 ∧
        Subgroup.center C = ⊤) ∧
      (ε = 1 → Monoid.exponent C = 4 ∧ Subgroup.closure {x | ∃ c ∈ C, c ^ 2 = x} = A ∧
        (∀ x : D, x ∈ ⁅C, C⁆ ↔ ∃ B : binarySymMatrices 3,
          (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ binaryAltMatrices 3 ∧
            x = a.symm (.ofAdd B)) ∧
        (Subgroup.center C).map C.subtype = E ∧ ∀ c ∈ C, c ^ 2 = 1 ↔ c ∈ E) := by
  subst hR hC
  have hFE' : ∀ d : D, symThreeDiag (ν d) = 0 → d ∈ E ∨ z⁻¹ * d ∈ E := by
    intro d hd
    obtain ⟨x, hx, e, he, rfl⟩ := Set.mem_mul.1 ((hFE d).1 ((symThree_mem_alt_iff _).2 hd))
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rcases symThree_zpow_of_sq_eq_one hz2 k with h | h
    · left
      rw [h, one_mul]
      exact he
    · right
      rw [h, inv_mul_cancel_left]
      exact he
  have hJ : ∀ B : binarySymMatrices 3, ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1 = 0 ∧
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 0 ∧
        (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2 = 0) ↔
      ∀ i j : Fin 3, i ≠ 0 → j ≠ 0 → (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j = 0 := by
    intro B
    have h21 : (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 =
        (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 :=
      congrFun (congrFun B.2 1) 2
    constructor
    · rintro ⟨h11, h12, h22⟩ i j hi hj
      fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd rfl hi
        | exact absurd rfl hj
        | exact h11
        | exact h12
        | exact h22
        | exact h21.trans h12
    · intro h
      exact ⟨h 1 1 (by decide) (by decide), h 1 2 (by decide) (by decide),
        h 2 2 (by decide) (by decide)⟩
  let S : SymThreeCentralizerData D :=
    { A := A
      central := hAc
      a := a
      z := z
      z_sq := hz2
      z_not_mem := hzA
      sq_mem := hsq
      ν := ν
      ν_spec := hν
      ν_surj := hνs
      ν_ker := hνk
      ρ := ρ
      ρ_z := hρz
      ρ_a := hρa
      E := E
      E_F := fun e he => (symThree_mem_alt_iff _).1 (hEF e he)
      E_ρ := hEρ
      E_comm := fun _ he _ he' => setLike_mul_comm he he'
      E_sq := hE2
      E_R := hER
      F_E := hFE'
      P := P
      P_comm := fun _ hp _ hp' => setLike_mul_comm hp hp'
      A_P := hAP
      P_R := hPR
      P_J := fun B => (hJ B).trans (hPJ B) }
  obtain ⟨ε, hε⟩ := S.exists_ε
  refine ⟨S.C_normal, S.C_map_ρ, S.card_eq, S.card_E, S.card_P, S.card_C, S.univ_eq, S.C_inf_R,
    fun c => by rw [symThree_mem_alt_iff]; exact S.mem_E_iff c, S.P_le_C, S.E_le_center,
    S.exists_quotient_A, S.ν_ρ, S.exists_quotient_E,
    fun g d => by
      show symThreeDiag (S.ν (S.ρ g d) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
      rw [S.ν_ρ, symThreeDiag_coe_congr], ε,
    fun c hc d hd => ⟨S.sq_formula hε hc, S.commutator_formula hε hc hd⟩, ?_, ?_⟩
  · rintro rfl
    exact ⟨(S.eps_zero hε).1, S.card_C, (S.eps_zero hε).2⟩
  · rintro rfl
    obtain ⟨h1, h2, h3, h4, h5⟩ := S.eps_one hε
    refine ⟨h1, h2, fun x => ?_, h4, h5⟩
    show x ∈ ⁅S.C, S.C⁆ ↔ _
    rw [h3]
    show (∃ B : binarySymMatrices 3, symThreeDiag B = 0 ∧ x = S.aE B) ↔ _
    exact exists_congr fun B => and_congr_left fun _ => (symThree_mem_alt_iff B).symm

end CFSG.LocalAnalysis.ComponentInitial
