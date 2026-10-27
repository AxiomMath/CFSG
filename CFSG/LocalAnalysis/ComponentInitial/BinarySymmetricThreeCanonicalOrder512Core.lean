module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeCentralizerComplement

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix
open scoped commutatorElement Pointwise

section SymThreeAffineAlgebra

@[expose] def symThreeRankOneSym (v : Fin 3 → ZMod 2) : binarySymMatrices 3 :=
  ⟨vecMulVec v v, MatrixExtension.vecMulVec_self_mem_binarySymMatrices v⟩

@[expose] def symThreeTransl (a : Fin 3 → ZMod 2) (ε : ZMod 2) (B : binarySymMatrices 3) :
    binarySymMatrices 3 :=
  ⟨(B : Matrix (Fin 3) (Fin 3) (ZMod 2)) + symThreePolar a (symThreeDiag B) +
      ε • vecMulVec a a,
    add_mem (add_mem B.2 (symThreePolar_mem _ _))
      (symThree_smul_mem ε (MatrixExtension.vecMulVec_self_mem_binarySymMatrices a))⟩

theorem coe_symThreeRankOneSym (v : Fin 3 → ZMod 2) :
    (symThreeRankOneSym v : Matrix (Fin 3) (Fin 3) (ZMod 2)) = vecMulVec v v :=
  rfl

theorem coe_symThreeTransl (a : Fin 3 → ZMod 2) (ε : ZMod 2) (B : binarySymMatrices 3) :
    (symThreeTransl a ε B : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) + symThreePolar a (symThreeDiag B) +
        ε • vecMulVec a a :=
  rfl

theorem symThreeDiag_rankOneSym (v : Fin 3 → ZMod 2) : symThreeDiag (symThreeRankOneSym v) = v :=
  symThreeDiag_vecMulVec_self v

theorem symThreeDiag_transl (a : Fin 3 → ZMod 2) (ε : ZMod 2) (B : binarySymMatrices 3) :
    symThreeDiag (symThreeTransl a ε B) = symThreeDiag B + ε • a := by
  rw [coe_symThreeTransl, symThreeDiag_add, symThreeDiag_add, symThreeDiag_polar, add_zero,
    symThreeDiag_smul, symThreeDiag_vecMulVec_self]

theorem symThreeTransl_zero_right (a : Fin 3 → ZMod 2) :
    symThreeTransl a 1 0 = symThreeRankOneSym a := by
  apply Subtype.ext
  rw [coe_symThreeTransl, coe_symThreeRankOneSym, symThreePolar_comm, show symThreeDiag
    ((0 : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 from rfl,
    symThreePolar_zero_left]
  simp

theorem symThreeTransl_of_diag_eq_zero (a : Fin 3 → ZMod 2) {B : binarySymMatrices 3}
    (hB : symThreeDiag B = 0) : symThreeTransl a 0 B = B := by
  apply Subtype.ext
  rw [coe_symThreeTransl, hB, symThreePolar_comm, symThreePolar_zero_left]
  simp

theorem coe_symThreeTransl_zero (a : Fin 3 → ZMod 2) (B : binarySymMatrices 3) :
    (symThreeTransl a 0 B : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) + symThreePolar a (symThreeDiag B) := by
  rw [coe_symThreeTransl, zero_smul, add_zero]

theorem symThreeRankOneSym_eq_zero_iff (v : Fin 3 → ZMod 2) : symThreeRankOneSym v = 0 ↔ v = 0 := by
  rw [← vecMulVec_self_eq_zero_iff, ← coe_symThreeRankOneSym]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

@[expose] def symThreeDiagSym (v : Fin 3 → ZMod 2) : binarySymMatrices 3 :=
  ⟨diagonal v, by rw [mem_binarySymMatrices, diagonal_transpose]⟩

theorem symThreeDiag_diagSym (v : Fin 3 → ZMod 2) : symThreeDiag (symThreeDiagSym v) = v := by
  funext k
  simp [symThreeDiagSym, symThreeDiag]

theorem symThree_order_seven_fixed : ∀ L : Matrix (Fin 3) (Fin 3) (ZMod 2), L ^ 7 = 1 → L ≠ 1 →
    ∀ v : Fin 3 → ZMod 2, L *ᵥ v = v → v = 0 := by
  decide +kernel

theorem symThreeSinger_natural_cube :
    symThreeSingerMatrix *ᵥ (symThreeSingerMatrix *ᵥ (symThreeSingerMatrix *ᵥ ![1, 0, 0])) =
      ![1, 0, 0] + symThreeSingerMatrix *ᵥ ![1, 0, 0] := by
  decide

theorem symThreeSinger_natural_kill : ∀ X : Fin 3 → ZMod 2,
    symThreeSingerMatrix *ᵥ (symThreeSingerMatrix *ᵥ (symThreeSingerMatrix *ᵥ X)) +
      symThreeSingerMatrix *ᵥ (symThreeSingerMatrix *ᵥ X) + X = 0 → X = 0 := by
  decide

theorem symThreeSinger_natural_span : ∀ w : Fin 3 → ZMod 2, ∃ a b c : Bool,
    w = (if a then ![1, 0, 0] else 0) + (if b then symThreeSingerMatrix *ᵥ ![1, 0, 0] else 0) +
      (if c then symThreeSingerMatrix *ᵥ (symThreeSingerMatrix *ᵥ ![1, 0, 0]) else 0) := by
  decide

theorem symThreeSingerMatrix_pow_seven : symThreeSingerMatrix ^ 7 = 1 := by
  decide

theorem symThreeSingerMatrix_ne_one : symThreeSingerMatrix ≠ 1 := by
  decide

theorem symThreeSinger_pow_seven : symThreeSinger ^ 7 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val]; exact symThreeSingerMatrix_pow_seven)

theorem symThreeSinger_ne_one : symThreeSinger ≠ 1 := fun h =>
  symThreeSingerMatrix_ne_one (congrArg Units.val h)

end SymThreeAffineAlgebra

structure SymThreeAffineData (M : Type*) [Group M] where
  R : Subgroup M
  θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2)
  D : Subgroup M
  D_normal : D.Normal
  R_le_D : R ≤ D
  τ : M → Fin 3 → ZMod 2
  τ_mul : ∀ d ∈ D, ∀ d' ∈ D, τ (d * d') = τ d + τ d'
  τ_eq_zero : ∀ d ∈ D, τ d = 0 ↔ d ∈ R
  τ_surj : ∀ a, ∃ d ∈ D, τ d = a
  conj_D : ∀ d ∈ D, ∀ B ε, d⁻¹ * (θ.symm (.ofAdd (B, ε)) : M) * d =
    θ.symm (.ofAdd (symThreeTransl (τ d) ε B, ε))
  lin : M → GL (Fin 3) (ZMod 2)
  conj_lin : ∀ m : M, m⁻¹ * (θ.symm (.ofAdd (0, 1)) : M) * m = θ.symm (.ofAdd (0, 1)) →
    ∀ B ε, m⁻¹ * (θ.symm (.ofAdd (B, ε)) : M) * m = θ.symm (.ofAdd (symThreeCongr (lin m) B, ε))
  τ_conj : ∀ m : M, m⁻¹ * (θ.symm (.ofAdd (0, 1)) : M) * m = θ.symm (.ofAdd (0, 1)) →
    ∀ d ∈ D, τ (m⁻¹ * d * m) = (lin m : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ τ d
  lin_mul : ∀ m m' : M, m⁻¹ * (θ.symm (.ofAdd (0, 1)) : M) * m = θ.symm (.ofAdd (0, 1)) →
    m'⁻¹ * (θ.symm (.ofAdd (0, 1)) : M) * m' = θ.symm (.ofAdd (0, 1)) →
      lin (m * m') = lin m' * lin m
  lin_one : lin 1 = 1
  mem_R_of_lin : ∀ m : M, m⁻¹ * (θ.symm (.ofAdd (0, 1)) : M) * m = θ.symm (.ofAdd (0, 1)) →
    lin m = 1 → m ∈ R
  exists_lin : ∀ L, ∃ m : M, m⁻¹ * (θ.symm (.ofAdd (0, 1)) : M) * m = θ.symm (.ofAdd (0, 1)) ∧
    lin m = L
  A_normal : ∀ (m : M) (B : binarySymMatrices 3), ∃ B',
    m⁻¹ * (θ.symm (.ofAdd (B, 0)) : M) * m = θ.symm (.ofAdd (B', 0))
  I_normal : ∀ (m : M) (B : binarySymMatrices 3), symThreeDiag B = 0 →
    ∃ B' : binarySymMatrices 3, symThreeDiag B' = 0 ∧
      m⁻¹ * (θ.symm (.ofAdd (B, 0)) : M) * m = θ.symm (.ofAdd (B', 0))

namespace SymThreeAffineData

variable {M : Type*} [Group M] (S : SymThreeAffineData M)

@[expose] def e (B : binarySymMatrices 3) (ε : ZMod 2) : M := S.θ.symm (.ofAdd (B, ε))

theorem e_mul (B B' : binarySymMatrices 3) (ε ε' : ZMod 2) :
    S.e B ε * S.e B' ε' = S.e (B + B') (ε + ε') := by
  rw [e, e, e, ← Subgroup.coe_mul, ← map_mul, ← ofAdd_add, Prod.mk_add_mk]

theorem e_injective {B B' : binarySymMatrices 3} {ε ε' : ZMod 2} (h : S.e B ε = S.e B' ε') :
    B = B' ∧ ε = ε' :=
  Prod.mk.inj (Multiplicative.ofAdd.injective (S.θ.symm.injective (Subtype.ext h)))

theorem e_zero_zero : S.e 0 0 = 1 := by
  rw [e, show ((0 : binarySymMatrices 3), (0 : ZMod 2)) = 0 from rfl, ofAdd_zero, map_one,
    Subgroup.coe_one]

theorem e_eq_one {B : binarySymMatrices 3} {ε : ZMod 2} : S.e B ε = 1 ↔ B = 0 ∧ ε = 0 :=
  ⟨fun h => S.e_injective (h.trans S.e_zero_zero.symm), by
    rintro ⟨rfl, rfl⟩
    exact S.e_zero_zero⟩

theorem e_mem (B : binarySymMatrices 3) (ε : ZMod 2) : S.e B ε ∈ S.R :=
  (S.θ.symm _).2

theorem exists_e {x : M} (hx : x ∈ S.R) : ∃ B ε, x = S.e B ε :=
  ⟨(Multiplicative.toAdd (S.θ ⟨x, hx⟩)).1, (Multiplicative.toAdd (S.θ ⟨x, hx⟩)).2, by
    rw [e, Prod.mk.eta, ofAdd_toAdd, MulEquiv.symm_apply_apply]⟩

theorem e_comm (B B' : binarySymMatrices 3) (ε ε' : ZMod 2) :
    S.e B ε * S.e B' ε' = S.e B' ε' * S.e B ε := by
  rw [e_mul, e_mul, add_comm B, add_comm ε]

theorem e_mul_self (B : binarySymMatrices 3) (ε : ZMod 2) : S.e B ε * S.e B ε = 1 := by
  rw [e_mul, symThree_add_self, symThree_zmod_add_self, e_zero_zero]

theorem e_inv (B : binarySymMatrices 3) (ε : ZMod 2) : (S.e B ε)⁻¹ = S.e B ε :=
  inv_eq_of_mul_eq_one_right (S.e_mul_self B ε)

theorem e_sq (B : binarySymMatrices 3) (ε : ZMod 2) : S.e B ε ^ 2 = 1 := by
  rw [sq, e_mul_self]

theorem mem_comm {x y : M} (hx : x ∈ S.R) (hy : y ∈ S.R) : x * y = y * x := by
  obtain ⟨B, ε, rfl⟩ := S.exists_e hx
  obtain ⟨B', ε', rfl⟩ := S.exists_e hy
  exact S.e_comm B B' ε ε'

theorem sq_eq_one_of_mem_R {x : M} (hx : x ∈ S.R) : x ^ 2 = 1 := by
  obtain ⟨B, ε, rfl⟩ := S.exists_e hx
  exact S.e_sq B ε

@[expose] def z : M := S.e 0 1

theorem z_mem : S.z ∈ S.R :=
  S.e_mem 0 1

theorem z_mem_D : S.z ∈ S.D :=
  S.R_le_D S.z_mem

theorem z_inv : S.z⁻¹ = S.z :=
  S.e_inv 0 1

theorem z_sq : S.z ^ 2 = 1 :=
  S.e_sq 0 1

@[expose] def A : Subgroup M where
  carrier := {x | ∃ B, x = S.e B 0}
  mul_mem' := by
    rintro _ _ ⟨B, rfl⟩ ⟨B', rfl⟩
    exact ⟨B + B', by rw [e_mul, add_zero]⟩
  one_mem' := ⟨0, S.e_zero_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨B, rfl⟩
    exact ⟨B, S.e_inv B 0⟩

theorem e_mem_A (B : binarySymMatrices 3) : S.e B 0 ∈ S.A :=
  ⟨B, rfl⟩

@[expose] def I : Subgroup M where
  carrier := {x | ∃ B : binarySymMatrices 3, symThreeDiag B = 0 ∧ x = S.e B 0}
  mul_mem' := by
    rintro _ _ ⟨B, hB, rfl⟩ ⟨B', hB', rfl⟩
    refine ⟨B + B', ?_, by rw [e_mul, add_zero]⟩
    rw [AddSubgroup.coe_add, symThreeDiag_add, hB, hB', add_zero]
  one_mem' := ⟨0, symThreeDiag_zero, S.e_zero_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨B, hB, S.e_inv B 0⟩

theorem mem_I {x : M} : x ∈ S.I ↔ ∃ B : binarySymMatrices 3, symThreeDiag B = 0 ∧ x = S.e B 0 :=
  Iff.rfl

theorem e_mem_I_iff (B : binarySymMatrices 3) : S.e B 0 ∈ S.I ↔ symThreeDiag B = 0 := by
  constructor
  · rintro ⟨B', hB', h⟩
    rwa [(S.e_injective h).1]
  · intro h
    exact ⟨B, h, rfl⟩

theorem I_le_A : S.I ≤ S.A := by
  rintro _ ⟨B, -, rfl⟩
  exact S.e_mem_A B

theorem A_le_R : S.A ≤ S.R := by
  rintro _ ⟨B, rfl⟩
  exact S.e_mem B 0

theorem A_le_D : S.A ≤ S.D :=
  S.A_le_R.trans S.R_le_D

theorem z_not_mem_A : S.z ∉ S.A := by
  rintro ⟨B, h⟩
  exact absurd (S.e_injective h).2 (by decide)

theorem mem_A_or_of_mem_R {x : M} (hx : x ∈ S.R) : x ∈ S.A ∨ S.z⁻¹ * x ∈ S.A := by
  obtain ⟨B, ε, rfl⟩ := S.exists_e hx
  rcases MatrixExtension.zmod_two_eq_zero_or_one ε with rfl | rfl
  · exact Or.inl (S.e_mem_A B)
  · right
    rw [z_inv, z, e_mul, zero_add]
    exact S.e_mem_A B

theorem A_normal' : S.A.Normal :=
  ⟨fun n hn g => by
    obtain ⟨B, rfl⟩ := hn
    obtain ⟨B', hB'⟩ := S.A_normal g⁻¹ B
    rw [inv_inv] at hB'
    have hB'' : g * S.e B 0 * g⁻¹ = S.e B' 0 := hB'
    rw [hB'']
    exact S.e_mem_A B'⟩

theorem I_normal' : S.I.Normal :=
  ⟨fun n hn g => by
    obtain ⟨B, hB, rfl⟩ := hn
    obtain ⟨B', hB'0, hB'⟩ := S.I_normal g⁻¹ B hB
    rw [inv_inv] at hB'
    have hB'' : g * S.e B 0 * g⁻¹ = S.e B' 0 := hB'
    rw [hB'']
    exact ⟨B', hB'0, rfl⟩⟩

theorem card_R : Nat.card S.R = 128 := by
  rw [Nat.card_congr (S.θ.toEquiv.trans Multiplicative.toAdd), Nat.card_prod,
    SymThreeCosetData.card_sym, Nat.card_zmod]

theorem card_A : Nat.card S.A = 64 := by
  rw [← SymThreeCosetData.card_sym]
  refine (Nat.card_eq_of_bijective (fun B => (⟨S.e B 0, S.e_mem_A B⟩ : S.A)) ⟨?_, ?_⟩).symm
  · intro B B' h
    have h' : S.e B 0 = S.e B' 0 := congrArg (Subtype.val : S.A → M) h
    exact (S.e_injective h').1
  · rintro ⟨_, B, rfl⟩
    exact ⟨B, rfl⟩

theorem τ_one : S.τ 1 = 0 := by
  have h := S.τ_mul 1 S.D.one_mem 1 S.D.one_mem
  rw [mul_one] at h
  have h2 : S.τ 1 + S.τ 1 = 0 := by
    funext k
    exact symThree_zmod_add_self _
  rw [← h] at h2
  exact h2

theorem τ_inv {d : M} (hd : d ∈ S.D) : S.τ d⁻¹ = S.τ d := by
  have h := S.τ_mul d hd d⁻¹ (inv_mem hd)
  rw [mul_inv_cancel, τ_one] at h
  funext k
  have hk := congrFun h k
  simp only [Pi.add_apply, Pi.zero_apply] at hk
  have := symThree_zmod_add_self (S.τ d k)
  grind

theorem τ_of_mem_R {r : M} (hr : r ∈ S.R) : S.τ r = 0 :=
  (S.τ_eq_zero r (S.R_le_D hr)).2 hr

theorem τ_eq_iff {x y : M} (hx : x ∈ S.D) (hy : y ∈ S.D) : S.τ x = S.τ y ↔ x⁻¹ * y ∈ S.R := by
  rw [← S.τ_eq_zero _ (mul_mem (inv_mem hx) hy), S.τ_mul _ (inv_mem hx) _ hy, S.τ_inv hx]
  constructor
  · intro h
    rw [h]
    funext k
    exact symThree_zmod_add_self _
  · intro h
    funext k
    have hk := congrFun h k
    simp only [Pi.add_apply, Pi.zero_apply] at hk
    have := symThree_zmod_add_self (S.τ y k)
    grind

theorem τ_eq_iff' {x y : M} (hx : x ∈ S.D) (hy : y ∈ S.D) :
    S.τ x = S.τ y ↔ y * x⁻¹ ∈ S.R := by
  rw [← S.τ_eq_zero _ (mul_mem hy (inv_mem hx)), S.τ_mul _ hy _ (inv_mem hx), S.τ_inv hx]
  constructor
  · intro h
    rw [h]
    funext k
    exact symThree_zmod_add_self _
  · intro h
    funext k
    have hk := congrFun h k
    simp only [Pi.add_apply, Pi.zero_apply] at hk
    have := symThree_zmod_add_self (S.τ y k)
    grind

theorem τ_z : S.τ S.z = 0 :=
  S.τ_of_mem_R S.z_mem

theorem conj_e_D {d : M} (hd : d ∈ S.D) (B : binarySymMatrices 3) (ε : ZMod 2) :
    d⁻¹ * S.e B ε * d = S.e (symThreeTransl (S.τ d) ε B) ε :=
  S.conj_D d hd B ε

theorem conj_z_D {d : M} (hd : d ∈ S.D) : d⁻¹ * S.z * d = S.e (symThreeRankOneSym (S.τ d)) 1 := by
  rw [z, S.conj_e_D hd, symThreeTransl_zero_right]

theorem commutatorElement_z {d : M} (hd : d ∈ S.D) :
    ⁅S.z, d⁆ = S.e (symThreeRankOneSym (S.τ d)) 0 := by
  have h : ⁅S.z, d⁆ = S.z * ((d⁻¹)⁻¹ * S.z * d⁻¹) := by
    rw [commutatorElement_def, inv_inv, S.z_inv]
    group
  rw [h, S.conj_z_D (inv_mem hd), S.τ_inv hd, z, e_mul, zero_add]
  rfl

theorem sq_mem_R {d : M} (hd : d ∈ S.D) : d ^ 2 ∈ S.R := by
  rw [← S.τ_eq_zero _ (by rw [sq]; exact mul_mem hd hd), sq, S.τ_mul _ hd _ hd]
  funext k
  exact symThree_zmod_add_self _

theorem sq_mem_A {d : M} (hd : d ∈ S.D) : d ^ 2 ∈ S.A := by
  obtain ⟨B, ε, hB⟩ := S.exists_e (S.sq_mem_R hd)
  rcases MatrixExtension.zmod_two_eq_zero_or_one ε with rfl | rfl
  · exact ⟨B, hB⟩
  · exfalso
    have hcomm : d⁻¹ * d ^ 2 * d = d ^ 2 := by group
    rw [hB, S.conj_e_D hd] at hcomm
    have h := congrArg symThreeDiag (congrArg Subtype.val (S.e_injective hcomm).1)
    rw [symThreeDiag_transl, one_smul] at h
    have h0 : S.τ d = 0 := add_eq_left.mp h
    obtain ⟨B', ε', hd'⟩ := S.exists_e ((S.τ_eq_zero d hd).1 h0)
    rw [hd', e_sq] at hB
    exact absurd (S.e_injective (hB.symm.trans S.e_zero_zero.symm)).2 (by decide)

theorem commutatorElement_mem_A {x y : M} (hx : x ∈ S.D) (hy : y ∈ S.D) : ⁅x, y⁆ ∈ S.A := by
  rw [symThree_commutatorElement_eq_sq]
  exact mul_mem (mul_mem (S.sq_mem_A (mul_mem hx hy))
    (S.sq_mem_A (mul_mem (mul_mem (inv_mem hy) (inv_mem hx)) hy))) (S.sq_mem_A (inv_mem hy))

theorem conj_A_D {d : M} (hd : d ∈ S.D) (B : binarySymMatrices 3) :
    d⁻¹ * S.e B 0 * d = S.e (symThreeTransl (S.τ d) 0 B) 0 :=
  S.conj_e_D hd B 0

theorem conj_I_D {d : M} (hd : d ∈ S.D) {x : M} (hx : x ∈ S.I) : d⁻¹ * x * d = x := by
  obtain ⟨B, hB, rfl⟩ := hx
  rw [S.conj_A_D hd, symThreeTransl_of_diag_eq_zero _ hB]

theorem commute_I_D {d : M} (hd : d ∈ S.D) {x : M} (hx : x ∈ S.I) : d * x = x * d := by
  have h := S.conj_I_D hd hx
  calc d * x = d * (d⁻¹ * x * d) := by rw [h]
    _ = x * d := by group

theorem I_le_D : S.I ≤ S.D :=
  S.I_le_A.trans S.A_le_D

include S in
theorem card_D : Nat.card S.D = 1024 := by
  have h := symThree_card_eq_card_image_mul S.R_le_D S.τ (fun x hx y hy => S.τ_eq_iff hx hy)
  have himage : S.τ '' (S.D : Set M) = Set.univ :=
    Set.eq_univ_of_forall fun a => by
      obtain ⟨d, hd, rfl⟩ := S.τ_surj a
      exact ⟨d, hd, rfl⟩
  rw [himage, Nat.card_univ, S.card_R] at h
  rw [h]
  simp

open Classical in
@[expose] noncomputable def lab (x : M) : binarySymMatrices 3 :=
  if h : x ∈ S.R then (Multiplicative.toAdd (S.θ ⟨x, h⟩)).1 else 0

theorem lab_e (B : binarySymMatrices 3) (ε : ZMod 2) : S.lab (S.e B ε) = B := by
  have h : (⟨S.e B ε, S.e_mem B ε⟩ : S.R) = S.θ.symm (.ofAdd (B, ε)) := rfl
  rw [lab, dite_eq_left (S.e_mem B ε), h, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem eq_e_lab {x : M} (hx : x ∈ S.A) : x = S.e (S.lab x) 0 := by
  obtain ⟨B, rfl⟩ := hx
  rw [lab_e]

theorem lab_mul {x y : M} (hx : x ∈ S.A) (hy : y ∈ S.A) : S.lab (x * y) = S.lab x + S.lab y := by
  rw [S.eq_e_lab hx, S.eq_e_lab hy, e_mul, lab_e, lab_e, lab_e]

theorem lab_inv {x : M} (hx : x ∈ S.A) : S.lab x⁻¹ = S.lab x := by
  rw [S.eq_e_lab hx, e_inv, lab_e]

theorem lab_one : S.lab 1 = 0 := by
  rw [← S.e_zero_zero, lab_e]

theorem diag_lab_conj {d x : M} (hd : d ∈ S.D) (hx : x ∈ S.A) :
    symThreeDiag (S.lab (d⁻¹ * x * d)) = symThreeDiag (S.lab x) := by
  rw [S.eq_e_lab hx, S.conj_A_D hd, lab_e, lab_e, symThreeDiag_transl, zero_smul, add_zero]

theorem diag_lab_conj' {d x : M} (hd : d ∈ S.D) (hx : x ∈ S.A) :
    symThreeDiag (S.lab (d * x * d⁻¹)) = symThreeDiag (S.lab x) := by
  have h := S.diag_lab_conj (inv_mem hd) hx
  rwa [inv_inv] at h

@[expose] noncomputable def κ (x y : M) : Fin 3 → ZMod 2 :=
  symThreeDiag (S.lab ⁅x, y⁆)

theorem κ_mul_right {x y w : M} (hx : x ∈ S.D) (hy : y ∈ S.D) (hw : w ∈ S.D) :
    S.κ x (y * w) = S.κ x y + S.κ x w := by
  have h : ⁅x, y * w⁆ = ⁅x, y⁆ * (y * ⁅x, w⁆ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hA1 := S.commutatorElement_mem_A hx hy
  have hA2 := S.commutatorElement_mem_A hx hw
  have hA3 : y * ⁅x, w⁆ * y⁻¹ ∈ S.A := by
    have := S.A_normal'.conj_mem _ hA2 y
    exact this
  rw [κ, h, S.lab_mul hA1 hA3, AddSubgroup.coe_add, symThreeDiag_add, S.diag_lab_conj' hy hA2]
  rfl

theorem κ_comm {x y : M} (hx : x ∈ S.D) (hy : y ∈ S.D) : S.κ y x = S.κ x y := by
  rw [κ, κ, ← commutatorElement_inv, S.lab_inv (S.commutatorElement_mem_A hx hy)]

theorem κ_self (x : M) : S.κ x x = 0 := by
  rw [κ, commutatorElement_self, lab_one]
  rfl

theorem κ_of_mem_A {x a : M} (hx : x ∈ S.D) (ha : a ∈ S.A) : S.κ x a = 0 := by
  have h : ⁅x, a⁆ = (x * a * x⁻¹) * a⁻¹ := by
    rw [commutatorElement_def]
  have hA : x * a * x⁻¹ ∈ S.A := S.A_normal'.conj_mem _ ha x
  rw [κ, h, S.lab_mul hA (inv_mem ha), AddSubgroup.coe_add, symThreeDiag_add,
    S.diag_lab_conj' hx ha, S.lab_inv ha]
  funext k
  exact symThree_zmod_add_self _

theorem κ_eq_zero_iff {x y : M} (hx : x ∈ S.D) (hy : y ∈ S.D) : S.κ x y = 0 ↔ ⁅x, y⁆ ∈ S.I := by
  have h := S.eq_e_lab (S.commutatorElement_mem_A hx hy)
  rw [κ]
  conv_rhs => rw [h]
  rw [e_mem_I_iff]

theorem κ_z {d : M} (hd : d ∈ S.D) : S.κ S.z d = S.τ d := by
  rw [κ, S.commutatorElement_z hd, lab_e, symThreeDiag_rankOneSym]

theorem κ_conj {m x y : M} (hm : m⁻¹ * S.z * m = S.z) (hx : x ∈ S.D) (hy : y ∈ S.D) :
    S.κ (m⁻¹ * x * m) (m⁻¹ * y * m) =
      (S.lin m : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ S.κ x y := by
  have h : ⁅m⁻¹ * x * m, m⁻¹ * y * m⁆ = m⁻¹ * ⁅x, y⁆ * m := by
    simp only [commutatorElement_def]
    group
  have hA := S.commutatorElement_mem_A hx hy
  have h2 : m⁻¹ * ⁅x, y⁆ * m = S.e (symThreeCongr (S.lin m) (S.lab ⁅x, y⁆)) 0 := by
    conv_lhs => rw [S.eq_e_lab hA]
    exact S.conj_lin m hm _ 0
  rw [κ, κ, h, h2, lab_e]
  exact symThreeDiag_coe_congr _ _

theorem exists_singer : ∃ m : M, m⁻¹ * S.z * m = S.z ∧ S.lin m = symThreeSinger :=
  S.exists_lin symThreeSinger

@[expose] noncomputable def m₀ : M :=
  Classical.choose S.exists_singer

theorem m₀_fix : S.m₀⁻¹ * S.z * S.m₀ = S.z :=
  (Classical.choose_spec S.exists_singer).1

theorem lin_m₀ : S.lin S.m₀ = symThreeSinger :=
  (Classical.choose_spec S.exists_singer).2

@[expose] noncomputable def φ : MulAut M :=
  MulAut.conj S.m₀⁻¹

theorem φ_apply (x : M) : S.φ x = S.m₀⁻¹ * x * S.m₀ := by
  rw [φ, MulAut.conj_apply, inv_inv]

theorem φ_z : S.φ S.z = S.z := by
  rw [φ_apply, S.m₀_fix]

theorem φ_mem_D {x : M} (hx : x ∈ S.D) : S.φ x ∈ S.D := by
  rw [φ_apply]
  have := S.D_normal.conj_mem x hx S.m₀⁻¹
  rwa [inv_inv] at this

theorem τ_φ {x : M} (hx : x ∈ S.D) : S.τ (S.φ x) = symThreeSingerMatrix *ᵥ S.τ x := by
  rw [φ_apply, S.τ_conj _ S.m₀_fix x hx, S.lin_m₀]
  rfl

theorem κ_φ {x y : M} (hx : x ∈ S.D) (hy : y ∈ S.D) :
    S.κ (S.φ x) (S.φ y) = symThreeSingerMatrix *ᵥ S.κ x y := by
  rw [φ_apply, φ_apply, S.κ_conj S.m₀_fix hx hy, S.lin_m₀]
  rfl

theorem exists_coherent : ∃ d₀ ∈ S.D, S.τ d₀ = ![1, 0, 0] ∧
    (d₀ * S.φ d₀)⁻¹ * S.φ (S.φ (S.φ d₀)) ∈ S.A := by
  obtain ⟨f, hf, hfτ⟩ := S.τ_surj ![1, 0, 0]
  have h1 := S.φ_mem_D hf
  have h3 := S.φ_mem_D (S.φ_mem_D h1)
  have hr : (f * S.φ f)⁻¹ * S.φ (S.φ (S.φ f)) ∈ S.R := by
    rw [← S.τ_eq_iff (mul_mem hf h1) h3, S.τ_mul _ hf _ h1, S.τ_φ (S.φ_mem_D h1),
      S.τ_φ h1, S.τ_φ hf, hfτ]
    exact symThreeSinger_natural_cube.symm
  rcases S.mem_A_or_of_mem_R hr with h | h
  · exact ⟨f, hf, hfτ, h⟩
  · refine ⟨f * S.z, mul_mem hf S.z_mem_D, by rw [S.τ_mul _ hf _ S.z_mem_D, S.τ_z, add_zero,
      hfτ], ?_⟩
    rw [map_mul, map_mul, map_mul, φ_z, φ_z, φ_z]
    have key : (f * S.z * (S.φ f * S.z))⁻¹ * (S.φ (S.φ (S.φ f)) * S.z) =
        S.z⁻¹ * (⁅(S.φ f)⁻¹, S.z⁻¹⁆ *
          (S.z⁻¹ * ((f * S.φ f)⁻¹ * S.φ (S.φ (S.φ f))))) * S.z := by
      rw [commutatorElement_def]
      group
    have hc : ⁅(S.φ f)⁻¹, S.z⁻¹⁆ * (S.z⁻¹ * ((f * S.φ f)⁻¹ * S.φ (S.φ (S.φ f)))) ∈ S.A :=
      mul_mem (S.commutatorElement_mem_A (inv_mem h1) (inv_mem S.z_mem_D)) h
    rw [key, mul_assoc, S.mem_comm (S.A_le_R hc) S.z_mem, ← mul_assoc, inv_mul_cancel,
      one_mul]
    exact hc

@[expose] noncomputable def d₀ : M :=
  Classical.choose S.exists_coherent

theorem d₀_mem : S.d₀ ∈ S.D :=
  (Classical.choose_spec S.exists_coherent).1

theorem τ_d₀ : S.τ S.d₀ = ![1, 0, 0] :=
  (Classical.choose_spec S.exists_coherent).2.1

theorem d₀_coherent : (S.d₀ * S.φ S.d₀)⁻¹ * S.φ (S.φ (S.φ S.d₀)) ∈ S.A :=
  (Classical.choose_spec S.exists_coherent).2.2

theorem κ_orbit : S.κ S.d₀ (S.φ S.d₀) = 0 ∧ S.κ S.d₀ (S.φ (S.φ S.d₀)) = 0 ∧
    S.κ (S.φ S.d₀) (S.φ (S.φ S.d₀)) = 0 := by
  have h0 := S.d₀_mem
  have h1 := S.φ_mem_D h0
  have h2 := S.φ_mem_D h1
  have ha := S.d₀_coherent
  have haD := S.A_le_D ha
  have h3 : S.φ (S.φ (S.φ S.d₀)) =
      S.d₀ * S.φ S.d₀ * ((S.d₀ * S.φ S.d₀)⁻¹ * S.φ (S.φ (S.φ S.d₀))) := by
    group
  have hE1 : symThreeSingerMatrix *ᵥ S.κ S.d₀ (S.φ (S.φ S.d₀)) = S.κ S.d₀ (S.φ S.d₀) := by
    rw [← S.κ_φ h0 h2, h3, S.κ_mul_right h1 (mul_mem h0 h1) haD, S.κ_of_mem_A h1 ha, add_zero,
      S.κ_mul_right h1 h0 h1, S.κ_self, add_zero, S.κ_comm h0 h1]
  have hE2 : symThreeSingerMatrix *ᵥ (symThreeSingerMatrix *ᵥ S.κ S.d₀ (S.φ S.d₀)) =
      S.κ S.d₀ (S.φ (S.φ S.d₀)) + symThreeSingerMatrix *ᵥ S.κ S.d₀ (S.φ S.d₀) := by
    rw [← S.κ_φ h0 h1, ← S.κ_φ h1 h2, h3, S.κ_mul_right h2 (mul_mem h0 h1) haD,
      S.κ_of_mem_A h2 ha, add_zero, S.κ_mul_right h2 h0 h1, S.κ_comm h0 h2, S.κ_comm h1 h2,
      S.κ_φ h0 h1]
  have hX : S.κ S.d₀ (S.φ S.d₀) = 0 := by
    apply symThreeSinger_natural_kill
    simp only [hE2, mulVec_add, hE1]
    funext k
    simp only [Pi.add_apply, Pi.zero_apply]
    grind
  have hY : S.κ S.d₀ (S.φ (S.φ S.d₀)) = 0 := by
    have h := hE2
    rw [hX, mulVec_zero, mulVec_zero, add_zero] at h
    exact h.symm
  refine ⟨hX, hY, ?_⟩
  rw [S.κ_φ h0 h1, hX, mulVec_zero]

@[expose] noncomputable def gens : Set M :=
  (S.A : Set M) ∪ {S.d₀, S.φ S.d₀, S.φ (S.φ S.d₀)}

@[expose] noncomputable def C : Subgroup M :=
  Subgroup.closure S.gens

theorem gens_subset_D : S.gens ⊆ S.D := by
  rintro x (hx | hx | hx | hx)
  · exact S.A_le_D hx
  · rw [hx]
    exact S.d₀_mem
  · rw [hx]
    exact S.φ_mem_D S.d₀_mem
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact S.φ_mem_D (S.φ_mem_D S.d₀_mem)

theorem κ_gens {p q : M} (hp : p ∈ S.gens) (hq : q ∈ S.gens) : S.κ p q = 0 := by
  obtain ⟨h01, h02, h12⟩ := S.κ_orbit
  have hpD := S.gens_subset_D hp
  have hqD := S.gens_subset_D hq
  rcases hp with hp | hp | hp | hp
  · rw [← S.κ_comm hpD hqD]
    exact S.κ_of_mem_A hqD hp
  · rcases hq with hq | hq | hq | hq
    · exact S.κ_of_mem_A hpD hq
    · rw [hp, hq, κ_self]
    · rw [hp, hq]
      exact h01
    · rw [Set.mem_singleton_iff] at hq
      rw [hp, hq]
      exact h02
  · rcases hq with hq | hq | hq | hq
    · exact S.κ_of_mem_A hpD hq
    · rw [hp, hq, S.κ_comm S.d₀_mem (S.φ_mem_D S.d₀_mem)]
      exact h01
    · rw [hp, hq, κ_self]
    · rw [Set.mem_singleton_iff] at hq
      rw [hp, hq]
      exact h12
  · rw [Set.mem_singleton_iff] at hp
    rcases hq with hq | hq | hq | hq
    · exact S.κ_of_mem_A hpD hq
    · rw [hp, hq, S.κ_comm S.d₀_mem (S.φ_mem_D (S.φ_mem_D S.d₀_mem))]
      exact h02
    · rw [hp, hq, S.κ_comm (S.φ_mem_D S.d₀_mem) (S.φ_mem_D (S.φ_mem_D S.d₀_mem))]
      exact h12
    · rw [Set.mem_singleton_iff] at hq
      rw [hp, hq, κ_self]

theorem C_le_D : S.C ≤ S.D :=
  (Subgroup.closure_le _).2 S.gens_subset_D

theorem A_le_C : S.A ≤ S.C :=
  fun _ ha => Subgroup.subset_closure (Or.inl ha)

theorem I_le_C : S.I ≤ S.C :=
  S.I_le_A.trans S.A_le_C

theorem d₀_mem_C : S.d₀ ∈ S.C :=
  Subgroup.subset_closure (Or.inr (Or.inl rfl))

theorem φd₀_mem_C : S.φ S.d₀ ∈ S.C :=
  Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))

theorem φφd₀_mem_C : S.φ (S.φ S.d₀) ∈ S.C :=
  Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))

theorem commutator_mem_I {x y : M} (hx : x ∈ S.C) (hy : y ∈ S.C) : ⁅x, y⁆ ∈ S.I := by
  have := S.I_normal'
  have hpair : (QuotientGroup.mk' S.I '' S.gens).Pairwise Commute := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ -
    apply commutatorElement_eq_one_iff_commute.1
    rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (S.κ_eq_zero_iff (S.gens_subset_D hp) (S.gens_subset_D hq)).1 (S.κ_gens hp hq)
  have hcomm := Subgroup.isMulCommutative_closure hpair
  have hmap : S.C.map (QuotientGroup.mk' S.I) =
      Subgroup.closure (QuotientGroup.mk' S.I '' S.gens) :=
    MonoidHom.map_closure _ _
  have hx' : QuotientGroup.mk' S.I x ∈ Subgroup.closure (QuotientGroup.mk' S.I '' S.gens) :=
    hmap ▸ Subgroup.mem_map_of_mem _ hx
  have hy' : QuotientGroup.mk' S.I y ∈ Subgroup.closure (QuotientGroup.mk' S.I '' S.gens) :=
    hmap ▸ Subgroup.mem_map_of_mem _ hy
  have h1 : QuotientGroup.mk' S.I ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact setLike_mul_comm hx' hy'
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1

theorem z_not_mem_C : S.z ∉ S.C := by
  intro hz
  have h := (S.κ_eq_zero_iff S.z_mem_D S.d₀_mem).2 (S.commutator_mem_I hz S.d₀_mem_C)
  rw [S.κ_z S.d₀_mem, S.τ_d₀] at h
  exact absurd (congrFun h 0) (by decide)

theorem mem_A_of_mem_C_R {x : M} (hx : x ∈ S.C) (hxR : x ∈ S.R) : x ∈ S.A := by
  rcases S.mem_A_or_of_mem_R hxR with h | h
  · exact h
  · exfalso
    apply S.z_not_mem_C
    have := mul_mem hx (inv_mem (S.A_le_C h))
    rwa [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at this

theorem C_inf_R : S.C ⊓ S.R = S.A :=
  le_antisymm (fun _ hx => S.mem_A_of_mem_C_R (Subgroup.mem_inf.1 hx).1 (Subgroup.mem_inf.1 hx).2)
    (le_inf S.A_le_C S.A_le_R)

theorem exists_mem_C_τ (a : Fin 3 → ZMod 2) : ∃ c ∈ S.C, S.τ c = a := by
  obtain ⟨b₀, b₁, b₂, hab⟩ := symThreeSinger_natural_span a
  have hif : ∀ (b : Bool) {x : M}, x ∈ S.C → (if b then x else 1) ∈ S.C := by
    intro b x hx
    split_ifs
    · exact hx
    · exact S.C.one_mem
  have hτif : ∀ (b : Bool) {x : M} (v : Fin 3 → ZMod 2), S.τ x = v →
      S.τ (if b then x else 1) = if b then v else 0 := by
    intro b x v hv
    split_ifs
    · exact hv
    · exact S.τ_one
  refine ⟨(if b₀ then S.d₀ else 1) * (if b₁ then S.φ S.d₀ else 1) *
    (if b₂ then S.φ (S.φ S.d₀) else 1), mul_mem (mul_mem (hif _ S.d₀_mem_C) (hif _ S.φd₀_mem_C))
      (hif _ S.φφd₀_mem_C), ?_⟩
  rw [S.τ_mul _ (S.C_le_D (mul_mem (hif _ S.d₀_mem_C) (hif _ S.φd₀_mem_C))) _
      (S.C_le_D (hif _ S.φφd₀_mem_C)),
    S.τ_mul _ (S.C_le_D (hif _ S.d₀_mem_C)) _ (S.C_le_D (hif _ S.φd₀_mem_C)),
    hτif b₀ _ S.τ_d₀, hτif b₁ _ (by rw [S.τ_φ S.d₀_mem, S.τ_d₀]),
    hτif b₂ _ (by rw [S.τ_φ (S.φ_mem_D S.d₀_mem), S.τ_φ S.d₀_mem, S.τ_d₀]), hab]

theorem card_C : Nat.card S.C = 512 := by
  have h := symThree_card_eq_card_image_mul S.A_le_C S.τ (fun x hx y hy => by
    rw [S.τ_eq_iff (S.C_le_D hx) (S.C_le_D hy)]
    exact ⟨fun h => S.mem_A_of_mem_C_R (mul_mem (inv_mem hx) hy) h, fun h => S.A_le_R h⟩)
  have himage : S.τ '' (S.C : Set M) = Set.univ :=
    Set.eq_univ_of_forall fun a => by
      obtain ⟨c, hc, hcτ⟩ := S.exists_mem_C_τ a
      exact ⟨c, hc, hcτ⟩
  rw [himage, Nat.card_univ, S.card_A] at h
  rw [h]
  simp

theorem mem_C_or {d : M} (hd : d ∈ S.D) : d ∈ S.C ∨ S.z⁻¹ * d ∈ S.C := by
  obtain ⟨c, hc, hcτ⟩ := S.exists_mem_C_τ (S.τ d)
  have hR : d * c⁻¹ ∈ S.R := (S.τ_eq_iff' (S.C_le_D hc) hd).1 hcτ
  rcases S.mem_A_or_of_mem_R hR with h | h
  · left
    have := mul_mem (S.A_le_C h) hc
    rwa [inv_mul_cancel_right] at this
  · right
    have := mul_mem (S.A_le_C h) hc
    rwa [mul_assoc, inv_mul_cancel_right] at this

theorem D_eq_RC : (S.D : Set M) = (S.R : Set M) * (S.C : Set M) := by
  ext d
  rw [Set.mem_mul]
  constructor
  · intro hd
    rcases S.mem_C_or hd with h | h
    · exact ⟨1, S.R.one_mem, d, h, one_mul d⟩
    · exact ⟨S.z, S.z_mem, S.z⁻¹ * d, h, mul_inv_cancel_left _ _⟩
  · rintro ⟨r, hr, c, hc, rfl⟩
    exact mul_mem (S.R_le_D hr) (S.C_le_D hc)

theorem relIndex_C_D : S.C.relIndex S.D = 2 := by
  have h := Subgroup.card_mul_index (S.C.subgroupOf S.D)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.C_le_D).toEquiv, S.card_C, S.card_D] at h
  change 512 * S.C.relIndex S.D = 1024 at h
  omega

theorem diag_eq_zero_of_polar {u : Fin 3 → ZMod 2} (h : ∀ v, symThreePolar v u = 0) : u = 0 := by
  by_contra hu
  obtain ⟨v, hv⟩ := symThreeDiag_polar_ne u hu
  exact hv (by rw [symThreePolar_comm]; exact h v)

theorem center_D : (Subgroup.center S.D).map S.D.subtype = S.I := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hx
    have hcz : (x : M)⁻¹ * S.z * x = S.z := by
      have h := congrArg Subtype.val (hx ⟨S.z, S.z_mem_D⟩)
      change S.z * (x : M) = x * S.z at h
      rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [S.conj_z_D x.2] at hcz
    have h0 : S.τ x = 0 := (symThreeRankOneSym_eq_zero_iff _).1 (S.e_injective hcz).1
    obtain ⟨B, ε, hBε⟩ := S.exists_e ((S.τ_eq_zero x x.2).1 h0)
    have hfix : ∀ a, symThreeTransl a ε B = B := by
      intro a
      obtain ⟨d, hd, rfl⟩ := S.τ_surj a
      have h := congrArg Subtype.val (hx ⟨d, hd⟩)
      change d * (x : M) = x * d at h
      have h' : d⁻¹ * (x : M) * d = x := by
        rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hBε, S.conj_e_D hd] at h'
      exact (S.e_injective h').1
    have hε : ε = 0 := by
      have h := congrArg symThreeDiag (congrArg Subtype.val (hfix ![1, 0, 0]))
      rw [symThreeDiag_transl] at h
      have h' := congrFun (add_eq_left.mp h) 0
      simpa using h'
    subst hε
    have hB : symThreeDiag B = 0 := by
      apply diag_eq_zero_of_polar
      intro v
      have h := congrArg Subtype.val (hfix v)
      rw [coe_symThreeTransl, zero_smul, add_zero] at h
      exact add_eq_left.mp h
    change (x : M) ∈ S.I
    rw [hBε]
    exact ⟨B, hB, rfl⟩
  · intro x hx
    refine ⟨⟨x, S.I_le_D hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro d
    exact Subtype.ext (S.commute_I_D d.2 hx)

@[expose] def IsCanonical (X : Subgroup M) : Prop :=
  X ≤ S.D ∧ S.I ≤ X ∧ (∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ S.I) ∧ Nat.card X = 512

theorem C_isCanonical : S.IsCanonical S.C :=
  ⟨S.C_le_D, S.I_le_C, fun _ hx _ hy => S.commutator_mem_I hx hy, S.card_C⟩

theorem eq_C_of_isCanonical {X : Subgroup M} (hX : S.IsCanonical X) : X = S.C := by
  have hfinC : Finite S.C := Nat.finite_of_card_ne_zero (by rw [S.card_C]; norm_num)
  by_contra hne
  have hXC : ¬ X ≤ S.C := fun h => hne (Subgroup.eq_of_le_of_card_ge h (by
    rw [hX.2.2.2, S.card_C]))
  obtain ⟨x, hxX, hxC⟩ := Set.not_subset.1 hXC
  have hzx : S.z⁻¹ * x ∈ S.C := (S.mem_C_or (hX.1 hxX)).resolve_left hxC
  have hinf : ∀ y, y ∈ X → y ∈ S.C → y ∈ S.A := by
    intro y hyX hyC
    have h1 : ⁅x, y⁆ ∈ S.I := hX.2.2.1 x hxX y hyX
    have h2 : ⁅S.z⁻¹ * x, y⁆ ∈ S.I := S.commutator_mem_I hzx hyC
    have h3 : ⁅S.z, y⁆ ∈ S.I := by
      have hid : ⁅S.z, y⁆ = (S.z * ⁅S.z⁻¹ * x, y⁆ * S.z⁻¹)⁻¹ * ⁅x, y⁆ := by
        simp only [commutatorElement_def]
        group
      rw [hid]
      exact mul_mem (inv_mem (S.I_normal'.conj_mem _ h2 S.z)) h1
    have hyD := S.C_le_D hyC
    have h4 := (S.κ_eq_zero_iff S.z_mem_D hyD).2 h3
    rw [S.κ_z hyD] at h4
    exact S.mem_A_of_mem_C_R hyC ((S.τ_eq_zero y hyD).1 h4)
  have hfinA : Finite S.A := Nat.finite_of_card_ne_zero (by rw [S.card_A]; norm_num)
  have h1 : Nat.card (S.C.subgroupOf X) ≤ 64 := by
    rw [← S.card_A]
    exact Nat.card_le_card_of_injective (fun c => (⟨c.1.1, hinf _ c.1.2 c.2⟩ : S.A))
      (fun c c' hcc => by
        have h' : c.1.1 = c'.1.1 := congrArg (Subtype.val : S.A → M) hcc
        exact Subtype.ext (Subtype.ext h'))
  have h2 : S.C.relIndex X ≤ 2 := by
    rw [← S.relIndex_C_D]
    exact Subgroup.relIndex_le_of_le_right hX.1 (by rw [S.relIndex_C_D]; norm_num)
  have h3 := Subgroup.card_mul_index (S.C.subgroupOf X)
  rw [hX.2.2.2] at h3
  change Nat.card (S.C.subgroupOf X) * S.C.relIndex X = 512 at h3
  have : Nat.card (S.C.subgroupOf X) * S.C.relIndex X ≤ 64 * 2 := Nat.mul_le_mul h1 h2
  omega

theorem isCanonical_map_conj (g : M) : S.IsCanonical (S.C.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact S.D_normal.conj_mem c (S.C_le_D hc) g
  · intro x hx
    refine ⟨g⁻¹ * x * g, S.I_le_C ?_, ?_⟩
    · have := S.I_normal'.conj_mem x hx g⁻¹
      rwa [inv_inv] at this
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
    change ⁅g * c * g⁻¹, g * c' * g⁻¹⁆ ∈ S.I
    have h : ⁅g * c * g⁻¹, g * c' * g⁻¹⁆ = g * ⁅c, c'⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact S.I_normal'.conj_mem _ (S.commutator_mem_I hc hc') g
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, S.card_C]

theorem C_normal : S.C.Normal :=
  ⟨fun c hc g => by
    rw [← S.eq_C_of_isCanonical (S.isCanonical_map_conj g)]
    exact ⟨c, hc, rfl⟩⟩

theorem C_characteristic : (S.C.subgroupOf S.D).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro ψ
  have hcen : ∀ (χ : S.D ≃* S.D) (x : S.D), x ∈ Subgroup.center S.D →
      χ x ∈ Subgroup.center S.D := by
    intro χ x hx
    have h := Subgroup.characteristic_iff_map_eq.1 (inferInstance :
      (Subgroup.center S.D).Characteristic) χ
    rw [← h]
    exact ⟨x, hx, rfl⟩
  have hI : ∀ x : S.D, (x : M) ∈ S.I ↔ x ∈ Subgroup.center S.D := by
    intro x
    rw [← S.center_D]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hX : S.IsCanonical (((S.C.subgroupOf S.D).map ψ.toMonoidHom).map S.D.subtype) := by
    refine ⟨Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
    · intro x hx
      have hxc : (⟨x, S.I_le_D hx⟩ : S.D) ∈ Subgroup.center S.D := (hI _).1 hx
      refine ⟨ψ (ψ.symm ⟨x, S.I_le_D hx⟩), ⟨ψ.symm ⟨x, S.I_le_D hx⟩, ?_, rfl⟩, ?_⟩
      · exact S.I_le_C ((hI _).2 (hcen ψ.symm _ hxc))
      · rw [MulEquiv.apply_symm_apply]
        rfl
    · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩ _ ⟨_, ⟨c', hc', rfl⟩, rfl⟩
      have h := S.commutator_mem_I hc hc'
      have h' : ⁅c, c'⁆ ∈ Subgroup.center S.D := (hI _).1 h
      have h'' := (hI _).2 (hcen ψ _ h')
      rw [map_commutatorElement] at h''
      exact h''
    · rw [Subgroup.card_map_of_injective S.D.subtype_injective,
        Subgroup.card_map_of_injective ψ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.C_le_D).toEquiv, S.card_C]
  have h := S.eq_C_of_isCanonical hX
  have h2 := congrArg (Subgroup.comap S.D.subtype) h
  rw [Subgroup.comap_map_eq_self_of_injective S.D.subtype_injective] at h2
  exact h2

theorem e_add_zero (X Y : binarySymMatrices 3) : S.e (X + Y) 0 = S.e X 0 * S.e Y 0 := by
  rw [e_mul, add_zero]

theorem conj_I_C {c x : M} (hc : c ∈ S.C) (hx : x ∈ S.I) : c * x * c⁻¹ = x := by
  rw [S.commute_I_D (S.C_le_D hc) hx, mul_inv_cancel_right]

theorem center_C : (Subgroup.center S.C).map S.C.subtype = S.I := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hx
    have hconj : ∀ c ∈ S.C, c⁻¹ * (x : M) * c = x := by
      intro c hc
      have h := congrArg Subtype.val (hx ⟨c, hc⟩)
      change c * (x : M) = x * c at h
      rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
    have hxD := S.C_le_D x.2
    have hτ : S.τ x = 0 := by
      by_contra hw
      obtain ⟨v, hv⟩ := symThreeDiag_polar_ne _ hw
      have hcomm : (x : M) * S.e (symThreeDiagSym v) 0 = S.e (symThreeDiagSym v) 0 * x :=
        congrArg Subtype.val (hx ⟨_, S.A_le_C (S.e_mem_A (symThreeDiagSym v))⟩).symm
      have h' : (x : M)⁻¹ * S.e (symThreeDiagSym v) 0 * x = S.e (symThreeDiagSym v) 0 := by
        rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [S.conj_A_D hxD] at h'
      have h'' := congrArg Subtype.val (S.e_injective h').1
      rw [coe_symThreeTransl_zero, symThreeDiag_diagSym] at h''
      exact hv (add_eq_left.mp h'')
    obtain ⟨B, hB⟩ := S.mem_A_of_mem_C_R x.2 ((S.τ_eq_zero x hxD).1 hτ)
    have hBd : symThreeDiag B = 0 := by
      apply diag_eq_zero_of_polar
      intro v
      obtain ⟨c, hc, hcτ⟩ := S.exists_mem_C_τ v
      have h' := hconj c hc
      rw [hB, S.conj_A_D (S.C_le_D hc), hcτ] at h'
      have h'' := congrArg Subtype.val (S.e_injective h').1
      rw [coe_symThreeTransl_zero] at h''
      exact add_eq_left.mp h''
    change (x : M) ∈ S.I
    rw [hB]
    exact ⟨B, hBd, rfl⟩
  · intro x hx
    refine ⟨⟨x, S.I_le_C hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (S.commute_I_D (S.C_le_D c.2) hx)

theorem polar_mem_commutator (u v : Fin 3 → ZMod 2) :
    S.e ⟨symThreePolar v u, symThreePolar_mem v u⟩ 0 ∈ ⁅S.C, S.C⁆ := by
  obtain ⟨c, hc, hcτ⟩ := S.exists_mem_C_τ v
  have ha : S.e (symThreeDiagSym u) 0 ∈ S.C := S.A_le_C (S.e_mem_A _)
  have h : ⁅S.e (symThreeDiagSym u) 0, c⁻¹⁆ = S.e ⟨symThreePolar v u, symThreePolar_mem v u⟩ 0 := by
    have h1 : ⁅S.e (symThreeDiagSym u) 0, c⁻¹⁆ =
        S.e (symThreeDiagSym u) 0 * (c⁻¹ * S.e (symThreeDiagSym u) 0 * c) := by
      rw [commutatorElement_def, inv_inv, S.e_inv]
      group
    rw [h1, S.conj_A_D (S.C_le_D hc), hcτ, ← e_add_zero]
    congr 1
    apply Subtype.ext
    rw [AddSubgroup.coe_add, coe_symThreeTransl_zero, symThreeDiag_diagSym]
    ext i j
    simp only [Matrix.add_apply]
    grind
  rw [← h]
  exact Subgroup.commutator_mem_commutator ha (inv_mem hc)

theorem commutator_C : ⁅S.C, S.C⁆ = S.I := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact S.commutator_mem_I hx hy
  · rintro _ ⟨B, hB, rfl⟩
    have hsel : ∀ (p : Prop) [Decidable p] (X : binarySymMatrices 3),
        S.e X 0 ∈ ⁅S.C, S.C⁆ → S.e (if p then X else 0) 0 ∈ ⁅S.C, S.C⁆ := by
      intro p _ X hX
      split_ifs
      · exact hX
      · rw [e_zero_zero]
        exact Subgroup.one_mem _
    have hBeq : B = (if symThreeOff B 0 = 1 then
          ⟨symThreePolar ![0, 1, 0] ![0, 0, 1], symThreePolar_mem _ _⟩ else 0) +
        (if symThreeOff B 1 = 1 then
          ⟨symThreePolar ![1, 0, 0] ![0, 0, 1], symThreePolar_mem _ _⟩ else 0) +
        (if symThreeOff B 2 = 1 then
          ⟨symThreePolar ![1, 0, 0] ![0, 1, 0], symThreePolar_mem _ _⟩ else 0) := by
      have hBt : (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) = symThreeAlt (symThreeOff B) :=
        eq_symThreeAlt B.2 hB
      apply Subtype.ext
      rw [AddSubgroup.coe_add, AddSubgroup.coe_add]
      conv_lhs => rw [hBt, symThreeAlt_eq_polar]
      split_ifs <;> rfl
    rw [hBeq, e_add_zero, e_add_zero]
    exact mul_mem (mul_mem (hsel _ _ (S.polar_mem_commutator _ _))
      (hsel _ _ (S.polar_mem_commutator _ _))) (hsel _ _ (S.polar_mem_commutator _ _))

theorem sq_mem_I_C {c : M} (hc : c ∈ S.C) : c ^ 2 ∈ S.I := by
  rw [← S.center_C]
  refine ⟨⟨c ^ 2, pow_mem hc 2⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  change (x : M) * c ^ 2 = c ^ 2 * x
  have h1 := S.commutator_mem_I hc x.2
  have h2 : ⁅c ^ 2, (x : M)⁆ = 1 := by
    have hid : ⁅c * c, (x : M)⁆ = c * ⁅c, (x : M)⁆ * c⁻¹ * ⁅c, (x : M)⁆ := by
      simp only [commutatorElement_def]
      group
    rw [sq, hid, S.conj_I_C hc h1, ← sq]
    exact S.sq_eq_one_of_mem_R (S.A_le_R (S.I_le_A h1))
  exact (commutatorElement_eq_one_iff_commute.1 h2).symm

theorem closure_sq_C : Subgroup.closure {x | ∃ c ∈ S.C, c ^ 2 = x} = S.I := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    exact S.sq_mem_I_C hc
  · rw [← S.commutator_C, Subgroup.commutator_le]
    intro x hx y hy
    rw [symThree_commutatorElement_eq_sq]
    exact mul_mem (mul_mem (Subgroup.subset_closure ⟨_, mul_mem hx hy, rfl⟩)
      (Subgroup.subset_closure ⟨_, mul_mem (mul_mem (inv_mem hy) (inv_mem hx)) hy, rfl⟩))
      (Subgroup.subset_closure ⟨_, inv_mem hy, rfl⟩)

theorem I_ne_bot : S.I ≠ ⊥ := by
  intro h
  have hx : S.e (symThreeAltSym ![1, 0, 0]) 0 ∈ S.I := ⟨_, symThreeDiag_alt _, rfl⟩
  rw [h, Subgroup.mem_bot, e_eq_one, symThreeAltSym_eq_zero_iff] at hx
  exact absurd hx.1 (by decide)

theorem exponent_C : Monoid.exponent S.C = 4 := by
  have h4 : ∀ c : S.C, c ^ 4 = 1 := fun c => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      S.sq_eq_one_of_mem_R (S.A_le_R (S.I_le_A (S.sq_mem_I_C c.2)))])
  have hndvd : ¬ Monoid.exponent S.C ∣ 2 := by
    intro h
    apply S.I_ne_bot
    rw [← S.closure_sq_C, Subgroup.closure_eq_bot_iff]
    rintro _ ⟨c, hc, rfl⟩
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 h ⟨c, hc⟩
    exact congrArg Subtype.val this
  have hdvd : Monoid.exponent S.C ∣ 4 := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 h4
  have hle : Monoid.exponent S.C ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Monoid.exponent S.C
  · exact absurd hdvd (by decide)
  · exact absurd (one_dvd 2) hndvd
  · exact absurd (dvd_refl 2) hndvd
  · exact absurd hdvd (by decide)
  · rfl

theorem nilpotencyClass_C : Group.nilpotencyClass S.C = 2 := by
  have h1 : S.C.lowerCentralSeries 1 = S.I := S.commutator_C
  have h2 : S.C.lowerCentralSeries 2 = ⊥ := by
    change ⁅S.C.lowerCentralSeries 1, S.C⁆ = ⊥
    rw [h1, eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    exact (S.commute_I_D (S.C_le_D hy) hx).symm
  have hT : ∀ n, ((⊤ : Subgroup S.C).lowerCentralSeries n = ⊥ ↔ S.C.lowerCentralSeries n = ⊥) := by
    intro n
    rw [← Subgroup.top_subtype_lowerCentralSeries S.C n,
      Subgroup.map_eq_bot_iff_of_injective _ S.C.subtype_injective]
  have hnil : Group.IsNilpotent S.C := Subgroup.nilpotent_iff_lowerCentralSeries.2 ⟨2, (hT 2).2 h2⟩
  have hle : Group.nilpotencyClass S.C ≤ 2 :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.1 ((hT 2).2 h2)
  have hnle : ¬ Group.nilpotencyClass S.C ≤ 1 := by
    intro h
    have h' := (hT 1).1 (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.2 h)
    rw [h1] at h'
    exact S.I_ne_bot h'
  omega

theorem fix_iff {m : M} : m⁻¹ * S.z * m = S.z ↔ S.z * m = m * S.z := by
  constructor
  · intro h
    calc S.z * m = m * (m⁻¹ * S.z * m) := by group
      _ = m * S.z := by rw [h]
  · intro h
    rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem fix_pow {m : M} (hm : m⁻¹ * S.z * m = S.z) (k : ℕ) : (m ^ k)⁻¹ * S.z * m ^ k = S.z :=
  S.fix_iff.2 ((Commute.pow_right (S.fix_iff.1 hm) k).eq)

theorem fix_zpow {m : M} (hm : m⁻¹ * S.z * m = S.z) (k : ℤ) : (m ^ k)⁻¹ * S.z * m ^ k = S.z :=
  S.fix_iff.2 ((Commute.zpow_right (S.fix_iff.1 hm) k).eq)

theorem lin_pow {m : M} (hm : m⁻¹ * S.z * m = S.z) (k : ℕ) : S.lin (m ^ k) = S.lin m ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, S.lin_one]
  | succ k ih => rw [pow_succ, S.lin_mul _ _ (S.fix_pow hm k) hm, ih, pow_succ']

theorem exists_order_seven : ∃ Y : Subgroup M, (∀ y ∈ Y, y⁻¹ * S.z * y = S.z) ∧
    Nat.card Y = 7 := by
  have h7 : (S.m₀ ^ 7) ^ 2 = 1 := S.sq_eq_one_of_mem_R (S.mem_R_of_lin _ (S.fix_pow S.m₀_fix 7)
    (by rw [S.lin_pow S.m₀_fix, S.lin_m₀, symThreeSinger_pow_seven]))
  have hy7 : (S.m₀ ^ 8) ^ 7 = 1 := by
    rw [← pow_mul, show 8 * 7 = 7 * 2 * 4 from rfl, pow_mul, pow_mul, h7, one_pow]
  have hy1 : S.m₀ ^ 8 ≠ 1 := by
    intro h
    have hl := S.lin_pow S.m₀_fix 8
    rw [h, S.lin_one, S.lin_m₀, show (8 : ℕ) = 7 + 1 from rfl, pow_succ,
      symThreeSinger_pow_seven, one_mul] at hl
    exact symThreeSinger_ne_one hl.symm
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hord : orderOf (S.m₀ ^ 8) = 7 := orderOf_eq_prime hy7 hy1
  refine ⟨Subgroup.zpowers (S.m₀ ^ 8), ?_, by rw [Nat.card_zpowers, hord]⟩
  rintro _ ⟨k, rfl⟩
  exact S.fix_zpow (S.fix_pow S.m₀_fix 8) k

theorem τ_list_prod {d : M} (hd : d ∈ S.D) (L : List M)
    (hL : ∀ y ∈ L, y⁻¹ * S.z * y = S.z) :
    (L.map fun y => y⁻¹ * d * y).prod ∈ S.D ∧ S.τ (L.map fun y => y⁻¹ * d * y).prod =
      (L.map fun y => (S.lin y : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ S.τ d).sum := by
  induction L with
  | nil => exact ⟨S.D.one_mem, S.τ_one⟩
  | cons y L ih =>
    have hy := hL y List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := ih fun y' hy' => hL y' (List.mem_cons_of_mem _ hy')
    have hyd : y⁻¹ * d * y ∈ S.D := by
      have := S.D_normal.conj_mem d hd y⁻¹
      rwa [inv_inv] at this
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons]
    exact ⟨mul_mem hyd ih1, by rw [S.τ_mul _ hyd _ ih1, S.τ_conj y hy d hd, ih2]⟩

theorem length_eq {Y : Subgroup M} (hY7 : Nat.card Y = 7) {l : List M} (hl : l.Nodup)
    (hlY : ∀ y, y ∈ l ↔ y ∈ Y) : l.length = 7 := by
  classical
  rw [← List.toFinset_card_of_nodup hl, ← Nat.card_eq_finsetCard, ← hY7]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by
    rw [List.mem_toFinset, hlY])

theorem norm_mem_R {Y : Subgroup M} (hYz : ∀ y ∈ Y, y⁻¹ * S.z * y = S.z) (hY7 : Nat.card Y = 7)
    {l : List M} (hl : l.Nodup) (hlY : ∀ y, y ∈ l ↔ y ∈ Y) {d : M} (hd : d ∈ S.D) :
    (l.map fun y => y⁻¹ * d * y).prod ∈ S.R := by
  have hlz : ∀ y ∈ l, y⁻¹ * S.z * y = S.z := fun y hy => hYz y ((hlY y).1 hy)
  obtain ⟨hD, hτ⟩ := S.τ_list_prod hd l hlz
  rw [← S.τ_eq_zero _ hD, hτ]
  set u := (l.map fun y => (S.lin y : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ S.τ d).sum with hu
  have hfix : ∀ y' ∈ Y, (S.lin y' : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u = u := by
    intro y' hy'
    have hperm : (l.map (· * y')).Perm l := by
      refine (List.perm_ext_iff_of_nodup (hl.map (mul_left_injective y')) hl).2 fun x => ?_
      rw [List.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hlY _).2 (mul_mem ((hlY y).1 hy) hy')
      · intro hx
        exact ⟨x * y'⁻¹, (hlY _).2 (mul_mem ((hlY x).1 hx) (inv_mem hy')), inv_mul_cancel_right _ _⟩
    have h1 : (S.lin y' : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u =
        ((l.map (· * y')).map fun y => (S.lin y : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
          S.τ d).sum := by
      rw [hu, ← Matrix.mulVecLin_apply, map_list_sum, List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro y hy
      simp only [Function.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [S.lin_mul y y' (hlz y hy) (hYz y' hy'), Units.val_mul]
    rw [h1, (hperm.map _).sum_eq]
  obtain ⟨y', hy'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (fun h : Y = ⊥ => by
    rw [h, Subgroup.card_bot] at hY7
    exact absurd hY7 (by norm_num))
  have hy'7 : (y' : M) ^ 7 = 1 := by
    have := orderOf_dvd_natCard y'
    rw [hY7] at this
    have h := orderOf_dvd_iff_pow_eq_one.1 this
    exact congrArg Subtype.val h
  have hlin7 : (S.lin y' : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 7 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← S.lin_pow (hYz _ y'.2), hy'7, S.lin_one, Units.val_one]
  have hlin1 : (S.lin y' : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 := by
    intro h
    have hR := S.mem_R_of_lin _ (hYz _ y'.2) (Units.ext h)
    apply hy'
    apply Subtype.ext
    have h2 := S.sq_eq_one_of_mem_R hR
    change (y' : M) = 1
    calc (y' : M) = (y' : M) ^ 7 * (((y' : M) ^ 2) ^ 3)⁻¹ := by group
      _ = 1 := by rw [hy'7, h2, one_pow, inv_one, mul_one]
  exact symThree_order_seven_fixed _ hlin7 hlin1 u (hfix _ y'.2)

theorem mem_C_iff_norm {Y : Subgroup M} (hYz : ∀ y ∈ Y, y⁻¹ * S.z * y = S.z)
    (hY7 : Nat.card Y = 7) {l : List M} (hl : l.Nodup) (hlY : ∀ y, y ∈ l ↔ y ∈ Y) {d : M}
    (hd : d ∈ S.D) : d ∈ S.C ↔ (l.map fun y => y⁻¹ * d * y).prod ∈ S.A := by
  have hfwd : ∀ c ∈ S.C, (l.map fun y => y⁻¹ * c * y).prod ∈ S.A := by
    intro c hc
    have hR := S.norm_mem_R hYz hY7 hl hlY (S.C_le_D hc)
    have hC : (l.map fun y => y⁻¹ * c * y).prod ∈ S.C := S.C.list_prod_mem (by
      intro x hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      have := S.C_normal.conj_mem c hc y⁻¹
      rwa [inv_inv] at this)
    exact S.mem_A_of_mem_C_R hC hR
  refine ⟨hfwd d, fun hA => ?_⟩
  by_contra hdC
  have hc₁ : S.z⁻¹ * d ∈ S.C := (S.mem_C_or hd).resolve_left hdC
  have hN := S.A_normal'
  have hAD : (S.A.subgroupOf S.D).Normal := Subgroup.normal_subgroupOf
  let _ : CommGroup (S.D ⧸ S.A.subgroupOf S.D) :=
    { (inferInstance : Group (S.D ⧸ S.A.subgroupOf S.D)) with
      mul_comm := by
        rintro ⟨x⟩ ⟨y⟩
        change ((x * y : S.D) : S.D ⧸ S.A.subgroupOf S.D) = ((y * x : S.D) : S.D ⧸ _)
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have h := S.commutatorElement_mem_A (inv_mem y.2) (inv_mem x.2)
        have hid : (((x * y)⁻¹ * (y * x) : S.D) : M) = ⁅(y : M)⁻¹, (x : M)⁻¹⁆ := by
          rw [commutatorElement_def, inv_inv, inv_inv]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [hid]
        exact h }
  let π : S.D →* S.D ⧸ S.A.subgroupOf S.D := QuotientGroup.mk' _
  have hconj : ∀ (x : M) (hx : x ∈ S.D) (y : M), y⁻¹ * x * y ∈ S.D := fun x hx y => by
    have := S.D_normal.conj_mem x hx y⁻¹
    rwa [inv_inv] at this
  let f : M → S.D := fun y => ⟨y⁻¹ * d * y, hconj d hd y⟩
  let g : M → S.D := fun y => ⟨y⁻¹ * (S.z⁻¹ * d) * y, hconj _ (S.C_le_D hc₁) y⟩
  have hπA : ∀ x : S.D, (x : M) ∈ S.A → π x = 1 := fun x hx => by
    change ((x : S.D) : S.D ⧸ S.A.subgroupOf S.D) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hx
  have hprodf : ((l.map f).prod : M) = (l.map fun y => y⁻¹ * d * y).prod := by
    rw [SubmonoidClass.coe_list_prod, List.map_map]
    rfl
  have hprodg : ((l.map g).prod : M) = (l.map fun y => y⁻¹ * (S.z⁻¹ * d) * y).prod := by
    rw [SubmonoidClass.coe_list_prod, List.map_map]
    rfl
  have hf1 : π (l.map f).prod = 1 := hπA _ (by rw [hprodf]; exact hA)
  have hg1 : π (l.map g).prod = 1 := hπA _ (by rw [hprodg]; exact hfwd _ hc₁)
  have hfg : ∀ y ∈ l, f y = ⟨S.z, S.z_mem_D⟩ * g y := by
    intro y hy
    apply Subtype.ext
    have hyz := hYz y ((hlY y).1 hy)
    change y⁻¹ * d * y = S.z * (y⁻¹ * (S.z⁻¹ * d) * y)
    calc y⁻¹ * d * y = (y⁻¹ * S.z * y) * (y⁻¹ * (S.z⁻¹ * d) * y) := by group
      _ = S.z * (y⁻¹ * (S.z⁻¹ * d) * y) := by rw [hyz]
  have hmap : (l.map f).map π = l.map fun y => π ⟨S.z, S.z_mem_D⟩ * π (g y) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro y hy
    simp only [Function.comp_apply]
    rw [hfg y hy, map_mul]
  have hg1' : (l.map fun y => π (g y)).prod = 1 := by
    rw [← hg1, map_list_prod, List.map_map]
    rfl
  rw [map_list_prod, hmap, List.prod_map_mul, List.map_const', List.prod_replicate,
    length_eq hY7 hl hlY, hg1', mul_one] at hf1
  have hz : π ⟨S.z, S.z_mem_D⟩ = 1 := by
    have h2 : π ⟨S.z, S.z_mem_D⟩ ^ 2 = 1 := by
      rw [← map_pow]
      exact hπA _ (by
        change S.z ^ 2 ∈ S.A
        rw [S.z_sq]
        exact S.A.one_mem)
    calc π ⟨S.z, S.z_mem_D⟩ = π ⟨S.z, S.z_mem_D⟩ ^ 7 * (π ⟨S.z, S.z_mem_D⟩ ^ 2)⁻¹ ^ 3 := by
          group
      _ = 1 := by rw [hf1, h2, inv_one, one_pow, mul_one]
  apply S.z_not_mem_A
  have := (QuotientGroup.eq_one_iff (N := S.A.subgroupOf S.D) (⟨S.z, S.z_mem_D⟩ : S.D)).1 hz
  exact this

theorem relIndex_A_D : S.A.relIndex S.D = 16 := by
  have h := Subgroup.card_mul_index (S.A.subgroupOf S.D)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.A_le_D).toEquiv, S.card_A, S.card_D] at h
  change 64 * S.A.relIndex S.D = 1024 at h
  omega

theorem card_I : Nat.card S.I = 8 := by
  rw [← SymThreeCosetData.card_alt]
  refine (Nat.card_eq_of_bijective (fun B : {B : binarySymMatrices 3 | symThreeDiag B = 0} =>
    (⟨S.e B 0, B, B.2, rfl⟩ : S.I)) ⟨?_, ?_⟩).symm
  · intro B B' h
    have h' : S.e B 0 = S.e B' 0 := congrArg (Subtype.val : S.I → M) h
    exact Subtype.ext (S.e_injective h').1
  · rintro ⟨_, B, hB, rfl⟩
    exact ⟨⟨B, hB⟩, rfl⟩

theorem isCanonical_iff (X : Subgroup M) : S.IsCanonical X ↔
    X ≤ S.D ∧ S.I ≤ X ∧ ⁅X, X⁆ ≤ S.I ∧ S.I.relIndex X = 64 := by
  have hcard : ∀ X : Subgroup M, S.I ≤ X → (Nat.card X = 512 ↔ S.I.relIndex X = 64) := by
    intro X hIX
    have h := Subgroup.card_mul_index (S.I.subgroupOf X)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIX).toEquiv, S.card_I] at h
    change 8 * S.I.relIndex X = Nat.card X at h
    omega
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, (Subgroup.commutator_le).2 h3, (hcard X h2).1 h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, fun x hx y hy => h3 (Subgroup.commutator_mem_commutator hx hy),
      (hcard X h2).2 h4⟩

theorem canonical_summary :
    S.A.Normal ∧ S.I.Normal ∧ (S.A ≤ S.D ∧ (∀ d ∈ S.D, d ^ 2 ∈ S.A) ∧ S.A.relIndex S.D = 16) ∧
    (S.C ≤ S.D ∧ S.I ≤ S.C ∧ ⁅S.C, S.C⁆ ≤ S.I ∧ S.I.relIndex S.C = 64) ∧
    (∀ X : Subgroup M, X ≤ S.D → S.I ≤ X → ⁅X, X⁆ ≤ S.I → S.I.relIndex X = 64 → X = S.C) ∧
    (S.C.subgroupOf S.D).Characteristic ∧ S.C.Normal ∧ Nat.card S.C = 512 ∧ S.A ≤ S.C ∧
    (S.D : Set M) = (S.R : Set M) * (S.C : Set M) ∧ S.R ⊓ S.C = S.A ∧
    (Subgroup.center S.C).map S.C.subtype = S.I ∧ ⁅S.C, S.C⁆ = S.I ∧
    Subgroup.closure {x | ∃ c ∈ S.C, c ^ 2 = x} = S.I ∧ (∀ c ∈ S.C, c ^ 2 ∈ S.I) ∧
    Group.nilpotencyClass S.C = 2 ∧ Monoid.exponent S.C = 4 ∧
    (∃ Y : Subgroup M, (∀ y ∈ Y, y⁻¹ * S.z * y = S.z) ∧ Nat.card Y = 7) ∧
    ∀ Y : Subgroup M, (∀ y ∈ Y, y⁻¹ * S.z * y = S.z) → Nat.card Y = 7 →
      ∀ l : List M, l.Nodup → (∀ y, y ∈ l ↔ y ∈ Y) →
        ∀ d ∈ S.D, (d ∈ S.C ↔ (l.map fun y => y⁻¹ * d * y).prod ∈ S.A) :=
  ⟨S.A_normal', S.I_normal', ⟨S.A_le_D, fun _ hd => S.sq_mem_A hd, S.relIndex_A_D⟩,
    (S.isCanonical_iff S.C).1 S.C_isCanonical,
    fun X h1 h2 h3 h4 => S.eq_C_of_isCanonical ((S.isCanonical_iff X).2 ⟨h1, h2, h3, h4⟩),
    S.C_characteristic, S.C_normal, S.card_C, S.A_le_C, S.D_eq_RC,
    by rw [inf_comm, S.C_inf_R], S.center_C, S.commutator_C, S.closure_sq_C,
    fun _ hc => S.sq_mem_I_C hc, S.nilpotencyClass_C, S.exponent_C, S.exists_order_seven,
    fun _ hYz hY7 _ hl hlY _ hd => S.mem_C_iff_norm hYz hY7 hl hlY hd⟩

end SymThreeAffineData

end CFSG.LocalAnalysis.ComponentInitial
