module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeBasic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix
open scoped commutatorElement Pointwise

section SymThreeAlgebra

@[expose] def symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Fin 3 → ZMod 2 :=
  fun k => B k k

@[expose] def symThreePolar (u v : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  vecMulVec u v + vecMulVec v u

@[expose] def symThreeAlt (t : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![0, t 2, t 1; t 2, 0, t 0; t 1, t 0, 0]

@[expose] def symThreeOff (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Fin 3 → ZMod 2 :=
  ![B 1 2, B 0 2, B 0 1]

theorem symThree_zmod_mul_self (x : ZMod 2) : x * x = x := by
  revert x
  decide

theorem symThree_zmod_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

theorem symThree_smul_mem (c : ZMod 2) {P : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hP : P ∈ binarySymMatrices 3) : c • P ∈ binarySymMatrices 3 := by
  rw [mem_binarySymMatrices, transpose_smul, show Pᵀ = P from hP]

theorem symThreePolar_mem (u v : Fin 3 → ZMod 2) : symThreePolar u v ∈ binarySymMatrices 3 := by
  rw [mem_binarySymMatrices, symThreePolar, transpose_add, transpose_vecMulVec,
    transpose_vecMulVec, add_comm]

theorem symThreeDiag_polar (u v : Fin 3 → ZMod 2) : symThreeDiag (symThreePolar u v) = 0 := by
  funext k
  simp only [symThreeDiag, symThreePolar, Matrix.add_apply, vecMulVec_apply, Pi.zero_apply]
  grind

theorem symThreePolar_zero_left (v : Fin 3 → ZMod 2) : symThreePolar 0 v = 0 := by
  simp [symThreePolar]

theorem symThreePolar_self (u : Fin 3 → ZMod 2) : symThreePolar u u = 0 := by
  ext i j
  simp only [symThreePolar, Matrix.add_apply, vecMulVec_apply, Matrix.zero_apply]
  grind

theorem symThreePolar_comm (u v : Fin 3 → ZMod 2) : symThreePolar u v = symThreePolar v u :=
  add_comm _ _

theorem symThreeDiag_add (B C : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    symThreeDiag (B + C) = symThreeDiag B + symThreeDiag C :=
  rfl

theorem symThreeDiag_smul (c : ZMod 2) (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    symThreeDiag (c • B) = c • symThreeDiag B :=
  rfl

theorem symThreeDiag_zero : symThreeDiag 0 = 0 :=
  rfl

theorem symThreeDiag_congr (g B : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hB : Bᵀ = B) :
    symThreeDiag (g * B * gᵀ) = g *ᵥ symThreeDiag B := by
  have h10 : B 1 0 = B 0 1 := congrFun (congrFun hB 0) 1
  have h20 : B 2 0 = B 0 2 := congrFun (congrFun hB 0) 2
  have h21 : B 2 1 = B 1 2 := congrFun (congrFun hB 1) 2
  funext k
  simp only [symThreeDiag, mul_apply, transpose_apply, mulVec, dotProduct, Fin.sum_univ_three,
    h10, h20, h21]
  have h0 := symThree_zmod_mul_self (g k 0)
  have h1 := symThree_zmod_mul_self (g k 1)
  have h2 := symThree_zmod_mul_self (g k 2)
  grind

theorem symThreeAlt_mem (t : Fin 3 → ZMod 2) : symThreeAlt t ∈ binarySymMatrices 3 := by
  rw [mem_binarySymMatrices]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem symThreeDiag_alt (t : Fin 3 → ZMod 2) : symThreeDiag (symThreeAlt t) = 0 := by
  funext k
  fin_cases k <;> rfl

theorem eq_symThreeAlt {B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hB : Bᵀ = B)
    (hd : symThreeDiag B = 0) : B = symThreeAlt (symThreeOff B) := by
  have h10 : B 1 0 = B 0 1 := congrFun (congrFun hB 0) 1
  have h20 : B 2 0 = B 0 2 := congrFun (congrFun hB 0) 2
  have h21 : B 2 1 = B 1 2 := congrFun (congrFun hB 1) 2
  have h00 : B 0 0 = 0 := congrFun hd 0
  have h11 : B 1 1 = 0 := congrFun hd 1
  have h22 : B 2 2 = 0 := congrFun hd 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symThreeAlt, symThreeOff, h10, h20, h21, h00, h11, h22]

theorem symThreeAlt_eq_zero_iff (t : Fin 3 → ZMod 2) : symThreeAlt t = 0 ↔ t = 0 := by
  revert t
  decide

@[expose] def symThreeAffine (κ : ZMod 2) (C B : binarySymMatrices 3) : binarySymMatrices 3 :=
  ⟨(B : Matrix (Fin 3) (Fin 3) (ZMod 2)) + C +
      κ • symThreePolar (symThreeDiag C) (symThreeDiag B),
    add_mem (add_mem B.2 C.2)
      (symThree_smul_mem κ (symThreePolar_mem _ _))⟩

@[expose] def symThreeLinear (κ ε : ZMod 2) (C B : binarySymMatrices 3) : binarySymMatrices 3 :=
  ⟨(B : Matrix (Fin 3) (Fin 3) (ZMod 2)) + κ • symThreePolar (symThreeDiag C) (symThreeDiag B) +
      ε • (C : Matrix (Fin 3) (Fin 3) (ZMod 2)),
    add_mem (add_mem B.2
      (symThree_smul_mem κ (symThreePolar_mem _ _)))
      (symThree_smul_mem ε C.2)⟩

@[expose] def symThreeCongr (g : GL (Fin 3) (ZMod 2)) (B : binarySymMatrices 3) :
    binarySymMatrices 3 :=
  ⟨(g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * B * (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ, by
    rw [mem_binarySymMatrices, transpose_mul, transpose_mul, transpose_transpose,
      show (B : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = B from B.2, Matrix.mul_assoc]⟩

theorem coe_symThreeAffine (κ : ZMod 2) (C B : binarySymMatrices 3) :
    (symThreeAffine κ C B : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) + C +
        κ • symThreePolar (symThreeDiag C) (symThreeDiag B) :=
  rfl

theorem coe_symThreeLinear (κ ε : ZMod 2) (C B : binarySymMatrices 3) :
    (symThreeLinear κ ε C B : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) + κ • symThreePolar (symThreeDiag C) (symThreeDiag B) +
        ε • (C : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  rfl

theorem coe_symThreeCongr (g : GL (Fin 3) (ZMod 2)) (B : binarySymMatrices 3) :
    (symThreeCongr g B : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * B * (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ :=
  rfl

theorem symThreeAffine_zero_right (κ : ZMod 2) (C : binarySymMatrices 3) :
    symThreeAffine κ C 0 = C := by
  apply Subtype.ext
  rw [coe_symThreeAffine]
  simp [symThreeDiag_zero, symThreePolar_comm _ 0, symThreePolar_zero_left]

theorem symThreeAffine_zero_left (κ : ZMod 2) (B : binarySymMatrices 3) :
    symThreeAffine κ 0 B = B := by
  apply Subtype.ext
  rw [coe_symThreeAffine]
  simp [symThreeDiag_zero, symThreePolar_zero_left]

theorem symThreeAffine_of_diag_eq_zero (κ : ZMod 2) {C : binarySymMatrices 3}
    (hC : symThreeDiag C = 0) (B : binarySymMatrices 3) : symThreeAffine κ C B = B + C := by
  apply Subtype.ext
  rw [coe_symThreeAffine, hC, symThreePolar_zero_left, smul_zero, add_zero]
  rfl

theorem symThreeDiag_affine (κ : ZMod 2) (C B : binarySymMatrices 3) :
    symThreeDiag (symThreeAffine κ C B) = symThreeDiag B + symThreeDiag C := by
  rw [coe_symThreeAffine, symThreeDiag_add, symThreeDiag_smul, symThreeDiag_polar, smul_zero,
    add_zero, symThreeDiag_add]

theorem symThreeAffine_add_right (κ : ZMod 2) (C B : binarySymMatrices 3) :
    symThreeAffine κ C B + C = symThreeLinear κ 0 C B := by
  apply Subtype.ext
  ext i j
  simp only [AddSubgroup.coe_add, coe_symThreeAffine, coe_symThreeLinear, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, zero_mul, add_zero]
  grind

theorem symThreeAffine_eq_linear (κ : ZMod 2) (C B : binarySymMatrices 3) :
    symThreeAffine κ C B = symThreeLinear κ 1 C B := by
  apply Subtype.ext
  rw [coe_symThreeAffine, coe_symThreeLinear, one_smul, add_right_comm]

theorem symThreeLinear_zero_of_diag_eq_zero (κ : ZMod 2) {C : binarySymMatrices 3}
    (hC : symThreeDiag C = 0) (B : binarySymMatrices 3) : symThreeLinear κ 0 C B = B := by
  apply Subtype.ext
  rw [coe_symThreeLinear, hC, symThreePolar_zero_left, smul_zero, add_zero, zero_smul, add_zero]

theorem symThreeLinear_one_of_diag_eq_zero (κ : ZMod 2) {C : binarySymMatrices 3}
    (hC : symThreeDiag C = 0) (B : binarySymMatrices 3) : symThreeLinear κ 1 C B = B + C := by
  apply Subtype.ext
  rw [coe_symThreeLinear, hC, symThreePolar_zero_left, smul_zero, add_zero, one_smul]
  rfl

theorem symThreeDiag_coe_congr (g : GL (Fin 3) (ZMod 2)) (B : binarySymMatrices 3) :
    symThreeDiag (symThreeCongr g B) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ symThreeDiag B :=
  symThreeDiag_congr _ _ B.2

theorem symThreeCongr_zero (g : GL (Fin 3) (ZMod 2)) : symThreeCongr g 0 = 0 := by
  apply Subtype.ext
  simp [coe_symThreeCongr]

theorem symThreeCongr_add (g : GL (Fin 3) (ZMod 2)) (B C : binarySymMatrices 3) :
    symThreeCongr g (B + C) = symThreeCongr g B + symThreeCongr g C := by
  apply Subtype.ext
  simp [coe_symThreeCongr, Matrix.mul_add, Matrix.add_mul]

theorem symThree_add_self (B : binarySymMatrices 3) : B + B = 0 := by
  apply Subtype.ext
  ext i j
  exact symThree_zmod_add_self _

theorem symThree_eq_of_add_eq_zero {B C : binarySymMatrices 3} (h : B + C = 0) : B = C := by
  rw [← sub_eq_zero, sub_eq_add_neg]
  have : -C = C := by rw [neg_eq_iff_add_eq_zero, symThree_add_self]
  rwa [this]

theorem symThreeAffine_self (κ : ZMod 2) (C : binarySymMatrices 3) :
    symThreeAffine κ C C = 0 := by
  apply Subtype.ext
  rw [coe_symThreeAffine, symThreePolar_self, smul_zero, add_zero]
  exact congrArg Subtype.val (symThree_add_self C)

theorem symThreeLinear_one_eq_self {κ : ZMod 2} {C B : binarySymMatrices 3}
    (h : symThreeLinear κ 1 C B = B) : C = 0 := by
  have hm := congrArg (fun X : binarySymMatrices 3 => (X : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
  simp only [coe_symThreeLinear, one_smul] at hm
  have hm' : κ • symThreePolar (symThreeDiag C) (symThreeDiag B) +
      (C : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by
    rw [add_assoc] at hm
    exact add_left_cancel (hm.trans (add_zero _).symm)
  have hδ := congrArg symThreeDiag hm'
  rw [symThreeDiag_add, symThreeDiag_smul, symThreeDiag_polar, smul_zero, zero_add,
    symThreeDiag_zero] at hδ
  rw [hδ, symThreePolar_zero_left, smul_zero, zero_add] at hm'
  exact Subtype.ext hm'

theorem symThreeDiag_linear_of_diag_eq_zero (κ ε : ZMod 2) {C : binarySymMatrices 3}
    (hC : symThreeDiag C = 0) (B : binarySymMatrices 3) :
    symThreeDiag (symThreeLinear κ ε C B) = symThreeDiag B := by
  rw [coe_symThreeLinear, symThreeDiag_add, symThreeDiag_add, symThreeDiag_smul,
    symThreeDiag_polar, symThreeDiag_smul, hC, smul_zero, smul_zero, add_zero, add_zero]

@[expose] def symThreeAltSym (t : Fin 3 → ZMod 2) : binarySymMatrices 3 :=
  ⟨symThreeAlt t, symThreeAlt_mem t⟩

theorem symThreeAltSym_eq_zero_iff (t : Fin 3 → ZMod 2) : symThreeAltSym t = 0 ↔ t = 0 := by
  rw [← symThreeAlt_eq_zero_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem eq_symThreeAltSym {B : binarySymMatrices 3} (hB : symThreeDiag B = 0) :
    B = symThreeAltSym (symThreeOff B) :=
  Subtype.ext (eq_symThreeAlt B.2 hB)

@[expose] def symThreeTransvection (u w : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  1 + vecMulVec u w

theorem symThree_alt_stabilizer_moves : ∀ t : Fin 3 → ZMod 2, t ≠ 0 →
    ∀ v : Fin 3 → ZMod 2, v ≠ 0 → ∃ u w : Fin 3 → ZMod 2,
      symThreeTransvection u w * symThreeTransvection u w = 1 ∧
      symThreeTransvection u w * symThreeAlt t * (symThreeTransvection u w)ᵀ = symThreeAlt t ∧
      symThreeTransvection u w *ᵥ v ≠ v := by
  decide

@[expose] def symThreeSingerMatrix : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def symThreeSingerInvMatrix : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] def symThreeSinger : GL (Fin 3) (ZMod 2) :=
  ⟨symThreeSingerMatrix, symThreeSingerInvMatrix, by decide, by decide⟩

@[expose] def symThreeSingerCongr (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  symThreeSingerMatrix * B * symThreeSingerMatrixᵀ

theorem symThreeSingerCongr_cube :
    symThreeSingerCongr (symThreeSingerCongr (symThreeSingerCongr (symThreeAlt ![1, 0, 0]))) =
      symThreeAlt ![1, 0, 0] +
        symThreeSingerCongr (symThreeSingerCongr (symThreeAlt ![1, 0, 0])) := by
  decide

theorem symThreeSingerCongr_cube_eq : ∀ t : Fin 3 → ZMod 2,
    symThreeSingerCongr (symThreeSingerCongr (symThreeSingerCongr (symThreeAlt t))) =
      symThreeAlt t + symThreeSingerCongr (symThreeAlt t) → t = 0 := by
  decide

theorem symThreeSingerCongr_span : ∀ t : Fin 3 → ZMod 2, ∃ a b c : Bool,
    symThreeAlt t = (if a then symThreeAlt ![1, 0, 0] else 0) +
      (if b then symThreeSingerCongr (symThreeAlt ![1, 0, 0]) else 0) +
      (if c then symThreeSingerCongr (symThreeSingerCongr (symThreeAlt ![1, 0, 0])) else 0) := by
  decide

theorem symThreeSingerCongr_transitive : ∀ t t' : Fin 3 → ZMod 2, t ≠ 0 → t' ≠ 0 →
    ∃ k : Fin 7, symThreeSingerCongr^[k] (symThreeAlt t) = symThreeAlt t' := by
  decide

theorem coe_iterate_symThreeCongr_singer (k : ℕ) (B : binarySymMatrices 3) :
    ((symThreeCongr symThreeSinger)^[k] B : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      symThreeSingerCongr^[k] (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

end SymThreeAlgebra

theorem symThree_commutatorElement_eq_sq {G : Type*} [Group G] (x y : G) :
    ⁅x, y⁆ = (x * y) ^ 2 * (y⁻¹ * x⁻¹ * y) ^ 2 * y⁻¹ ^ 2 := by
  rw [commutatorElement_def, sq, sq, sq]
  group

theorem symThree_card_eq_card_image_mul {G X : Type*} [Group G] {K L : Subgroup G}
    (hLK : L ≤ K) (f : G → X) (hf : ∀ x ∈ K, ∀ y ∈ K, f x = f y ↔ x⁻¹ * y ∈ L) :
    Nat.card K = Nat.card (f '' K) * Nat.card L := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (L.subgroupOf K),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLK).toEquiv]
  congr 1
  refine Nat.card_congr (Equiv.ofBijective (Quotient.lift
    (fun x : K => (⟨f x, x, x.2, rfl⟩ : f '' (K : Set G))) ?_) ⟨?_, ?_⟩)
  · intro a b hab
    have hab' : a⁻¹ * b ∈ L.subgroupOf K := QuotientGroup.leftRel_apply.mp hab
    exact Subtype.ext ((hf a a.2 b b.2).2 (Subgroup.mem_subgroupOf.1 hab'))
  · rintro ⟨a⟩ ⟨b⟩ hab
    have hab' : f a = f b := congrArg Subtype.val hab
    exact Quotient.sound ((QuotientGroup.leftRel_apply).2
      (Subgroup.mem_subgroupOf.2 ((hf a a.2 b b.2).1 hab')))
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨Quotient.mk _ ⟨x, hx⟩, rfl⟩

structure SymThreeCosetData (D : Type*) [Group D] where
  R : Subgroup D
  normal : R.Normal
  θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2)
  κ : ZMod 2
  ρ : GL (Fin 3) (ZMod 2) →* MulAut D
  ν : D → binarySymMatrices 3
  conj_one : ∀ d B, d⁻¹ * (θ.symm (.ofAdd (B, 1)) : D) * d =
    θ.symm (.ofAdd (symThreeAffine κ (ν d) B, 1))
  surj : ∀ C, ∃ d, ν d = C
  faith : ∀ d, (∀ B, d⁻¹ * (θ.symm (.ofAdd (B, 1)) : D) * d = θ.symm (.ofAdd (B, 1))) → d ∈ R
  ρ_apply : ∀ g B ε, ρ g (θ.symm (.ofAdd (B, ε)) : D) = θ.symm (.ofAdd (symThreeCongr g B, ε))

namespace SymThreeCosetData

variable {D : Type*} [Group D] (S : SymThreeCosetData D)

@[expose] def e (B : binarySymMatrices 3) (ε : ZMod 2) : D := S.θ.symm (.ofAdd (B, ε))

theorem e_mul (B B' : binarySymMatrices 3) (ε ε' : ZMod 2) :
    S.e B ε * S.e B' ε' = S.e (B + B') (ε + ε') := by
  rw [e, e, e, ← Subgroup.coe_mul, ← map_mul, ← ofAdd_add, Prod.mk_add_mk]

theorem e_injective {B B' : binarySymMatrices 3} {ε ε' : ZMod 2} (h : S.e B ε = S.e B' ε') :
    B = B' ∧ ε = ε' :=
  Prod.mk.inj (Multiplicative.ofAdd.injective (S.θ.symm.injective (Subtype.ext h)))

theorem e_zero_zero : S.e 0 0 = 1 := by
  rw [e, show ((0 : binarySymMatrices 3), (0 : ZMod 2)) = 0 from rfl, ofAdd_zero, map_one,
    Subgroup.coe_one]

theorem e_mem (B : binarySymMatrices 3) (ε : ZMod 2) : S.e B ε ∈ S.R :=
  (S.θ.symm _).2

theorem exists_e {x : D} (hx : x ∈ S.R) : ∃ B ε, x = S.e B ε :=
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

theorem mem_comm {x y : D} (hx : x ∈ S.R) (hy : y ∈ S.R) : x * y = y * x := by
  obtain ⟨B, ε, rfl⟩ := S.exists_e hx
  obtain ⟨B', ε', rfl⟩ := S.exists_e hy
  exact S.e_comm B B' ε ε'

@[expose] def z : D := S.e 0 1

theorem z_mem : S.z ∈ S.R :=
  S.e_mem 0 1

theorem z_inv : S.z⁻¹ = S.z :=
  S.e_inv 0 1

theorem conj_e_one (d : D) (B : binarySymMatrices 3) :
    d⁻¹ * S.e B 1 * d = S.e (symThreeAffine S.κ (S.ν d) B) 1 :=
  S.conj_one d B

theorem conj_z (d : D) : d⁻¹ * S.z * d = S.e (S.ν d) 1 := by
  rw [z, conj_e_one, symThreeAffine_zero_right]

theorem conj_e (d : D) (B : binarySymMatrices 3) (ε : ZMod 2) :
    d⁻¹ * S.e B ε * d = S.e (symThreeLinear S.κ ε (S.ν d) B) ε := by
  rcases MatrixExtension.zmod_two_eq_zero_or_one ε with rfl | rfl
  · have h : S.e B 0 = S.e B 1 * S.e 0 1 := by
      rw [e_mul, add_zero]
      rfl
    rw [h, show d⁻¹ * (S.e B 1 * S.e 0 1) * d = (d⁻¹ * S.e B 1 * d) * (d⁻¹ * S.e 0 1 * d) by
      group, conj_e_one, conj_e_one, e_mul, symThreeAffine_zero_right, symThreeAffine_add_right]
    rfl
  · rw [conj_e_one, symThreeAffine_eq_linear]

theorem ν_mul (d d' : D) : S.ν (d * d') = symThreeAffine S.κ (S.ν d') (S.ν d) := by
  have h : (d * d')⁻¹ * S.z * (d * d') = d'⁻¹ * (d⁻¹ * S.z * d) * d' := by group
  rw [conj_z, conj_z, conj_e_one] at h
  exact (S.e_injective h).1

theorem ν_one : S.ν 1 = 0 := by
  have h := S.conj_z 1
  rw [inv_one, one_mul, mul_one, z] at h
  exact (S.e_injective h).1.symm

theorem ν_of_mem {r : D} (hr : r ∈ S.R) : S.ν r = 0 := by
  have h := S.conj_z r
  rw [show r⁻¹ * S.z * r = S.z by
    rw [S.mem_comm (inv_mem hr) S.z_mem, mul_assoc, inv_mul_cancel, mul_one], z] at h
  exact (S.e_injective h).1.symm

theorem mem_of_ν_eq_zero {d : D} (hd : S.ν d = 0) : d ∈ S.R := by
  apply S.faith
  intro B
  rw [S.conj_one, hd, symThreeAffine_zero_left]

theorem ν_eq_iff (d d' : D) : S.ν d = S.ν d' ↔ d⁻¹ * d' ∈ S.R := by
  constructor
  · intro h
    apply S.mem_of_ν_eq_zero
    rw [ν_mul, ← h, ← ν_mul, inv_mul_cancel, ν_one]
  · intro h
    rw [show d' = d * (d⁻¹ * d') by group, ν_mul, S.ν_of_mem h, symThreeAffine_zero_left]

theorem ν_eq_iff' (d d' : D) : S.ν d = S.ν d' ↔ d' * d⁻¹ ∈ S.R := by
  rw [ν_eq_iff]
  constructor
  · intro h
    have := S.normal.conj_mem _ h d
    rwa [show d * (d⁻¹ * d') * d⁻¹ = d' * d⁻¹ by group] at this
  · intro h
    have := S.normal.conj_mem _ h d⁻¹
    rwa [show d⁻¹ * (d' * d⁻¹) * d⁻¹⁻¹ = d⁻¹ * d' by group] at this

theorem ν_mul_mem_R (d : D) {r : D} (hr : r ∈ S.R) : S.ν (d * r) = S.ν d := by
  rw [ν_mul, S.ν_of_mem hr, symThreeAffine_zero_left]

@[expose] def A : Subgroup D where
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

@[expose] def I : Subgroup D where
  carrier := {x | ∃ B : binarySymMatrices 3, symThreeDiag B = 0 ∧ x = S.e B 0}
  mul_mem' := by
    rintro _ _ ⟨B, hB, rfl⟩ ⟨B', hB', rfl⟩
    refine ⟨B + B', ?_, by rw [e_mul, add_zero]⟩
    rw [AddSubgroup.coe_add, symThreeDiag_add, hB, hB', add_zero]
  one_mem' := ⟨0, symThreeDiag_zero, S.e_zero_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨B, hB, S.e_inv B 0⟩

theorem mem_I {x : D} : x ∈ S.I ↔ ∃ B : binarySymMatrices 3, symThreeDiag B = 0 ∧ x = S.e B 0 :=
  Iff.rfl

theorem e_mem_I_iff (B : binarySymMatrices 3) : S.e B 0 ∈ S.I ↔ symThreeDiag B = 0 := by
  constructor
  · rintro ⟨B', hB', h⟩
    rwa [(S.e_injective h).1]
  · intro h
    exact ⟨B, h, rfl⟩

theorem A_le_R : S.A ≤ S.R := by
  rintro _ ⟨B, rfl⟩
  exact S.e_mem B 0

theorem mem_A_or_of_mem_R {x : D} (hx : x ∈ S.R) : x ∈ S.A ∨ S.z⁻¹ * x ∈ S.A := by
  obtain ⟨B, ε, rfl⟩ := S.exists_e hx
  rcases MatrixExtension.zmod_two_eq_zero_or_one ε with rfl | rfl
  · exact Or.inl (S.e_mem_A B)
  · right
    rw [z_inv, z, e_mul, zero_add]
    exact S.e_mem_A B

@[expose] def diagHom : D →* Multiplicative (Fin 3 → ZMod 2) where
  toFun d := .ofAdd (symThreeDiag (S.ν d))
  map_one' := by
    rw [ν_one]
    rfl
  map_mul' d d' := by
    rw [ν_mul, symThreeDiag_affine, ofAdd_add, mul_comm]

@[expose] def F : Subgroup D :=
  S.diagHom.ker

theorem mem_F {d : D} : d ∈ S.F ↔ symThreeDiag (S.ν d) = 0 :=
  ofAdd_eq_one

theorem ν_mul_of_mem_F (d : D) {f : D} (hf : f ∈ S.F) : S.ν (d * f) = S.ν d + S.ν f := by
  rw [ν_mul, symThreeAffine_of_diag_eq_zero _ (S.mem_F.1 hf)]

theorem R_le_F : S.R ≤ S.F := fun _ hr => S.mem_F.2 (by rw [S.ν_of_mem hr]; rfl)

theorem conj_mem_A_of_mem_F {f : D} (hf : f ∈ S.F) {a : D} (ha : a ∈ S.A) : f⁻¹ * a * f = a := by
  obtain ⟨B, rfl⟩ := ha
  rw [conj_e, symThreeLinear_zero_of_diag_eq_zero _ (S.mem_F.1 hf)]

theorem commute_of_mem_F {f a : D} (hf : f ∈ S.F) (ha : a ∈ S.A) : f * a = a * f := by
  have h := S.conj_mem_A_of_mem_F hf ha
  calc f * a = f * (f⁻¹ * a * f) := by rw [h]
    _ = a * f := by group

theorem conj_e_one_of_mem_F {f : D} (hf : f ∈ S.F) (B : binarySymMatrices 3) :
    f⁻¹ * S.e B 1 * f = S.e (B + S.ν f) 1 := by
  rw [conj_e, symThreeLinear_one_of_diag_eq_zero _ (S.mem_F.1 hf)]

theorem sq_mem_R (d : D) : d ^ 2 ∈ S.R :=
  S.mem_of_ν_eq_zero (by rw [sq, ν_mul, symThreeAffine_self])

theorem sq_mem_A (d : D) : d ^ 2 ∈ S.A := by
  obtain ⟨B, ε, hB⟩ := S.exists_e (S.sq_mem_R d)
  rcases MatrixExtension.zmod_two_eq_zero_or_one ε with rfl | rfl
  · exact ⟨B, hB⟩
  · exfalso
    have hcomm : d⁻¹ * d ^ 2 * d = d ^ 2 := by group
    rw [hB, conj_e] at hcomm
    have hC := symThreeLinear_one_eq_self (S.e_injective hcomm).1
    obtain ⟨B', ε', hd⟩ := S.exists_e (S.mem_of_ν_eq_zero hC)
    rw [hd, e_sq] at hB
    exact absurd (S.e_injective (hB.symm.trans S.e_zero_zero.symm)).2 (by decide)

theorem commutatorElement_mem_A (x y : D) : ⁅x, y⁆ ∈ S.A := by
  rw [symThree_commutatorElement_eq_sq]
  exact mul_mem (mul_mem (S.sq_mem_A _) (S.sq_mem_A _)) (S.sq_mem_A _)

theorem commutatorElement_z_inv (d : D) : ⁅S.z, d⁻¹⁆ = S.e (S.ν d) 0 := by
  rw [commutatorElement_def, inv_inv,
    show S.z * d⁻¹ * S.z⁻¹ * d = S.z * (d⁻¹ * S.z⁻¹ * d) by group, z_inv, conj_z, z, e_mul,
    zero_add]
  rfl

theorem commutator_eq_A : commutator D = S.A := by
  apply le_antisymm
  · rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact S.commutatorElement_mem_A x y
  · rintro _ ⟨B, rfl⟩
    obtain ⟨d, rfl⟩ := S.surj B
    rw [← commutatorElement_z_inv]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem closure_sq_eq_A : Subgroup.closure {x | ∃ d : D, d ^ 2 = x} = S.A := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨d, rfl⟩
    exact S.sq_mem_A d
  · rw [← S.commutator_eq_A, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [symThree_commutatorElement_eq_sq]
    exact mul_mem (mul_mem (Subgroup.subset_closure ⟨_, rfl⟩) (Subgroup.subset_closure ⟨_, rfl⟩))
      (Subgroup.subset_closure ⟨_, rfl⟩)

theorem card_sym : Nat.card (binarySymMatrices 3) = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_alt : Nat.card {C : binarySymMatrices 3 | symThreeDiag C = 0} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_R : Nat.card S.R = 128 := by
  rw [Nat.card_congr (S.θ.toEquiv.trans Multiplicative.toAdd), Nat.card_prod, card_sym,
    Nat.card_zmod]

theorem card_A : Nat.card S.A = 64 := by
  rw [← card_sym]
  refine (Nat.card_eq_of_bijective (fun B => (⟨S.e B 0, S.e_mem_A B⟩ : S.A)) ⟨?_, ?_⟩).symm
  · intro B B' h
    have h' : S.e B 0 = S.e B' 0 := congrArg (Subtype.val : S.A → D) h
    exact (S.e_injective h').1
  · rintro ⟨_, B, rfl⟩
    exact ⟨B, rfl⟩

include S in
theorem card_eq : Nat.card D = 8192 := by
  have h := symThree_card_eq_card_image_mul (K := ⊤) le_top S.ν
    (fun x _ y _ => S.ν_eq_iff x y)
  rw [Subgroup.card_top, Subgroup.coe_top, Set.image_univ_of_surjective (fun C => S.surj C),
    Nat.card_univ, card_sym, card_R] at h
  exact h

theorem image_F : S.ν '' S.F = {C : binarySymMatrices 3 | symThreeDiag C = 0} := by
  ext C
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact S.mem_F.1 hf
  · intro hC
    obtain ⟨d, rfl⟩ := S.surj C
    exact ⟨d, S.mem_F.2 hC, rfl⟩

theorem card_F : Nat.card S.F = 1024 := by
  have h := symThree_card_eq_card_image_mul S.R_le_F S.ν (fun x _ y _ => S.ν_eq_iff x y)
  rw [image_F, card_alt, card_R] at h
  exact h

theorem mem_F_iff_conj (d : D) : d ∈ S.F ↔ S.z⁻¹ * (d⁻¹ * S.z * d) ∈ S.I := by
  rw [conj_z, z_inv, z, e_mul, zero_add, mem_F]
  exact (S.e_mem_I_iff _).symm

@[expose] def i₀ : binarySymMatrices 3 :=
  symThreeAltSym ![1, 0, 0]

theorem diag_i₀ : symThreeDiag (i₀ : binarySymMatrices 3) = 0 :=
  symThreeDiag_alt _

theorem i₀_ne_zero : (i₀ : binarySymMatrices 3) ≠ 0 := by
  rw [i₀, Ne, symThreeAltSym_eq_zero_iff]
  decide

theorem center_F : (Subgroup.center S.F).map S.F.subtype = S.A := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hx
    have hxR : (x : D) ∈ S.R := by
      apply S.faith
      intro B
      have h' : S.e B 1 * (x : D) = (x : D) * S.e B 1 :=
        congrArg Subtype.val (hx ⟨S.e B 1, S.R_le_F (S.e_mem B 1)⟩)
      change (x : D)⁻¹ * S.e B 1 * (x : D) = S.e B 1
      rw [mul_assoc, h', ← mul_assoc, inv_mul_cancel, one_mul]
    obtain ⟨B, ε, hB⟩ := S.exists_e hxR
    rcases MatrixExtension.zmod_two_eq_zero_or_one ε with rfl | rfl
    · exact ⟨B, hB⟩
    · exfalso
      obtain ⟨f, hf⟩ := S.surj i₀
      have hfF : f ∈ S.F := S.mem_F.2 (by rw [hf]; exact diag_i₀)
      have h' : f * x = x * f := congrArg Subtype.val (hx ⟨f, hfF⟩)
      have hc : f⁻¹ * (x : D) * f = x := by
        rw [mul_assoc, ← h']
        group
      rw [hB, S.conj_e_one_of_mem_F hfF, hf] at hc
      have h0 := (S.e_injective hc).1
      apply i₀_ne_zero
      rw [← add_eq_left (a := B), h0]
  · intro a ha
    refine ⟨⟨a, S.R_le_F (S.A_le_R ha)⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro f
    exact Subtype.ext (S.commute_of_mem_F f.2 ha)

theorem ρ_e (g : GL (Fin 3) (ZMod 2)) (B : binarySymMatrices 3) (ε : ZMod 2) :
    S.ρ g (S.e B ε) = S.e (symThreeCongr g B) ε :=
  S.ρ_apply g B ε

theorem ρ_z (g : GL (Fin 3) (ZMod 2)) : S.ρ g S.z = S.z := by
  rw [z, ρ_e, symThreeCongr_zero]

theorem ν_ρ (g : GL (Fin 3) (ZMod 2)) (d : D) : S.ν (S.ρ g d) = symThreeCongr g (S.ν d) := by
  have h : (S.ρ g d)⁻¹ * S.z * S.ρ g d = S.ρ g (d⁻¹ * S.z * d) := by
    rw [map_mul, map_mul, map_inv, ρ_z]
  rw [conj_z, conj_z, ρ_e] at h
  exact (S.e_injective h).1

theorem ρ_mem_F (g : GL (Fin 3) (ZMod 2)) {d : D} (hd : d ∈ S.F) : S.ρ g d ∈ S.F := by
  rw [mem_F, ν_ρ, symThreeDiag_coe_congr, S.mem_F.1 hd, mulVec_zero]

theorem sq_mem_I {f : D} (hf : f ∈ S.F) : f ^ 2 ∈ S.I := by
  obtain ⟨Q, hQ⟩ := S.sq_mem_A f
  rw [hQ, e_mem_I_iff]
  have hδ := S.mem_F.1 hf
  have key : ∀ g : GL (Fin 3) (ZMod 2), symThreeCongr g (S.ν f) = S.ν f →
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ symThreeDiag Q = symThreeDiag Q := by
    intro g hg
    have hr : f⁻¹ * S.ρ g f ∈ S.R := by rw [← ν_eq_iff, ν_ρ, hg]
    obtain ⟨B, ε, hBε⟩ := S.exists_e hr
    have hgf : S.ρ g f = f * S.e B ε := by
      rw [← hBε]
      group
    have hsq : S.ρ g (f ^ 2) = f ^ 2 * (f⁻¹ * S.e B ε * f) * S.e B ε := by
      rw [map_pow, hgf, sq, sq]
      group
    rw [hQ, ρ_e, conj_e, e_mul, e_mul] at hsq
    rw [← symThreeDiag_coe_congr, (S.e_injective hsq).1, AddSubgroup.coe_add,
      AddSubgroup.coe_add, symThreeDiag_add, symThreeDiag_add,
      symThreeDiag_linear_of_diag_eq_zero _ _ hδ, add_assoc]
    funext k
    simp only [Pi.add_apply, symThree_zmod_add_self, add_zero]
  by_contra hne
  have hν0 : S.ν f ≠ 0 := by
    intro h0
    obtain ⟨B, ε, hB⟩ := S.exists_e (S.mem_of_ν_eq_zero h0)
    rw [hB, e_sq] at hQ
    rw [(S.e_injective (hQ.symm.trans S.e_zero_zero.symm)).1] at hne
    exact hne rfl
  have ht : symThreeOff (S.ν f) ≠ 0 := by
    intro h
    apply hν0
    rw [eq_symThreeAltSym hδ, h, symThreeAltSym_eq_zero_iff]
  obtain ⟨u, w, huw, hcong, hmove⟩ :=
    symThree_alt_stabilizer_moves (symThreeOff (S.ν f)) ht (symThreeDiag Q) hne
  refine hmove (key ⟨symThreeTransvection u w, symThreeTransvection u w, huw, huw⟩ ?_)
  apply Subtype.ext
  rw [coe_symThreeCongr]
  change symThreeTransvection u w * (S.ν f : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
    (symThreeTransvection u w)ᵀ = S.ν f
  rw [eq_symThreeAlt (S.ν f).2 hδ]
  exact hcong

theorem commutator_F_eq_I : ⁅S.F, S.F⁆ = S.I := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [symThree_commutatorElement_eq_sq]
    exact mul_mem (mul_mem (S.sq_mem_I (mul_mem hx hy))
      (S.sq_mem_I (mul_mem (mul_mem (inv_mem hy) (inv_mem hx)) hy))) (S.sq_mem_I (inv_mem hy))
  · rintro _ ⟨B, hB, rfl⟩
    obtain ⟨d, rfl⟩ := S.surj B
    rw [← commutatorElement_z_inv]
    exact Subgroup.commutator_mem_commutator (S.R_le_F S.z_mem) (inv_mem (S.mem_F.2 hB))

theorem closure_sq_F_eq_I : Subgroup.closure {x | ∃ f ∈ S.F, f ^ 2 = x} = S.I := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨f, hf, rfl⟩
    exact S.sq_mem_I hf
  · rw [← S.commutator_F_eq_I, Subgroup.commutator_le]
    intro x hx y hy
    rw [symThree_commutatorElement_eq_sq]
    exact mul_mem (mul_mem (Subgroup.subset_closure ⟨_, mul_mem hx hy, rfl⟩)
      (Subgroup.subset_closure ⟨_, mul_mem (mul_mem (inv_mem hy) (inv_mem hx)) hy, rfl⟩))
      (Subgroup.subset_closure ⟨_, inv_mem hy, rfl⟩)

theorem commutatorElement_mem_I {x y : D} (hx : x ∈ S.F) (hy : y ∈ S.F) : ⁅x, y⁆ ∈ S.I := by
  rw [← S.commutator_F_eq_I]
  exact Subgroup.commutator_mem_commutator hx hy

theorem commutatorElement_mul_right_of_mem_F (x : D) {y : D} (hy : y ∈ S.F) (w : D) :
    ⁅x, y * w⁆ = ⁅x, y⁆ * ⁅x, w⁆ := by
  have h : ⁅x, y * w⁆ = ⁅x, y⁆ * (y * ⁅x, w⁆ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [h, S.commute_of_mem_F hy (S.commutatorElement_mem_A x w), mul_assoc, mul_inv_cancel,
    mul_one]

theorem commutatorElement_eq_one_of_mem_A {x a : D} (hx : x ∈ S.F) (ha : a ∈ S.A) :
    ⁅x, a⁆ = 1 :=
  commutatorElement_eq_one_iff_commute.2 (S.commute_of_mem_F hx ha)

@[expose] def φ : MulAut D :=
  S.ρ symThreeSinger

theorem φ_z : S.φ S.z = S.z :=
  S.ρ_z _

theorem φ_e (B : binarySymMatrices 3) (ε : ZMod 2) :
    S.φ (S.e B ε) = S.e (symThreeCongr symThreeSinger B) ε :=
  S.ρ_e _ _ _

theorem ν_φ (d : D) : S.ν (S.φ d) = symThreeCongr symThreeSinger (S.ν d) :=
  S.ν_ρ _ d

theorem φ_mem_F {d : D} (hd : d ∈ S.F) : S.φ d ∈ S.F :=
  S.ρ_mem_F _ hd

@[expose] def IsMiddle (E : Subgroup D) : Prop :=
  E ≤ S.F ∧ IsMulCommutative E ∧ E ⊓ S.R = S.A ∧
    S.ν '' E = {C : binarySymMatrices 3 | symThreeDiag C = 0}

theorem exists_coherent : ∃ e₀ : D, e₀ ∈ S.F ∧ S.ν e₀ = i₀ ∧
    (e₀ * S.φ (S.φ e₀))⁻¹ * S.φ (S.φ (S.φ e₀)) ∈ S.A := by
  have hT3 : symThreeCongr symThreeSinger (symThreeCongr symThreeSinger
      (symThreeCongr symThreeSinger i₀)) =
      i₀ + symThreeCongr symThreeSinger (symThreeCongr symThreeSinger i₀) :=
    Subtype.ext symThreeSingerCongr_cube
  obtain ⟨f, hf⟩ := S.surj i₀
  have hfF : f ∈ S.F := S.mem_F.2 (by rw [hf]; exact diag_i₀)
  have hr : (f * S.φ (S.φ f))⁻¹ * S.φ (S.φ (S.φ f)) ∈ S.R := by
    rw [← ν_eq_iff, S.ν_mul_of_mem_F _ (S.φ_mem_F (S.φ_mem_F hfF)), ν_φ, ν_φ, ν_φ, ν_φ, ν_φ, hf,
      hT3]
  rcases S.mem_A_or_of_mem_R hr with h | h
  · exact ⟨f, hfF, hf, h⟩
  · refine ⟨f * S.z, mul_mem hfF (S.R_le_F S.z_mem), by rw [S.ν_mul_mem_R _ S.z_mem, hf], ?_⟩
    rw [map_mul, map_mul, map_mul, φ_z, φ_z, φ_z]
    have key : (f * S.z * (S.φ (S.φ f) * S.z))⁻¹ * (S.φ (S.φ (S.φ f)) * S.z) =
        S.z⁻¹ * (⁅(S.φ (S.φ f))⁻¹, S.z⁻¹⁆ *
          (S.z⁻¹ * ((f * S.φ (S.φ f))⁻¹ * S.φ (S.φ (S.φ f))))) * S.z := by
      rw [commutatorElement_def]
      group
    have hc : ⁅(S.φ (S.φ f))⁻¹, S.z⁻¹⁆ *
        (S.z⁻¹ * ((f * S.φ (S.φ f))⁻¹ * S.φ (S.φ (S.φ f)))) ∈ S.A :=
      mul_mem (S.commutatorElement_mem_A _ _) h
    rw [key, mul_assoc, S.mem_comm (S.A_le_R hc) S.z_mem, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hc

theorem exists_middle : ∃ E : Subgroup D, S.IsMiddle E := by
  obtain ⟨e₀, he₀F, he₀ν, he₀c⟩ := S.exists_coherent
  have he₁F : S.φ e₀ ∈ S.F := S.φ_mem_F he₀F
  have he₂F : S.φ (S.φ e₀) ∈ S.F := S.φ_mem_F he₁F
  obtain ⟨X, hXδ, hX⟩ := S.commutatorElement_mem_I he₀F he₁F
  obtain ⟨Y, hYδ, hY⟩ := S.commutatorElement_mem_I he₀F he₂F
  have h3 : S.φ (S.φ (S.φ e₀)) = e₀ * S.φ (S.φ e₀) *
      ((e₀ * S.φ (S.φ e₀))⁻¹ * S.φ (S.φ (S.φ e₀))) := by
    group
  have h12 : ⁅S.φ e₀, S.φ (S.φ e₀)⁆ = S.e (symThreeCongr symThreeSinger X) 0 := by
    rw [← map_commutatorElement, hX, φ_e]
  have hE1 : symThreeCongr symThreeSinger Y = X + symThreeCongr symThreeSinger X := by
    have h1 : ⁅S.φ e₀, S.φ (S.φ (S.φ e₀))⁆ = S.e (symThreeCongr symThreeSinger Y) 0 := by
      rw [← map_commutatorElement, hY, φ_e]
    rw [h3, S.commutatorElement_mul_right_of_mem_F _ (mul_mem he₀F he₂F),
      S.commutatorElement_eq_one_of_mem_A he₁F he₀c, mul_one,
      S.commutatorElement_mul_right_of_mem_F _ he₀F, ← commutatorElement_inv, hX,
      e_inv, h12, e_mul, add_zero] at h1
    exact (S.e_injective h1).1.symm
  have hE2 : symThreeCongr symThreeSinger (symThreeCongr symThreeSinger X) = Y := by
    have h2 : ⁅S.φ (S.φ e₀), S.φ (S.φ (S.φ e₀))⁆ =
        S.e (symThreeCongr symThreeSinger (symThreeCongr symThreeSinger X)) 0 := by
      rw [← map_commutatorElement, h12, φ_e]
    rw [h3, S.commutatorElement_mul_right_of_mem_F _ (mul_mem he₀F he₂F),
      S.commutatorElement_eq_one_of_mem_A he₂F he₀c, mul_one,
      S.commutatorElement_mul_right_of_mem_F _ he₀F, commutatorElement_self, mul_one,
      ← commutatorElement_inv, hY, e_inv] at h2
    exact (S.e_injective h2).1.symm
  have hX0 : X = 0 := by
    have hcube : symThreeCongr symThreeSinger (symThreeCongr symThreeSinger
        (symThreeCongr symThreeSinger X)) = X + symThreeCongr symThreeSinger X := by
      rw [hE2, hE1]
    rw [eq_symThreeAltSym hXδ] at hcube ⊢
    rw [symThreeAltSym_eq_zero_iff]
    exact symThreeSingerCongr_cube_eq _ (congrArg Subtype.val hcube)
  have hY0 : Y = 0 := by
    rw [← hE2, hX0, symThreeCongr_zero, symThreeCongr_zero]
  have hc01 : Commute e₀ (S.φ e₀) := by
    rw [← commutatorElement_eq_one_iff_commute, hX, hX0, e_zero_zero]
  have hc02 : Commute e₀ (S.φ (S.φ e₀)) := by
    rw [← commutatorElement_eq_one_iff_commute, hY, hY0, e_zero_zero]
  have hc12 : Commute (S.φ e₀) (S.φ (S.φ e₀)) := by
    rw [← commutatorElement_eq_one_iff_commute, h12, hX0, symThreeCongr_zero, e_zero_zero]
  set k : Set D := (S.A : Set D) ∪ {e₀, S.φ e₀, S.φ (S.φ e₀)} with hk
  have hkF : k ⊆ S.F := by
    rintro x (hx | hx | hx | hx)
    · exact S.R_le_F (S.A_le_R hx)
    · exact hx ▸ he₀F
    · exact hx ▸ he₁F
    · exact hx ▸ he₂F
  have hpair : k.Pairwise Commute := by
    have hA : ∀ {a x : D}, a ∈ S.A → x ∈ k → Commute a x := fun ha hx =>
      (S.commute_of_mem_F (hkF hx) ha).symm
    rintro x hx y hy -
    rcases hx with hx | hx | hx | hx
    · exact hA hx hy
    · rcases hy with hy | hy | hy | hy
      · exact (hA hy (Or.inr (Or.inl hx))).symm
      · rw [hx, hy]
      · rw [hx, hy]
        exact hc01
      · rw [Set.mem_singleton_iff] at hy
        rw [hx, hy]
        exact hc02
    · rcases hy with hy | hy | hy | hy
      · exact (hA hy (Or.inr (Or.inr (Or.inl hx)))).symm
      · rw [hx, hy]
        exact hc01.symm
      · rw [hx, hy]
      · rw [Set.mem_singleton_iff] at hy
        rw [hx, hy]
        exact hc12
    · rw [Set.mem_singleton_iff] at hx
      rcases hy with hy | hy | hy | hy
      · exact (hA hy (Or.inr (Or.inr (Or.inr hx)))).symm
      · rw [hx, hy]
        exact hc02.symm
      · rw [hx, hy]
        exact hc12.symm
      · rw [Set.mem_singleton_iff] at hy
        rw [hx, hy]
  have hEF : Subgroup.closure k ≤ S.F := (Subgroup.closure_le _).2 hkF
  have hcomm : IsMulCommutative (Subgroup.closure k) := Subgroup.isMulCommutative_closure hpair
  have hAE : S.A ≤ Subgroup.closure k := fun a ha => Subgroup.subset_closure (Or.inl ha)
  have he₀E : e₀ ∈ Subgroup.closure k := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have he₁E : S.φ e₀ ∈ Subgroup.closure k :=
    Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  have he₂E : S.φ (S.φ e₀) ∈ Subgroup.closure k :=
    Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))
  have hzE : S.z ∉ Subgroup.closure k := by
    intro hz
    have h := setLike_mul_comm hz he₀E
    have hc : e₀⁻¹ * S.z * e₀ = S.z := by
      rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [conj_z, z] at hc
    exact i₀_ne_zero (he₀ν ▸ (S.e_injective hc).1)
  refine ⟨Subgroup.closure k, hEF, hcomm, le_antisymm ?_ (le_inf hAE S.A_le_R), ?_⟩
  · intro x hx
    obtain ⟨hxE, hxR⟩ := Subgroup.mem_inf.1 hx
    rcases S.mem_A_or_of_mem_R hxR with h | h
    · exact h
    · exfalso
      apply hzE
      have := mul_mem hxE (inv_mem (hAE h))
      rwa [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact S.mem_F.1 (hEF hx)
    · intro C hC
      obtain ⟨a, b, c, habc⟩ := symThreeSingerCongr_span (symThreeOff C)
      refine ⟨(if a then e₀ else 1) * (if b then S.φ e₀ else 1) *
        (if c then S.φ (S.φ e₀) else 1), ?_, ?_⟩
      · refine mul_mem (mul_mem ?_ ?_) ?_
        · split_ifs
          · exact he₀E
          · exact (Subgroup.closure k).one_mem
        · split_ifs
          · exact he₁E
          · exact (Subgroup.closure k).one_mem
        · split_ifs
          · exact he₂E
          · exact (Subgroup.closure k).one_mem
      · have hif : ∀ (p : Bool) {x : D}, x ∈ S.F → (if p then x else 1) ∈ S.F := by
          intro p x hx
          split_ifs
          · exact hx
          · exact S.F.one_mem
        rw [S.ν_mul_of_mem_F _ (hif c he₂F), S.ν_mul_of_mem_F _ (hif b he₁F)]
        apply Subtype.ext
        rw [eq_symThreeAlt C.2 hC, habc]
        simp only [AddSubgroup.coe_add]
        congr 1
        · congr 1
          · split_ifs
            · rw [he₀ν]
              rfl
            · rw [ν_one]
              rfl
          · split_ifs
            · rw [ν_φ, he₀ν]
              rfl
            · rw [ν_one]
              rfl
        · split_ifs
          · rw [ν_φ, ν_φ, he₀ν]
            rfl
          · rw [ν_one]
            rfl

theorem iterate_φ_e (k : ℕ) (B : binarySymMatrices 3) :
    (S.φ)^[k] (S.e B 0) = S.e ((symThreeCongr symThreeSinger)^[k] B) 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, φ_e, Function.iterate_succ_apply']

theorem A_normal : S.A.Normal := by
  rw [← S.commutator_eq_A, commutator_def]
  infer_instance

theorem F_normal : S.F.Normal :=
  MonoidHom.normal_ker _

theorem relIndex_F (E : Subgroup D) (hEF : E ≤ S.F) (hE : Nat.card E = 512) :
    E.relIndex S.F = 2 := by
  have h := Subgroup.card_mul_index (E.subgroupOf S.F)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEF).toEquiv, hE, S.card_F] at h
  change 512 * E.relIndex S.F = 1024 at h
  omega

namespace IsMiddle

variable {S} {E : Subgroup D} (hE : S.IsMiddle E)
include hE

theorem le_F : E ≤ S.F :=
  hE.1

theorem isMulCommutative : IsMulCommutative E :=
  hE.2.1

theorem inf_R : E ⊓ S.R = S.A :=
  hE.2.2.1

theorem image : S.ν '' E = {C : binarySymMatrices 3 | symThreeDiag C = 0} :=
  hE.2.2.2

theorem A_le : S.A ≤ E :=
  hE.inf_R.symm.le.trans inf_le_left

theorem mem_A_of_mem_R {x : D} (hx : x ∈ E) (hxR : x ∈ S.R) : x ∈ S.A := by
  rw [← hE.inf_R]
  exact Subgroup.mem_inf.2 ⟨hx, hxR⟩

theorem card : Nat.card E = 512 := by
  have h := symThree_card_eq_card_image_mul hE.A_le S.ν (fun x hx y hy => by
    rw [ν_eq_iff]
    exact ⟨fun h => hE.mem_A_of_mem_R (mul_mem (inv_mem hx) hy) h, fun h => S.A_le_R h⟩)
  rw [hE.image, card_alt, card_A] at h
  exact h

theorem mem_or {f : D} (hf : f ∈ S.F) : f ∈ E ∨ S.z⁻¹ * f ∈ E := by
  have hfi : S.ν f ∈ S.ν '' E := by
    rw [hE.image]
    exact S.mem_F.1 hf
  obtain ⟨e, he, hef⟩ := hfi
  rcases S.mem_A_or_of_mem_R ((S.ν_eq_iff' e f).1 hef) with h | h
  · left
    have := mul_mem (hE.A_le h) he
    rwa [inv_mul_cancel_right] at this
  · right
    have := mul_mem (hE.A_le h) he
    rwa [mul_assoc, inv_mul_cancel_right] at this

theorem set_eq : (S.F : Set D) = (Subgroup.zpowers S.z : Set D) * (E : Set D) := by
  ext f
  rw [Set.mem_mul]
  constructor
  · intro hf
    rcases hE.mem_or hf with h | h
    · exact ⟨1, Subgroup.one_mem _, f, h, one_mul f⟩
    · exact ⟨S.z, Subgroup.mem_zpowers _, S.z⁻¹ * f, h, mul_inv_cancel_left _ _⟩
  · rintro ⟨x, hx, e, he, rfl⟩
    refine mul_mem ?_ (hE.le_F he)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact zpow_mem (S.R_le_F S.z_mem) n

theorem mem_A_of_commute {y y' : D} (hy : y ∈ S.F) (hyE : y ∉ E) (hy' : y' ∈ E)
    (hc : y * y' = y' * y) : y' ∈ S.A := by
  have he : S.z⁻¹ * y ∈ E := (hE.mem_or hy).resolve_left hyE
  have : IsMulCommutative E := hE.isMulCommutative
  have hee : S.z⁻¹ * y * y' = y' * (S.z⁻¹ * y) := setLike_mul_comm he hy'
  have hz : y'⁻¹ * S.z * y' = S.z := by
    have h1 : S.z * (S.z⁻¹ * y) * y' = y' * S.z * (S.z⁻¹ * y) := by
      rw [mul_inv_cancel_left, hc]
      group
    rw [mul_assoc, hee, ← mul_assoc] at h1
    have h2 := mul_right_cancel h1
    rw [mul_assoc, h2, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [conj_z, z] at hz
  exact hE.mem_A_of_mem_R hy' (S.mem_of_ν_eq_zero (S.e_injective hz).1)

theorem relIndex_eq : E.relIndex S.F = 2 :=
  S.relIndex_F E hE.le_F hE.card

theorem le_of_four_le {Y : Subgroup D} (hYF : Y ≤ S.F) [IsMulCommutative Y]
    (h4 : 4 ≤ S.A.relIndex (Y ⊔ S.A)) : Y ≤ E := by
  have := S.A_normal
  rw [Subgroup.relIndex_sup_right] at h4
  by_contra hne
  obtain ⟨y, hyY, hyE⟩ := Set.not_subset.1 hne
  have hinf : S.A ⊓ Y = E ⊓ Y := by
    apply le_antisymm
    · exact inf_le_inf_right _ hE.A_le
    · intro x hx
      obtain ⟨hxE, hxY⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨hE.mem_A_of_commute (hYF hyY) hyE hxE
        (setLike_mul_comm hyY hxY), hxY⟩
  have h2 : E.relIndex Y ≤ 2 := by
    rw [← hE.relIndex_eq]
    exact Subgroup.relIndex_le_of_le_right hYF (by rw [hE.relIndex_eq]; norm_num)
  rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right] at h4
  omega

theorem eq_of_card {E' : Subgroup D} (hE'F : E' ≤ S.F) [IsMulCommutative E']
    (hcard : Nat.card E' = 512) : E' = E := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hE.card]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge (hE.le_of_four_le hE'F ?_) (by rw [hE.card, hcard])
  have := S.A_normal
  rw [Subgroup.relIndex_sup_right]
  have h := Subgroup.card_mul_index (S.A.subgroupOf E')
  have hfinA : Finite S.A := Nat.finite_of_card_ne_zero (by rw [S.card_A]; norm_num)
  have hle : Nat.card (S.A.subgroupOf E') ≤ 64 := by
    rw [← S.card_A]
    exact Nat.card_le_card_of_injective (fun x => (⟨x.1.1, x.2⟩ : S.A)) (fun x y hxy => by
      have h' : x.1.1 = y.1.1 := congrArg (Subtype.val : S.A → D) hxy
      exact Subtype.ext (Subtype.ext h'))
  rw [hcard] at h
  change Nat.card (S.A.subgroupOf E') * S.A.relIndex E' = 512 at h
  by_contra hlt
  rw [not_le] at hlt
  have : Nat.card (S.A.subgroupOf E') * S.A.relIndex E' ≤ 64 * 3 :=
    Nat.mul_le_mul hle (by omega)
  omega

theorem map_eq (f : D ≃* D) (hf : ∀ x ∈ S.F, f x ∈ S.F) : E.map f.toMonoidHom = E := by
  have : IsMulCommutative E := hE.isMulCommutative
  refine hE.eq_of_card ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hf x (hE.le_F hx)
  · rw [Subgroup.card_map_of_injective f.injective, hE.card]

theorem normal : E.Normal := by
  constructor
  intro n hn g
  have h := hE.map_eq (MulAut.conj g) (fun x hx => S.F_normal.conj_mem x hx g)
  rw [← h]
  exact ⟨n, hn, rfl⟩

theorem ρ_invariant (g : GL (Fin 3) (ZMod 2)) : E.map (S.ρ g).toMonoidHom = E :=
  hE.map_eq (S.ρ g) (fun _ hx => S.ρ_mem_F g hx)

theorem characteristic : (E.subgroupOf S.F).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro ψ
  have : IsMulCommutative E := hE.isMulCommutative
  have h : ((E.subgroupOf S.F).map ψ.toMonoidHom).map S.F.subtype = E := by
    refine hE.eq_of_card (Subgroup.map_subtype_le _) ?_
    rw [Subgroup.card_map_of_injective S.F.subtype_injective,
      Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE.le_F).toEquiv, hE.card]
  have h2 := congrArg (Subgroup.comap S.F.subtype) h
  rw [Subgroup.comap_map_eq_self_of_injective S.F.subtype_injective] at h2
  exact h2

theorem φ_mem {x : D} (hx : x ∈ E) : S.φ x ∈ E := by
  rw [← hE.ρ_invariant symThreeSinger]
  exact ⟨x, hx, rfl⟩

theorem closure_sq : Subgroup.closure {x | ∃ e ∈ E, e ^ 2 = x} = ⊥ ∨
    Subgroup.closure {x | ∃ e ∈ E, e ^ 2 = x} = S.I := by
  set Q := Subgroup.closure {x | ∃ e ∈ E, e ^ 2 = x} with hQ
  have hQI : Q ≤ S.I := by
    rw [Subgroup.closure_le]
    rintro _ ⟨e, he, rfl⟩
    exact S.sq_mem_I (hE.le_F he)
  have hφQ : ∀ x ∈ Q, S.φ x ∈ Q := by
    intro x hx
    have h : Q.map (S.φ).toMonoidHom ≤ Q := by
      rw [hQ, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
      exact ⟨S.φ e, hE.φ_mem he, by simp⟩
    exact h ⟨x, hx, rfl⟩
  have hiter : ∀ k : ℕ, ∀ x ∈ Q, (S.φ)^[k] x ∈ Q := by
    intro k
    induction k with
    | zero => exact fun x hx => hx
    | succ k ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact hφQ _ (ih x hx)
  by_cases hbot : Q = ⊥
  · exact Or.inl hbot
  · right
    apply le_antisymm hQI
    obtain ⟨⟨x, hxQ⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
    obtain ⟨B, hB, rfl⟩ := hQI hxQ
    have hB0 : symThreeOff B ≠ 0 := by
      intro h
      apply hx1
      apply Subtype.ext
      change S.e B 0 = 1
      rw [eq_symThreeAltSym hB, h, (symThreeAltSym_eq_zero_iff 0).2 rfl, e_zero_zero]
    rintro _ ⟨B', hB', rfl⟩
    by_cases hB'0 : symThreeOff B' = 0
    · rw [eq_symThreeAltSym hB', hB'0, (symThreeAltSym_eq_zero_iff 0).2 rfl, e_zero_zero]
      exact Q.one_mem
    · obtain ⟨k, hk⟩ := symThreeSingerCongr_transitive _ _ hB0 hB'0
      have h := hiter k _ hxQ
      rw [iterate_φ_e] at h
      convert h using 2
      apply Subtype.ext
      rw [coe_iterate_symThreeCongr_singer, eq_symThreeAlt B.2 hB, hk,
        ← eq_symThreeAlt B'.2 hB']

end IsMiddle

end SymThreeCosetData

theorem binary_symmetric_three_full_coset_characteristic_abelian_middle_subgroup
    {D : Type*} [Group D] (R : Subgroup D) [R.Normal]
    (θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2)) (κ : ZMod 2)
    (hact : ∀ d : D, ∃ C : binarySymMatrices 3, ∀ B : binarySymMatrices 3,
      d⁻¹ * (θ.symm (.ofAdd (B, 1)) : D) * d = θ.symm (.ofAdd (symThreeAffine κ C B, 1)))
    (hsurj : ∀ C : binarySymMatrices 3, ∃ d : D, ∀ B : binarySymMatrices 3,
      d⁻¹ * (θ.symm (.ofAdd (B, 1)) : D) * d = θ.symm (.ofAdd (symThreeAffine κ C B, 1)))
    (hfaith : ∀ d : D, (∀ B : binarySymMatrices 3,
      d⁻¹ * (θ.symm (.ofAdd (B, 1)) : D) * d = θ.symm (.ofAdd (B, 1))) → d ∈ R)
    (ρ : GL (Fin 3) (ZMod 2) →* MulAut D)
    (hρ : ∀ (g : GL (Fin 3) (ZMod 2)) (B : binarySymMatrices 3) (ε : ZMod 2),
      ρ g (θ.symm (.ofAdd (B, ε)) : D) = θ.symm (.ofAdd (symThreeCongr g B, ε)))
    (z : D) (hz : z = θ.symm (.ofAdd (0, 1))) (A I : Subgroup D)
    (hA : ∀ x : D, x ∈ A ↔ ∃ B : binarySymMatrices 3, x = θ.symm (.ofAdd (B, 0)))
    (hI : ∀ x : D, x ∈ I ↔ ∃ B : binarySymMatrices 3,
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ binaryAltMatrices 3 ∧
        x = θ.symm (.ofAdd (B, 0))) :
    Nat.card D = 8192 ∧ commutator D = A ∧ Subgroup.closure {x | ∃ d : D, d ^ 2 = x} = A ∧
    ∃ F : Subgroup D, (∀ d : D, d ∈ F ↔ z⁻¹ * (d⁻¹ * z * d) ∈ I) ∧ Nat.card F = 1024 ∧
      (Subgroup.center F).map F.subtype = A ∧ ⁅F, F⁆ = I ∧
      Subgroup.closure {x | ∃ f ∈ F, f ^ 2 = x} = I ∧
      ∃ E₂ : Subgroup D, (E₂ ≤ F ∧ IsMulCommutative E₂ ∧ Nat.card E₂ = 512) ∧
        (∀ E : Subgroup D, E ≤ F → IsMulCommutative E → Nat.card E = 512 → E = E₂) ∧
        (E₂.subgroupOf F).Characteristic ∧ E₂.Normal ∧
        (∀ g : GL (Fin 3) (ZMod 2), E₂.map (ρ g).toMonoidHom = E₂) ∧
        (F : Set D) = (Subgroup.zpowers z : Set D) * (E₂ : Set D) ∧ E₂ ⊓ R = A ∧
        (∀ Y : Subgroup D, Y ≤ F → IsMulCommutative Y → 4 ≤ A.relIndex (Y ⊔ A) → Y ≤ E₂) ∧
        (Subgroup.closure {x | ∃ e ∈ E₂, e ^ 2 = x} = ⊥ ∨
          Subgroup.closure {x | ∃ e ∈ E₂, e ^ 2 = x} = I) := by
  let S : SymThreeCosetData D :=
    { R := R
      normal := inferInstance
      θ := θ
      κ := κ
      ρ := ρ
      ν := fun d => Classical.choose (hact d)
      conj_one := fun d => Classical.choose_spec (hact d)
      surj := fun C => by
        obtain ⟨d, hd⟩ := hsurj C
        refine ⟨d, ?_⟩
        have h1 := Classical.choose_spec (hact d) 0
        rw [hd 0, symThreeAffine_zero_right, symThreeAffine_zero_right] at h1
        exact (Prod.mk.inj (Multiplicative.ofAdd.injective
          (θ.symm.injective (Subtype.ext h1)))).1.symm
      faith := hfaith
      ρ_apply := hρ }
  have hAS : A = S.A := by
    ext x
    rw [hA]
    rfl
  have hIS : I = S.I := by
    ext x
    rw [hI, S.mem_I]
    refine exists_congr fun B => and_congr_left fun _ => ?_
    rw [mem_binaryAltMatrices]
    exact ⟨fun h => funext h.2, fun h => ⟨B.2, fun i => congrFun h i⟩⟩
  have hzS : z = S.z := hz
  subst hAS hIS hzS
  obtain ⟨E, hE⟩ := S.exists_middle
  have hEc := hE.isMulCommutative
  exact ⟨S.card_eq, S.commutator_eq_A, S.closure_sq_eq_A, S.F, S.mem_F_iff_conj, S.card_F,
    S.center_F, S.commutator_F_eq_I, S.closure_sq_F_eq_I, E, ⟨hE.le_F, hEc, hE.card⟩,
    fun E' hE'F _ hE'card => hE.eq_of_card hE'F hE'card, hE.characteristic, hE.normal,
    hE.ρ_invariant, hE.set_eq, hE.inf_R, fun Y hYF _ h4 => hE.le_of_four_le hYF h4,
    hE.closure_sq⟩

end CFSG.LocalAnalysis.ComponentInitial
