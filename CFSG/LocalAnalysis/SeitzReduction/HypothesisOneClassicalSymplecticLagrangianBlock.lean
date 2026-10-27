module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplecticNormalForm
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLagrangian

public section

namespace CFSG.SeitzReduction

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open SymplecticTorusWeyl (leviSp coe_leviSp)

namespace SymplecticLagrangian

section Generic

variable {G : Type*} [Group G] {s : G}

theorem mem_closure_odd_of_mem {c : G} (hc : c ∈ centralizer {s}) (ho : Odd (orderOf c)) :
    c ∈ closure {c : G | c ∈ centralizer {s} ∧ Odd (orderOf c)} :=
  subset_closure ⟨hc, ho⟩

theorem mul_conj_inv_mem_closure_odd {x y : G} (hx : x ∈ centralizer {s})
    (ho : Odd (orderOf x)) (hy : y ∈ centralizer {s}) :
    x * (y * x⁻¹ * y⁻¹) ∈ closure {c : G | c ∈ centralizer {s} ∧ Odd (orderOf c)} := by
  refine mul_mem (subset_closure ⟨hx, ho⟩) (subset_closure ⟨?_, ?_⟩)
  · exact mul_mem (mul_mem hy (inv_mem hx)) (inv_mem hy)
  · rw [show y * x⁻¹ * y⁻¹ = MulAut.conj y x⁻¹ from rfl, MulEquiv.orderOf_eq, orderOf_inv]
    exact ho

end Generic

variable {r : ℕ} {K : Type} [Field K]

theorem transpose_conj_eq {A T : Matrix (Fin r) (Fin r) K} (hT : Tᵀ = T) :
    (A * T * Aᵀ)ᵀ = A * T * Aᵀ := by
  rw [transpose_mul, transpose_mul, transpose_transpose, hT, Matrix.mul_assoc]

theorem transpose_conj_sub_eq {A T : Matrix (Fin r) (Fin r) K} (hT : Tᵀ = T) :
    (A * T * Aᵀ - T)ᵀ = A * T * Aᵀ - T := by
  rw [transpose_sub, transpose_conj_eq hT, hT]

theorem transpose_smul_eq {T : Matrix (Fin r) (Fin r) K} (hT : Tᵀ = T) (c : K) :
    (c • T)ᵀ = c • T := by
  rw [transpose_smul, hT]

theorem upperUnipotentSp_eq_of_eq {C D : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = C) (hD : Dᵀ = D)
    (h : C = D) : upperUnipotentSp r K hC = upperUnipotentSp r K hD := by
  subst h
  rfl

theorem upperUnipotentSp_mul_upperUnipotentSp {C D : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = C)
    (hD : Dᵀ = D) :
    upperUnipotentSp r K hC * upperUnipotentSp r K hD =
      upperUnipotentSp r K (show (C + D)ᵀ = C + D by rw [transpose_add, hC, hD]) := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_upperUnipotentSp, coe_upperUnipotentSp,
    coe_upperUnipotentSp, fromBlocks_multiply]
  simp [add_comm]

theorem upperUnipotentSp_zero_eq_one :
    upperUnipotentSp r K (show (0 : Matrix (Fin r) (Fin r) K)ᵀ = 0 from transpose_zero) = 1 := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_upperUnipotentSp, fromBlocks_one]
  rfl

theorem upperUnipotentSp_inv {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = C) :
    (upperUnipotentSp r K hC)⁻¹ =
      upperUnipotentSp r K (show (-C)ᵀ = -C by rw [transpose_neg, hC]) := by
  rw [inv_eq_iff_mul_eq_one, upperUnipotentSp_mul_upperUnipotentSp, ← upperUnipotentSp_zero_eq_one]
  exact upperUnipotentSp_eq_of_eq _ _ (add_neg_cancel C)

theorem leviSp_conj_upperUnipotentSp (A : GL (Fin r) K) {T : Matrix (Fin r) (Fin r) K}
    (hT : Tᵀ = T) :
    leviSp A * upperUnipotentSp r K hT * (leviSp A)⁻¹ =
      upperUnipotentSp r K (transpose_conj_eq (A := (A : Matrix (Fin r) (Fin r) K)) hT) := by
  apply SymplecticTorusWeyl.statedSp_ext
  have hA : (A : Matrix (Fin r) (Fin r) K) * ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_leviSp,
    coe_leviSp, coe_upperUnipotentSp, coe_upperUnipotentSp, fromBlocks_multiply,
    fromBlocks_multiply, inv_inv]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
  rw [hA, ← transpose_mul, hA, transpose_one]

theorem upperUnipotentSp_mem_centralizer {S T : Matrix (Fin r) (Fin r) K} (hS : Sᵀ = S)
    (hT : Tᵀ = T) : upperUnipotentSp r K hT ∈ centralizer {upperUnipotentSp r K hS} := by
  rw [mem_centralizer_singleton_iff, upperUnipotentSp_mul_upperUnipotentSp,
    upperUnipotentSp_mul_upperUnipotentSp]
  exact upperUnipotentSp_eq_of_eq _ _ (add_comm T S)

theorem leviSp_mem_centralizer {S : Matrix (Fin r) (Fin r) K} (hS : Sᵀ = S) {A : GL (Fin r) K}
    (hA : (A : Matrix (Fin r) (Fin r) K) * S * (A : Matrix (Fin r) (Fin r) K)ᵀ = S) :
    leviSp A ∈ centralizer {upperUnipotentSp r K hS} := by
  rw [mem_centralizer_singleton_iff]
  have h := leviSp_conj_upperUnipotentSp A hS
  rw [upperUnipotentSp_eq_of_eq _ hS hA] at h
  calc leviSp A * upperUnipotentSp r K hS
      = leviSp A * upperUnipotentSp r K hS * (leviSp A)⁻¹ * leviSp A := by group
    _ = upperUnipotentSp r K hS * leviSp A := by rw [h]

theorem odd_orderOf_leviSp {A : GL (Fin r) K} (hA : A ^ 3 = 1) : Odd (orderOf (leviSp A)) :=
  (by decide : Odd 3).of_dvd_nat (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hA, map_one]))

theorem leviSp_mem_closure_odd {S : Matrix (Fin r) (Fin r) K} (hS : Sᵀ = S) {A : GL (Fin r) K}
    (hA : (A : Matrix (Fin r) (Fin r) K) * S * (A : Matrix (Fin r) (Fin r) K)ᵀ = S)
    (hA3 : A ^ 3 = 1) :
    leviSp A ∈
      closure {c : StatedSp r K | c ∈ centralizer {upperUnipotentSp r K hS} ∧ Odd (orderOf c)} :=
  mem_closure_odd_of_mem (leviSp_mem_centralizer hS hA) (odd_orderOf_leviSp hA3)

theorem upperUnipotentSp_sub_mem_closure_odd {S : Matrix (Fin r) (Fin r) K} (hS : Sᵀ = S)
    {A : GL (Fin r) K}
    (hA : (A : Matrix (Fin r) (Fin r) K) * S * (A : Matrix (Fin r) (Fin r) K)ᵀ = S)
    (hA3 : A ^ 3 = 1) {T : Matrix (Fin r) (Fin r) K} (hT : Tᵀ = T) :
    upperUnipotentSp r K (transpose_conj_sub_eq (A := (A : Matrix (Fin r) (Fin r) K)) hT) ∈
      closure {c : StatedSp r K | c ∈ centralizer {upperUnipotentSp r K hS} ∧ Odd (orderOf c)} := by
  have h := mul_conj_inv_mem_closure_odd (leviSp_mem_centralizer hS hA) (odd_orderOf_leviSp hA3)
    (upperUnipotentSp_mem_centralizer hS hT)
  convert h using 1
  rw [← mul_assoc, ← mul_assoc, leviSp_conj_upperUnipotentSp, upperUnipotentSp_inv,
    upperUnipotentSp_mul_upperUnipotentSp]
  exact upperUnipotentSp_eq_of_eq _ _ (sub_eq_add_neg _ _)

theorem fromBlocks_one_eq_one_add (Y : Matrix (Fin r) (Fin r) K) :
    (fromBlocks 1 Y 0 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + fromBlocks 0 Y 0 0 := by
  rw [← fromBlocks_one, fromBlocks_add]
  simp

theorem forall_apply_eq_of_commute_upperUnipotentSp {g : StatedSp r K} {φ : K ≃+* K}
    {T₀ : Matrix (Fin r) (Fin r) K} (hT₀ : T₀ᵀ = T₀) (hT₀0 : T₀ ≠ 0)
    (h : ∀ c : K, g * fieldSp r K φ (upperUnipotentSp r K (transpose_smul_eq hT₀ c)) =
      upperUnipotentSp r K (transpose_smul_eq hT₀ c) * g) (a : K) : φ a = a := by
  set X : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := fromBlocks 0 T₀ 0 0 with hX
  set Xφ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := fromBlocks 0 (T₀.map φ) 0 0 with hXφ
  have key : ∀ c : K, φ c • (spMat g * Xφ) = c • (X * spMat g) := by
    intro c
    have h1 := congrArg (fun x : StatedSp r K => spMat x) (h c)
    simp only [spMat, Subgroup.coe_mul, Units.val_mul, coe_fieldSp, coe_upperUnipotentSp] at h1
    have e1 : (fromBlocks 1 (c • T₀) 0 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map φ =
        1 + φ c • Xφ := by
      ext (i | i) (j | j) <;> simp [hXφ, Matrix.one_apply]
    have e2 : (fromBlocks 1 (c • T₀) 0 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        1 + c • X := by
      ext (i | i) (j | j) <;> simp [hX, Matrix.one_apply]
    rw [e1, e2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul] at h1
    exact add_left_cancel h1
  have k1 := key 1
  rw [map_one, one_smul, one_smul] at k1
  have hXG : X * spMat g ≠ 0 := by
    intro h0
    apply hT₀0
    have hGinv : spMat g * spMat g⁻¹ = 1 := by
      show spMat (g * g⁻¹) = 1
      rw [mul_inv_cancel]
      rfl
    have hX0 : X = 0 := by
      calc X = X * spMat g * spMat g⁻¹ := by rw [Matrix.mul_assoc, hGinv, Matrix.mul_one]
        _ = 0 := by rw [h0, Matrix.zero_mul]
    have := congrArg Matrix.toBlocks₁₂ hX0
    rw [hX, toBlocks_fromBlocks₁₂] at this
    rw [this]
    ext i j
    rfl
  have k := key a
  rw [k1, ← sub_eq_zero, ← sub_smul] at k
  exact sub_eq_zero.mp ((smul_eq_zero.mp k).resolve_right hXG)

theorem exists_conj_vecMulVec_sub_ne_zero [CharP K 2] {A : GL (Fin r) K} (hA : A ≠ 1) :
    ∃ x : Fin r → K, (A : Matrix (Fin r) (Fin r) K) * vecMulVec x x *
      (A : Matrix (Fin r) (Fin r) K)ᵀ - vecMulVec x x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hA
  have hfix : ∀ x, (A : Matrix (Fin r) (Fin r) K) *ᵥ x = x := by
    intro x
    have h := hcon x
    rw [sub_eq_zero, mul_vecMulVec, vecMulVec_mul, vecMul_transpose] at h
    funext j
    have hj := congrFun (congrFun h j) j
    simp only [vecMulVec_apply] at hj
    exact CharTwo.sq_injective (by simpa [sq] using hj)
  apply Units.ext
  rw [Units.val_one]
  exact Matrix.ext_iff_mulVec.mpr fun v => by rw [hfix, one_mulVec]

theorem commute_toBlocks_of_commute_fromBlocks_diag
    {G : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (h21 : G.toBlocks₂₁ = 0)
    {P Q : Matrix (Fin r) (Fin r) K} (h : G * fromBlocks P 0 0 Q = fromBlocks P 0 0 Q * G) :
    G.toBlocks₁₁ * P = P * G.toBlocks₁₁ ∧ G.toBlocks₂₂ * Q = Q * G.toBlocks₂₂ := by
  rw [← fromBlocks_toBlocks G, h21, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at h
  exact ⟨h.1, h.2.2.2⟩

theorem toBlocks_mul_eq_of_commute_fromBlocks_one
    {G : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (h21 : G.toBlocks₂₁ = 0)
    {T : Matrix (Fin r) (Fin r) K} (h : G * fromBlocks 1 T 0 1 = fromBlocks 1 T 0 1 * G) :
    G.toBlocks₁₁ * T = T * G.toBlocks₂₂ := by
  rw [← fromBlocks_toBlocks G, h21] at h
  exact (ClassicalLagrangian.commute_fromBlocks_radical_iff _ _ _ _).mp h

theorem involutionCriterion_upperUnipotentSp [Finite K] [CharP K 2] (hr : 3 ≤ r)
    {S : Matrix (Fin r) (Fin r) K} (hS : Sᵀ = S) (hSu : IsUnit S) {A₀ : GL (Fin r) K}
    (hA₀ : (A₀ : Matrix (Fin r) (Fin r) K) * S * (A₀ : Matrix (Fin r) (Fin r) K)ᵀ = S)
    (hA₀3 : A₀ ^ 3 = 1) (hA₀1 : A₀ ≠ 1)
    (hscalar : ∀ G : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, G.toBlocks₂₁ = 0 →
      G.toBlocks₁₁ * S = S * G.toBlocks₂₂ →
      (∀ d ∈ closure {c : StatedSp r K | c ∈ centralizer {upperUnipotentSp r K hS} ∧
        Odd (orderOf c)}, G * spMat d = spMat d * G) →
      ∃ c : K, G.toBlocks₂₂ = c • 1) :
    InvolutionCriterion (spInner r K (upperUnipotentSp r K hS)) := by
  have : NeZero r := ⟨by omega⟩
  refine involutionCriterion_spInner_of_fixes hr le_rfl fun g φ hgs hgd => ?_
  obtain ⟨x, hx⟩ := exists_conj_vecMulVec_sub_ne_zero hA₀1
  have hT' : (vecMulVec x x)ᵀ = vecMulVec x x := transpose_vecMulVec x x
  have hT₀ := transpose_conj_sub_eq (A := (A₀ : Matrix (Fin r) (Fin r) K)) hT'
  have hmem : ∀ c : K, upperUnipotentSp r K (transpose_smul_eq hT₀ c) ∈
      closure {c : StatedSp r K | c ∈ centralizer {upperUnipotentSp r K hS} ∧
        Odd (orderOf c)} := by
    intro c
    have h := upperUnipotentSp_sub_mem_closure_odd hS hA₀ hA₀3 (transpose_smul_eq hT' c)
    convert h using 2
    rw [smul_sub, Matrix.mul_smul, Matrix.smul_mul]
  have hφ := forall_apply_eq_of_commute_upperUnipotentSp hT₀ hx fun c => hgd _ (hmem c)
  obtain rfl : φ = 1 := RingEquiv.ext hφ
  have hfield : ∀ d : StatedSp r K, fieldSp r K 1 d = d := fun d => by
    rw [map_one]
    rfl
  simp only [hfield] at hgs hgd
  have hGs : spMat g * fromBlocks 1 S 0 1 = fromBlocks 1 S 0 1 * spMat g := by
    have h := congrArg (fun x : StatedSp r K => spMat x) hgs
    simpa only [spMat, Subgroup.coe_mul, Units.val_mul, coe_upperUnipotentSp] using h
  have hblocks := hGs
  rw [← fromBlocks_toBlocks (spMat g)] at hblocks
  obtain ⟨h21, h11⟩ := (ClassicalLagrangian.commute_fromBlocks_one_iff hSu _ _ _ _).mp hblocks
  obtain ⟨c, hc⟩ := hscalar (spMat g) h21 h11 fun d hd => by
    have h := congrArg (fun x : StatedSp r K => spMat x) (hgd d hd)
    simpa only [spMat, Subgroup.coe_mul, Units.val_mul] using h
  have hGG := ClassicalLagrangian.mul_self_eq_smul_one_of_commute_fromBlocks hSu hGs hc
  exact ⟨by rw [hfield]; exact mul_self_eq_one_of_spMat_mul_self_eq_smul hGG, mul_one 1⟩

end SymplecticLagrangian

end CFSG.SeitzReduction
