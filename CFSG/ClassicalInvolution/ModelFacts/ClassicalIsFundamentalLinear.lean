module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.ClassicalInvolution.Models.LinearPairs.Intrinsic
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.ClassicalInvolution

section Idempotents

variable {R : Type*} [Ring R] {e f : R}

@[expose] def partOn (e f x : R) : R := e * x * e + f

theorem idem_left (hef : e + f = 1) (hef0 : e * f = 0) : e * e = e := by
  calc e * e = e * (e + f) := by rw [mul_add, hef0, add_zero]
    _ = e := by rw [hef, mul_one]

theorem idem_right (hef : e + f = 1) (hfe : f * e = 0) : f * f = f := by
  calc f * f = f * (e + f) := by rw [mul_add, hfe, zero_add]
    _ = f := by rw [hef, mul_one]

theorem cross_left (hef0 : e * f = 0) {x : R} (hxf : x * f = f * x) : e * x * f = 0 := by
  calc e * x * f = e * (x * f) := mul_assoc _ _ _
    _ = e * (f * x) := by rw [hxf]
    _ = (e * f) * x := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hef0, zero_mul]

theorem cross_right (hfe : f * e = 0) {x : R} (hxe : x * e = e * x) : f * x * e = 0 := by
  calc f * x * e = f * (x * e) := mul_assoc _ _ _
    _ = f * (e * x) := by rw [hxe]
    _ = (f * e) * x := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hfe, zero_mul]

theorem eq_add_of_commute (hef : e + f = 1) (hef0 : e * f = 0) (hfe : f * e = 0)
    {x : R} (hxe : x * e = e * x) (hxf : x * f = f * x) : x = e * x * e + f * x * f := by
  calc x = (e + f) * x * (e + f) := by rw [hef, one_mul, mul_one]
    _ = e * x * e + e * x * f + f * x * e + f * x * f := by noncomm_ring
    _ = e * x * e + f * x * f := by
      rw [cross_left hef0 hxf, cross_right hfe hxe, add_zero, add_zero]

theorem partOn_mul_partOn (hef : e + f = 1) (hef0 : e * f = 0) (hfe : f * e = 0)
    {x : R} (hxe : x * e = e * x) (hxf : x * f = f * x) :
    partOn e f x * partOn f e x = x := by
  have he := idem_left hef hef0
  have hf' := idem_right hef hfe
  unfold partOn
  calc (e * x * e + f) * (f * x * f + e)
      = e * x * (e * f) * x * f + e * x * (e * e) + (f * f) * x * f + f * e := by noncomm_ring
    _ = e * x * e + f * x * f := by rw [hef0, he, hf', hfe]; noncomm_ring
    _ = x := (eq_add_of_commute hef hef0 hfe hxe hxf).symm

theorem partOn_eq (hef : e + f = 1) (hef0 : e * f = 0) {x : R} (hxe : x * e = e * x) :
    partOn e f x = x * e + f := by
  have he := idem_left hef hef0
  unfold partOn
  congr 1
  calc e * x * e = x * e * e := by rw [← hxe]
    _ = x * e := by rw [mul_assoc, he]

theorem partOn_mul (hef : e + f = 1) (hef0 : e * f = 0) (hfe : f * e = 0)
    {x y : R} (hxe : x * e = e * x) (hye : y * e = e * y) (hyf : y * f = f * y) :
    partOn e f (x * y) = partOn e f x * partOn e f y := by
  have he := idem_left hef hef0
  have hf' := idem_right hef hfe
  have hxye : (x * y) * e = e * (x * y) := by
    rw [mul_assoc, hye, ← mul_assoc, hxe, mul_assoc]
  rw [partOn_eq hef hef0 hxe, partOn_eq hef hef0 hye, partOn_eq hef hef0 hxye]
  calc x * y * e + f = x * (y * e) * e + f := by
        rw [mul_assoc x y e, mul_assoc x (y * e) e, mul_assoc y e e, he]
    _ = (x * e + f) * (y * e + f) := by
        calc x * (y * e) * e + f
            = x * (e * y) * e + x * (e * f) + (f * y) * e + f * f := by
              rw [hye, hef0, hf', ← hyf, mul_zero, add_zero, mul_assoc y f e, hfe, mul_zero, add_zero]
          _ = (x * e + f) * (y * e + f) := by noncomm_ring

theorem partOn_one (hef : e + f = 1) (hef0 : e * f = 0) : partOn e f (1 : R) = 1 := by
  have he := idem_left hef hef0
  unfold partOn
  rw [mul_one, he, hef]

theorem partOn_mul_sub (hef : e + f = 1) (hef0 : e * f = 0) (hfe : f * e = 0) (x : R) :
    partOn e f x * (f - e) = f - e * x * e := by
  have he := idem_left hef hef0
  have hf' := idem_right hef hfe
  unfold partOn
  calc (e * x * e + f) * (f - e)
      = e * x * (e * f) - e * x * (e * e) + f * f - f * e := by noncomm_ring
    _ = f - e * x * e := by rw [hef0, he, hf', hfe]; noncomm_ring

theorem sub_mul_partOn (hef : e + f = 1) (hef0 : e * f = 0) (hfe : f * e = 0) (x : R) :
    (f - e) * partOn e f x = f - e * x * e := by
  have he := idem_left hef hef0
  have hf' := idem_right hef hfe
  unfold partOn
  calc (f - e) * (e * x * e + f)
      = (f * e) * x * e - (e * e) * x * e + f * f - e * f := by noncomm_ring
    _ = f - e * x * e := by rw [hef0, he, hf', hfe]; noncomm_ring

theorem partOn_mul_right (hef0 : e * f = 0) (hfe : f * e = 0) (hef : e + f = 1) (x : R) :
    partOn e f x * f = f := by
  have hf' := idem_right hef hfe
  unfold partOn
  calc (e * x * e + f) * f = e * x * (e * f) + f * f := by noncomm_ring
    _ = f := by rw [hef0, hf']; noncomm_ring

theorem commute_of_fix (hef : e + f = 1) (hef0 : e * f = 0) (hfe : f * e = 0) {x y : R}
    (hx : x = e * x * e + f) (hy : y = e + f * y * f) : x * y = y * x := by
  have he := idem_left hef hef0
  have hf' := idem_right hef hfe
  calc x * y = (e * x * e + f) * (e + f * y * f) := by rw [← hx, ← hy]
    _ = e * x * (e * e) + e * x * (e * f) * y * f + f * e + (f * f) * y * f := by noncomm_ring
    _ = e * x * e + f * y * f := by rw [he, hef0, hfe, hf']; noncomm_ring
    _ = (e + f * y * f) * (e * x * e + f) := by
        calc e * x * e + f * y * f
            = (e * e) * x * e + e * f + f * y * (f * e) * x * e + f * y * (f * f) := by
              rw [he, hef0, hfe, hf']; noncomm_ring
          _ = (e + f * y * f) * (e * x * e + f) := by noncomm_ring
    _ = y * x := by rw [← hx, ← hy]

end Idempotents

section Involution

open Matrix CFSG.ClassicalInvolution.Models
open scoped MatrixGroups

variable {F : Type} [Field F] {n : ℕ}

@[expose] noncomputable def minusProj (D : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  (2 : F)⁻¹ • (1 - D)

@[expose] noncomputable def plusProj (D : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  (2 : F)⁻¹ • (1 + D)

variable {D : Matrix (Fin n) (Fin n) F}

theorem minusProj_add_plusProj (h2 : (2 : F) ≠ 0) :
    minusProj D + plusProj D = 1 := by
  unfold minusProj plusProj
  rw [← smul_add]
  have : (1 - D) + (1 + D) = (2 : F) • (1 : Matrix (Fin n) (Fin n) F) := by
    rw [two_smul]; abel
  rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem minusProj_mul_plusProj (hD : D * D = 1) :
    minusProj D * plusProj D = 0 := by
  unfold minusProj plusProj
  rw [smul_mul_smul_comm]
  have : (1 - D) * (1 + D) = 0 := by
    have h : (1 - D) * (1 + D) = 1 - D * D := by noncomm_ring
    rw [h, hD, sub_self]
  rw [this, smul_zero]

theorem plusProj_mul_minusProj (hD : D * D = 1) :
    plusProj D * minusProj D = 0 := by
  unfold minusProj plusProj
  rw [smul_mul_smul_comm]
  have : (1 + D) * (1 - D) = 0 := by
    have h : (1 + D) * (1 - D) = 1 - D * D := by noncomm_ring
    rw [h, hD, sub_self]
  rw [this, smul_zero]

theorem eq_plusProj_sub_minusProj (h2 : (2 : F) ≠ 0) : D = plusProj D - minusProj D := by
  unfold minusProj plusProj
  rw [← smul_sub]
  have : (1 + D) - (1 - D) = (2 : F) • D := by rw [two_smul]; abel
  rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem commute_minusProj {x : Matrix (Fin n) (Fin n) F} (hx : x * D = D * x) :
    x * minusProj D = minusProj D * x := by
  unfold minusProj
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, hx]

theorem commute_plusProj {x : Matrix (Fin n) (Fin n) F} (hx : x * D = D * x) :
    x * plusProj D = plusProj D * x := by
  unfold plusProj
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, hx]

theorem eq_mul_partOn_of_commute (h2 : (2 : F) ≠ 0) (hD : D * D = 1)
    {x : Matrix (Fin n) (Fin n) F} (hx : x * D = D * x) :
    partOn (minusProj D) (plusProj D) x * partOn (plusProj D) (minusProj D) x = x :=
  partOn_mul_partOn (minusProj_add_plusProj h2) (minusProj_mul_plusProj hD)
    (plusProj_mul_minusProj hD) (commute_minusProj hx) (commute_plusProj hx)

theorem le_sup_longRootGroup_of_perfect (h2 : (2 : F) ≠ 0) (hD : D * D = 1)
    {L : Subgroup SL(n, F)} (hL : Group.IsPerfect ↥L)
    (hLD : ∀ x ∈ L, (x : Matrix (Fin n) (Fin n) F) * D = D * x) :
    L ≤ longRootGroup D ⊔ longRootGroup (-D) := by
  have hsum := minusProj_add_plusProj (D := D) h2
  have hef := minusProj_mul_plusProj hD
  have hfe := plusProj_mul_minusProj hD
  let δ₀ : ↥L →* F :=
    { toFun := fun x => (partOn (minusProj D) (plusProj D)
        ((x : SL(n, F)) : Matrix (Fin n) (Fin n) F)).det
      map_one' := by
        show (partOn (minusProj D) (plusProj D) (1 : Matrix (Fin n) (Fin n) F)).det = 1
        rw [partOn_one hsum hef, det_one]
      map_mul' := by
        intro x y
        have hx := hLD x x.2
        have hy := hLD y y.2
        show (partOn (minusProj D) (plusProj D)
          ((x : SL(n, F)) * (y : SL(n, F)) : SL(n, F)).1).det = _ * _
        rw [Matrix.SpecialLinearGroup.coe_mul,
          partOn_mul hsum hef hfe (commute_minusProj hx) (commute_minusProj hy)
            (commute_plusProj hy), det_mul] }
  have hδ : ∀ x : ↥L, δ₀ x = 1 := by
    intro x
    have hker : commutator ↥L ≤ (δ₀.toHomUnits).ker := Abelianization.commutator_subset_ker _
    rw [hL.commutator_eq_top] at hker
    have h1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top x))
    have h2' : ((δ₀.toHomUnits x : Fˣ) : F) = 1 := by rw [h1]; rfl
    simpa using h2'
  intro x hx
  have hxD := hLD x hx
  have hprod := eq_mul_partOn_of_commute h2 hD hxD
  have hdet : (partOn (minusProj D) (plusProj D) (x : Matrix (Fin n) (Fin n) F)).det = 1 :=
    hδ ⟨x, hx⟩
  have hdetp : (partOn (plusProj D) (minusProj D) (x : Matrix (Fin n) (Fin n) F)).det = 1 := by
    have := congrArg Matrix.det hprod
    rw [det_mul, hdet, one_mul] at this
    rw [this]
    exact x.2
  let xmS : SL(n, F) := ⟨partOn (minusProj D) (plusProj D) (x : Matrix (Fin n) (Fin n) F), hdet⟩
  let xpS : SL(n, F) := ⟨partOn (plusProj D) (minusProj D) (x : Matrix (Fin n) (Fin n) F), hdetp⟩
  have hDe : D = plusProj D - minusProj D := eq_plusProj_sub_minusProj h2
  have h1D : (1 : Matrix (Fin n) (Fin n) F) + D = (2 : F) • plusProj D := by
    unfold plusProj; rw [smul_smul, mul_inv_cancel₀ h2, one_smul]
  have h1D' : (1 : Matrix (Fin n) (Fin n) F) + -D = (2 : F) • minusProj D := by
    unfold minusProj; rw [smul_smul, mul_inv_cancel₀ h2, one_smul, sub_eq_add_neg]
  have hxm : xmS ∈ longRootGroup D := by
    refine ⟨?_, ?_⟩
    · show partOn (minusProj D) (plusProj D) (x : Matrix (Fin n) (Fin n) F) * D = D *
        partOn (minusProj D) (plusProj D) (x : Matrix (Fin n) (Fin n) F)
      have e1 := partOn_mul_sub hsum hef hfe (x : Matrix (Fin n) (Fin n) F)
      have e2 := sub_mul_partOn hsum hef hfe (x : Matrix (Fin n) (Fin n) F)
      rw [← hDe] at e1 e2
      rw [e1, e2]
    · show partOn (minusProj D) (plusProj D) (x : Matrix (Fin n) (Fin n) F) * (1 + D) = 1 + D
      rw [h1D, Matrix.mul_smul, partOn_mul_right hef hfe hsum]
  have hxp : xpS ∈ longRootGroup (-D) := by
    refine ⟨?_, ?_⟩
    · show partOn (plusProj D) (minusProj D) (x : Matrix (Fin n) (Fin n) F) * (-D) = (-D) *
        partOn (plusProj D) (minusProj D) (x : Matrix (Fin n) (Fin n) F)
      have hsum' : plusProj D + minusProj D = 1 := (add_comm _ _).trans hsum
      have e1 := partOn_mul_sub hsum' hfe hef (x : Matrix (Fin n) (Fin n) F)
      have e2 := sub_mul_partOn hsum' hfe hef (x : Matrix (Fin n) (Fin n) F)
      have hDe' : -D = minusProj D - plusProj D := by
        calc -D = -(plusProj D - minusProj D) := by rw [← hDe]
          _ = minusProj D - plusProj D := neg_sub _ _
      rw [← hDe'] at e1 e2
      rw [e1, e2]
    · show partOn (plusProj D) (minusProj D) (x : Matrix (Fin n) (Fin n) F) * (1 + -D) = 1 + -D
      rw [h1D', Matrix.mul_smul, partOn_mul_right hfe hef ((add_comm _ _).trans hsum)]
  have hx' : x = xmS * xpS := Subtype.ext hprod.symm
  rw [hx']
  exact Subgroup.mul_mem_sup hxm hxp

theorem eq_of_mem_longRootGroup (h2 : (2 : F) ≠ 0) (hD : D * D = 1) {x : SL(n, F)}
    (hx : x ∈ longRootGroup D) :
    (x : Matrix (Fin n) (Fin n) F) =
      minusProj D * x * minusProj D + plusProj D := by
  obtain ⟨h1, h3⟩ := hx
  have hxf : (x : Matrix (Fin n) (Fin n) F) * plusProj D = plusProj D := by
    have h1D : (1 : Matrix (Fin n) (Fin n) F) + D = (2 : F) • plusProj D := by
      unfold plusProj; rw [smul_smul, mul_inv_cancel₀ h2, one_smul]
    rw [h1D, Matrix.mul_smul] at h3
    exact smul_right_injective _ h2 h3
  have hfx : plusProj D * (x : Matrix (Fin n) (Fin n) F) = plusProj D := by
    rw [← commute_plusProj h1, hxf]
  have key := eq_add_of_commute (minusProj_add_plusProj h2) (minusProj_mul_plusProj hD)
    (plusProj_mul_minusProj hD) (commute_minusProj h1) (commute_plusProj h1)
  have hff := idem_right (minusProj_add_plusProj h2) (plusProj_mul_minusProj hD)
  conv_lhs => rw [key]
  rw [mul_assoc (plusProj D), hxf, hff]

theorem eq_of_mem_longRootGroup_neg (h2 : (2 : F) ≠ 0) (hD : D * D = 1) {y : SL(n, F)}
    (hy : y ∈ longRootGroup (-D)) :
    (y : Matrix (Fin n) (Fin n) F) =
      minusProj D + plusProj D * y * plusProj D := by
  obtain ⟨h1, h3⟩ := hy
  have h1' : (y : Matrix (Fin n) (Fin n) F) * D = D * y := by
    rw [Matrix.mul_neg, Matrix.neg_mul] at h1
    exact neg_injective h1
  have hye : (y : Matrix (Fin n) (Fin n) F) * minusProj D = minusProj D := by
    have h1D' : (1 : Matrix (Fin n) (Fin n) F) + -D = (2 : F) • minusProj D := by
      unfold minusProj; rw [smul_smul, mul_inv_cancel₀ h2, one_smul, sub_eq_add_neg]
    rw [h1D', Matrix.mul_smul] at h3
    exact smul_right_injective _ h2 h3
  have hey : minusProj D * (y : Matrix (Fin n) (Fin n) F) = minusProj D := by
    rw [← commute_minusProj h1', hye]
  have key := eq_add_of_commute (minusProj_add_plusProj h2) (minusProj_mul_plusProj hD)
    (plusProj_mul_minusProj hD) (commute_minusProj h1') (commute_plusProj h1')
  have he := idem_left (minusProj_add_plusProj h2) (minusProj_mul_plusProj hD)
  conv_lhs => rw [key]
  rw [mul_assoc (minusProj D), hye, he]

theorem commute_longRootGroup_neg (h2 : (2 : F) ≠ 0) (hD : D * D = 1) {x y : SL(n, F)}
    (hx : x ∈ longRootGroup D) (hy : y ∈ longRootGroup (-D)) : x * y = y * x := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact commute_of_fix (minusProj_add_plusProj h2) (minusProj_mul_plusProj hD)
    (plusProj_mul_minusProj hD) (eq_of_mem_longRootGroup h2 hD hx)
    (eq_of_mem_longRootGroup_neg h2 hD hy)

theorem exists_sl_conj_diagonal (h2 : (2 : F) ≠ 0) (hn : 0 < n)
    {D : Matrix (Fin n) (Fin n) F} (hD : D * D = 1) :
    ∃ (a : ℕ) (_ : a ≤ n) (P : SL(n, F)),
      D * (P : Matrix (Fin n) (Fin n) F) = (P : Matrix (Fin n) (Fin n) F) *
        Matrix.diagonal (fun j : Fin n => if j.val < a then (-1 : F) else 1) := by
  have hcompl := isCompl_eigSpace h2 hD
  set V := eigSpace D (-1) with hV
  set W := eigSpace D 1 with hW'
  set a := Module.finrank F V with ha'
  have ha : a ≤ n := by
    have := Submodule.finrank_le V
    rw [Module.finrank_fin_fun] at this
    exact this
  have hW : Module.finrank F W = n - a := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [Module.finrank_fin_fun] at this
    omega
  let E : Bool → Submodule F (Fin n → F) := fun b => cond b W V
  have hint : DirectSum.IsInternal E := by
    rw [DirectSum.isInternal_submodule_iff_isCompl E (i := false) (j := true) (by simp)
      (by ext b; cases b <;> simp)]
    exact hcompl
  let ε : Fin n → Bool := fun j => decide (a ≤ j.val)
  have hε : ∀ b, Nat.card {j // ε j = b} = Module.finrank F (E b) := by
    intro b
    cases b
    · change _ = Module.finrank F V
      rw [Nat.card_congr (Equiv.subtypeEquivRight (q := fun j : Fin n => j.val < a)
        (fun j => by simp only [ε, decide_eq_false_iff_not, not_le]))]
      exact card_fin_val_lt ha
    · change _ = Module.finrank F W
      rw [hW, Nat.card_congr (Equiv.subtypeEquivRight (q := fun j : Fin n => a ≤ j.val)
        (fun j => by simp only [ε, decide_eq_true_eq]))]
      exact card_fin_val_ge ha
  obtain ⟨P, hP⟩ := exists_sl_adapted hn E hint ε hε
  refine ⟨a, ha, P, ?_⟩
  ext i j
  rw [Matrix.mul_diagonal]
  have hcol := hP j
  by_cases hj : j.val < a
  · have hmem : (fun k => (P : Matrix (Fin n) (Fin n) F) k j) ∈ V := by
      simpa [E, ε, not_le.mpr hj] using hcol
    have := congr_fun (mem_eigSpace_neg_one.mp hmem) i
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply] at this
    simp only [Matrix.mul_apply, hj, ite_true]
    rw [this]
    ring
  · have hmem : (fun k => (P : Matrix (Fin n) (Fin n) F) k j) ∈ W := by
      simpa [E, ε, not_lt.mp hj] using hcol
    have := congr_fun (mem_eigSpace_one.mp hmem) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, hj, ite_false]
    rw [this]
    ring

end Involution
section GeneralBlock

open CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.Phan (blockMat blockIdx blockMat_apply blockMat_mul det_blockMat)
open CFSG.ClassicalInvolution.WeakCT (blockSL coe_blockSL)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def negBlockK (K : Type) [Field K] (n j k : ℕ) : Matrix (Fin n) (Fin n) K :=
  blockMat n j (-1 : Matrix (Fin k) (Fin k) K)

theorem negBlockK_eq_diagonal (n j k : ℕ) :
    negBlockK K n j k = Matrix.diagonal (fun a : Fin n =>
      if j ≤ a.val ∧ a.val < j + k then (-1 : K) else 1) := by
  ext a b
  rw [negBlockK, blockMat_apply, Matrix.diagonal_apply]
  by_cases hb : (j ≤ a.val ∧ a.val < j + k) ∧ (j ≤ b.val ∧ b.val < j + k)
  · rw [dite_eq_left hb]
    by_cases hab : a = b
    · subst hab
      simp [hb.1]
    · have : (⟨a.val - j, by omega⟩ : Fin k) ≠ ⟨b.val - j, by omega⟩ := by
        intro h
        apply hab
        apply Fin.ext
        have := congrArg Fin.val h
        simp only at this
        omega
      simp [hab, this]
  · rw [dite_eq_right hb]
    by_cases hab : a = b
    · subst hab
      have : ¬ (j ≤ a.val ∧ a.val < j + k) := fun h => hb ⟨h, h⟩
      simp [this]
    · simp [hab]

theorem blockSL_mem_longRootGroupK {j k : ℕ} (hj : j + k ≤ n) (A : SL(k, K)) :
    blockSL K n k j hj A ∈ longRootGroup (negBlockK K n j k) := by
  have hA : (-1 : Matrix (Fin k) (Fin k) K) * (A : Matrix (Fin k) (Fin k) K) =
      (A : Matrix (Fin k) (Fin k) K) * (-1) := by simp
  refine ⟨?_, ?_⟩
  · rw [coe_blockSL, negBlockK, ← blockMat_mul hj, ← blockMat_mul hj, hA]
  · rw [coe_blockSL, negBlockK, Matrix.mul_add, Matrix.mul_one, ← blockMat_mul hj]
    have : ((A : Matrix (Fin k) (Fin k) K) * (-1)) = -(A : Matrix (Fin k) (Fin k) K) := by simp
    rw [this]
    unfold blockMat
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul]
    abel

theorem exists_blockSL_of_mem_longRootGroupK (h2 : (2 : K) ≠ 0) {j k : ℕ} (hj : j + k ≤ n)
    {x : SL(n, K)} (hx : x ∈ longRootGroup (negBlockK K n j k)) :
    ∃ A : SL(k, K), blockSL K n k j hj A = x := by
  obtain ⟨h1, h3⟩ := hx
  rw [negBlockK_eq_diagonal] at h1 h3
  set X : Matrix (Fin n) (Fin n) K := (x : Matrix (Fin n) (Fin n) K) with hX
  set d : Fin n → K := fun a => if j ≤ a.val ∧ a.val < j + k then (-1 : K) else 1 with hd
  have e1 : ∀ a b, X a b * d b = d a * X a b := fun a b => by
    have := congr_fun (congr_fun h1 a) b
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have h3' : X * Matrix.diagonal (fun a => 1 + d a) = Matrix.diagonal (fun a => 1 + d a) := by
    have : (1 : Matrix (Fin n) (Fin n) K) + Matrix.diagonal d =
        Matrix.diagonal (fun a => 1 + d a) := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_add]
    rwa [this] at h3
  have e3 : ∀ a b, X a b * (1 + d b) = if a = b then 1 + d a else 0 := fun a b => by
    have := congr_fun (congr_fun h3' a) b
    simpa [Matrix.mul_diagonal, Matrix.diagonal_apply] using this
  let A : Matrix (Fin k) (Fin k) K := Matrix.of fun p q => X (blockIdx j hj p) (blockIdx j hj q)
  have hXA : X = blockMat n j A := by
    ext a b
    rw [blockMat_apply]
    by_cases hab : (j ≤ a.val ∧ a.val < j + k) ∧ (j ≤ b.val ∧ b.val < j + k)
    · rw [dite_eq_left hab]
      have ha : blockIdx j hj (⟨a.val - j, by omega⟩ : Fin k) = a :=
        Fin.ext (by simp only [blockIdx]; omega)
      have hb : blockIdx j hj (⟨b.val - j, by omega⟩ : Fin k) = b :=
        Fin.ext (by simp only [blockIdx]; omega)
      simp only [A, Matrix.of_apply, ha, hb]
    · rw [dite_eq_right hab]
      by_cases hb : j ≤ b.val ∧ b.val < j + k
      · have ha : ¬ (j ≤ a.val ∧ a.val < j + k) := fun h => hab ⟨h, hb⟩
        have hne : a ≠ b := fun h => ha (h ▸ hb)
        have := e1 a b
        simp only [hd, ite_eq_left hb, ite_eq_right ha] at this
        rw [Matrix.one_apply_ne hne]
        have h' : (2 : K) * X a b = 0 := by linear_combination -this
        exact (mul_eq_zero.mp h').resolve_left h2
      · have := e3 a b
        by_cases hab' : a = b
        · subst hab'
          rw [Matrix.one_apply_eq]
          simp only [hd, ite_eq_right hb, ite_true] at this
          have h' : (2 : K) * (X a a - 1) = 0 := by linear_combination this
          have := (mul_eq_zero.mp h').resolve_left h2
          linear_combination this
        · rw [Matrix.one_apply_ne hab']
          simp only [hd, ite_eq_right hb, hab', ite_false] at this
          have h' : (2 : K) * X a b = 0 := by linear_combination this
          exact (mul_eq_zero.mp h').resolve_left h2
  have hdet : A.det = 1 := by
    rw [← det_blockMat hj A, ← hXA]
    exact x.2
  exact ⟨⟨A, hdet⟩, Subtype.ext hXA.symm⟩

theorem range_blockSL_eq_longRootGroupK (h2 : (2 : K) ≠ 0) {j k : ℕ} (hj : j + k ≤ n) :
    (blockSL K n k j hj).range = longRootGroup (negBlockK K n j k) := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    exact blockSL_mem_longRootGroupK hj A
  · intro hx
    obtain ⟨A, hA⟩ := exists_blockSL_of_mem_longRootGroupK h2 hj hx
    exact ⟨A, hA⟩


end GeneralBlock


section LongRootData

open CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.WeakCT (blockSL blockSL_injective)
open scoped MatrixGroups

variable {F : Type} [Field F] {n : ℕ}

theorem exists_longRootGroup_data (h2 : (2 : F) ≠ 0) (hn : 0 < n)
    {D : Matrix (Fin n) (Fin n) F} (hD : D * D = 1) :
    ∃ (a : ℕ) (ha : a ≤ n) (P : SL(n, F)),
      D * (P : Matrix (Fin n) (Fin n) F) = (P : Matrix (Fin n) (Fin n) F) *
        Matrix.diagonal (fun j : Fin n => if j.val < a then (-1 : F) else 1) ∧
      longRootGroup D =
        ((blockSL F n a 0 (by omega)).range).map (MulAut.conj P).toMonoidHom := by
  obtain ⟨a, ha, P, hP⟩ := exists_sl_conj_diagonal h2 hn hD
  refine ⟨a, ha, P, hP, ?_⟩
  have hrange := range_blockSL_eq_longRootGroupK (K := F) (n := n) h2 (j := 0) (k := a)
    (by omega)
  have hdiag : negBlockK F n 0 a = Matrix.diagonal
      (fun j : Fin n => if j.val < a then (-1 : F) else 1) := by
    rw [negBlockK_eq_diagonal]
    congr 1
    funext j
    simp
  rw [hrange, ← longRootGroup_eq_map_conj_of_mul_eq P (hP.trans (by rw [← hdiag]))]

theorem subsingleton_sl_of_le_one {a : ℕ} (ha : a ≤ 1) : Subsingleton SL(a, F) := by
  interval_cases a
  · infer_instance
  · refine ⟨fun A B => Subtype.ext ?_⟩
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    have h1 := A.2
    have h2 := B.2
    rw [Matrix.det_unique] at h1 h2
    simp only [Fin.default_eq_zero] at h1 h2
    rw [h1, h2]

end LongRootData

open scoped MatrixGroups in
theorem false_of_sl_equiv_quotient_sl2 {F : Type} [Field F] [Finite F] (hF : 5 ≤ Nat.card F)
    {a : ℕ} (ha : 3 ≤ a) {G : Type} [Group G] (e1 : SL(a, F) ≃* G)
    (e2 : G ⧸ classicalInvolutionOddCore G ≃* SL(2, F)) : False := by
  have : Finite G := Finite.of_equiv _ e1.toEquiv
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  have hqF : CFSG.IsQuasisimple SL(m + 1, F) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple m F (by omega)
  have hq : CFSG.IsQuasisimple G := CFSG.LocalCores.isQuasisimple_of_mulEquiv e1 hqF
  have hq' : Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
  set N := Nat.card F with hNdef
  have hcenter : Nat.card (Subgroup.center (SL(m + 1, F))) ≤ N - 1 := by
    have hmax : max (Fintype.card (Fin (m + 1))) 1 = m + 1 := by
      rw [Fintype.card_fin]; omega
    have : NeZero (m + 1) := ⟨by omega⟩
    rw [Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin (m + 1)) (R := F)).toEquiv, hmax]
    rw [← Nat.card_units F]
    exact Nat.card_le_card_of_injective (fun x => (x : Fˣ)) Subtype.val_injective
  have hsl2 : Nat.card SL(2, F) = N * (N ^ 2 - 1) :=
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F
  set O := classicalInvolutionOddCore G with hO
  have hGO : Nat.card O * Nat.card (G ⧸ O) = Nat.card G := Subgroup.card_mul_index O
  have hquot : Nat.card (G ⧸ O) = N * (N ^ 2 - 1) := by
    rw [Nat.card_congr e2.toEquiv, hsl2]
  have hOle : Nat.card O ≤ N - 1 := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq O with h | h
    · calc Nat.card O ≤ Nat.card (Subgroup.center G) := Subgroup.card_le_of_le h
        _ = Nat.card (Subgroup.center (SL(m + 1, F))) :=
            (Nat.card_congr (Subgroup.centerCongr e1).toEquiv).symm
        _ ≤ N - 1 := hcenter
    · exfalso
      have hOtop : O = ⊤ := h
      have h1 : Nat.card (G ⧸ O) = 1 := by
        have : O.index = 1 := by rw [hOtop, Subgroup.index_top]
        exact this
      rw [hquot] at h1
      have h5 : 5 ≤ N := hF
      have h6 : 5 ≤ N ^ 2 - 1 := by
        have : 25 ≤ N ^ 2 := by nlinarith
        omega
      nlinarith
  have hs : Nat.card G ≤ (N - 1) * (N * (N ^ 2 - 1)) := by
    rw [← hGO, hquot]
    exact Nat.mul_le_mul_right _ hOle
  have hGL : Nat.card SL(m + 1, F) * Nat.card Fˣ = Nat.card (GL (Fin (m + 1)) F) :=
    Matrix.card_SL_mul_card_units
  have hunits : Nat.card Fˣ = N - 1 := Nat.card_units F
  have hSLG : Nat.card SL(m + 1, F) = Nat.card G := Nat.card_congr e1.toEquiv
  have hGLbound : N ^ ((m + 1) * m) ≤ Nat.card (GL (Fin (m + 1)) F) := by
    rw [Matrix.card_GL_field, hq']
    have hfac : ∀ i : Fin (m + 1), N ^ m ≤ N ^ (m + 1) - N ^ (i : ℕ) := by
      intro i
      have h1 : N ^ (i : ℕ) ≤ N ^ m := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : N ^ (m + 1) = N * N ^ m := by rw [pow_succ']
      have h3 : 2 * N ^ m ≤ N * N ^ m := Nat.mul_le_mul_right _ (by omega)
      omega
    calc N ^ ((m + 1) * m) = (N ^ m) ^ (m + 1) := by rw [← pow_mul, mul_comm]
      _ = (N ^ m) ^ (Finset.univ : Finset (Fin (m + 1))).card := by rw [Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ i : Fin (m + 1), (N ^ (m + 1) - N ^ (i : ℕ)) :=
          Finset.pow_card_le_prod _ _ _ fun i _ => hfac i
  have h6 : N ^ 6 ≤ N ^ ((m + 1) * m) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hup : (N - 1) * (N * (N ^ 2 - 1)) * (N - 1) ≤ N ^ 5 := by
    calc (N - 1) * (N * (N ^ 2 - 1)) * (N - 1) ≤ N * (N * N ^ 2) * N := by
          apply Nat.mul_le_mul
          · apply Nat.mul_le_mul (Nat.sub_le _ _)
            exact Nat.mul_le_mul le_rfl (Nat.sub_le _ _)
          · exact Nat.sub_le _ _
      _ = N ^ 5 := by ring
  have hlt : N ^ 5 < N ^ 6 := Nat.pow_lt_pow_right (by omega) (by omega)
  have := hGLbound
  rw [← hGL, hunits, hSLG] at this
  have h7 : Nat.card G * (N - 1) ≤ (N - 1) * (N * (N ^ 2 - 1)) * (N - 1) :=
    Nat.mul_le_mul_right _ hs
  omega


end CFSG.ClassicalInvolution.ModelFacts
