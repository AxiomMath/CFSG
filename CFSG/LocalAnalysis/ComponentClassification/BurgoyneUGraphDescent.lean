module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescent
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFourGroupTransport
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUNormal

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open LinearMap (BilinForm)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem stdHermForm_semilinearMatrixMap {A : Matrix (Fin n) (Fin n) K}
    (hA : (A.map h.bar)ᵀ * A = 1) (v w : Fin n → K) :
    stdHermForm h n (semilinearMatrixMap h A v) (semilinearMatrixMap h A w) =
      h.bar (stdHermForm h n v w) := by
  rw [semilinearMatrixMap_apply, semilinearMatrixMap_apply, stdHermForm_mulVec h hA,
    stdHermForm_apply, stdHermForm_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, h.bar_bar, mul_comm]

theorem exists_graph_frame (hp2 : p ≠ 2) (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) K}
    (hA : (A.map h.bar)ᵀ * A = 1) {c : K} (hc0 : c ≠ 0) (hAc : A * A.map h.bar = c • 1) :
    (c = 1 ∨ c = -1) ∧ ∃ (P Pi : Matrix (Fin n) (Fin n) K) (b s : K)
      (R : Matrix (Fin n) (Fin n) h.fixedField),
      P * Pi = 1 ∧ Pi * P = 1 ∧ b ≠ 0 ∧ s ≠ 0 ∧ b • (A * P.map h.bar) = P ∧
      R.map h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P) ∧
      (c = 1 → Rᵀ = R) ∧ (c = -1 → Rᵀ = -R) := by
  have : CharP K p := h.charP
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h3 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    have h4 := Nat.le_of_dvd two_pos ((CharP.cast_eq_zero_iff K p 2).mp h3)
    have := h.prime.two_le
    exact hp2 (by omega)
  set τ₀ := semilinearMatrixMap h A with hτ₀def
  have hμ : ∀ v, τ₀ (τ₀ v) = ((Units.mk0 c hc0 : Kˣ) : K) • v := by
    intro v
    rw [hτ₀def, semilinearMatrixMap_apply, semilinearMatrixMap_apply, Units.val_mk0]
    have hbar : (fun i => h.bar ((A *ᵥ fun j => h.bar (v j)) i)) = A.map h.bar *ᵥ v := by
      funext i
      rw [RingHom.map_mulVec]
      congr 1
      funext j
      exact h.bar_bar (v j)
    rw [hbar, mulVec_mulVec, hAc, smul_mulVec, one_mulVec]
  have hτ₀ : Function.Bijective τ₀ := by
    refine ⟨fun v w hvw => ?_, fun w => ⟨τ₀ ((c⁻¹ : K) • w), ?_⟩⟩
    · have h1 := congrArg τ₀ hvw
      rw [hμ, hμ, Units.val_mk0] at h1
      exact smul_right_injective _ hc0 h1
    · rw [hμ, Units.val_mk0, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hfinV : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hpodd (by omega) (stdHermForm_isSymm h n) (stdHermForm_separatingLeft h n) τ₀ hτ₀
    (stdHermForm_semilinearMatrixMap h hA) (Units.mk0 c hc0) hμ
  obtain ⟨hττ, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have hc1 : c = 1 ∨ c = -1 := by
    rcases hμ1 with e | e
    · left
      have := congrArg Units.val e
      rwa [Units.val_mk0, Units.val_one] at this
    · right
      have := congrArg Units.val e
      rwa [Units.val_mk0, Units.val_neg, Units.val_one] at this
  refine ⟨hc1, ?_⟩
  obtain ⟨s, B, hs0, hBs, hsym⟩ : ∃ (s : K) (B : BilinForm h.fixedField
      (conjFixed h ((b : K) • τ₀))), s ≠ 0 ∧
      (∀ v w, (B v w : K) = s * stdHermForm h n v w) ∧
      (c = 1 → B.IsSymm) ∧ (c = -1 → B.IsAlt) := by
    rcases hc1 with e | e
    · obtain ⟨B, hB, hsymm, -, -⟩ := hB1 (Units.ext (by rw [Units.val_mk0, e, Units.val_one]))
      refine ⟨1, B, one_ne_zero, fun v w => by rw [hB, one_mul], fun _ => hsymm, fun e' => ?_⟩
      rw [e] at e'
      exact absurd (by linear_combination e' : (2 : K) = 0) h2
    · obtain ⟨B, hB, halt, -, -, -⟩ := hB2 (Units.ext (by
        rw [Units.val_mk0, e, Units.val_neg, Units.val_one]))
      refine ⟨(t : K)⁻¹, B, inv_ne_zero t.ne_zero, hB, fun e' => ?_, fun _ => halt⟩
      rw [e] at e'
      exact absurd (by linear_combination -e' : (2 : K) = 0) h2
  have : FiniteDimensional h.fixedField (conjFixed h ((b : K) • τ₀)) := finite_conjFixed
  set bW := Module.finBasisOfFinrankEq h.fixedField (conjFixed h ((b : K) • τ₀))
    (hfinW.trans hfinV) with hbWdef
  set bV := conjFixedBasis hττ ht t.ne_zero h2 bW with hbVdef
  have hHij : ∀ a j, (Pi.basisFun K (Fin n)).toMatrix bV a j =
      (bW j : Fin n → K) a := by
    intro a j
    rw [Basis.toMatrix_apply, Pi.basisFun_repr, hbVdef, conjFixedBasis_apply]
  set P := (Pi.basisFun K (Fin n)).toMatrix bV with hP
  have hcol : ∀ j, (fun a => P a j) = (bW j : Fin n → K) := fun j => funext fun a => hHij a j
  refine ⟨P, bV.toMatrix (Pi.basisFun K (Fin n)), b, s, BilinForm.toMatrix bW B,
    (Pi.basisFun K (Fin n)).toMatrix_mul_toMatrix_flip bV,
    bV.toMatrix_mul_toMatrix_flip (Pi.basisFun K (Fin n)), b.ne_zero, hs0, ?_, ?_, ?_, ?_⟩
  ·
    ext a j
    have hfix := mem_conjFixed.mp (bW j).2
    have e := congrFun hfix a
    change ((b : K) • (A *ᵥ fun i => h.bar ((bW j : Fin n → K) i))) a =
      (bW j : Fin n → K) a at e
    rw [← hcol j] at e
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct] at e
    rw [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
    simp only [map_apply]
    exact e
  ·
    ext i j
    rw [map_apply, BilinForm.toMatrix_apply]
    change ((B (bW i) (bW j) : h.fixedField) : K) = _
    rw [hBs, Matrix.smul_apply, smul_eq_mul, stdHermForm_apply, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [transpose_apply, map_apply, hHij, hHij]
  · intro e
    refine Matrix.ext fun i j => ?_
    rw [transpose_apply, BilinForm.toMatrix_apply, BilinForm.toMatrix_apply]
    exact (hsym.1 e).eq (bW j) (bW i)
  · intro e
    refine Matrix.ext fun i j => ?_
    rw [transpose_apply, Matrix.neg_apply, BilinForm.toMatrix_apply, BilinForm.toMatrix_apply]
    exact ((hsym.2 e).neg_eq (bW i) (bW j)).symm

end CFSG.ComponentClassification.Burgoyne.U
