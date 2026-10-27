module

public import CFSG.Open.StatedAPI
public import CFSG.Open.StatedDefs
public import CFSG.GF2Type.ModelPSU
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

open Matrix CFSG.Open

abbrev F4 : Type := GaloisField 2 2

noncomputable abbrev fr : F4 →+* F4 := frobenius F4 2

theorem fr_apply (x : F4) : fr x = x ^ 2 := frobenius_def 2 x

theorem card_F4 : Nat.card F4 = 4 := GaloisField.card 2 2 (by norm_num)

theorem pow_four (x : F4) : x ^ 4 = x := by
  letI : Fintype F4 := Fintype.ofFinite F4
  have h := FiniteField.pow_card x
  rw [Fintype.card_eq_nat_card, card_F4] at h
  exact h

theorem fr_fr (x : F4) : fr (fr x) = x := by
  rw [fr_apply, fr_apply, ← pow_mul]
  exact pow_four x

theorem fr_fix01 {x : F4} (hx : x = 0 ∨ x = 1) : fr x = x := by
  rcases hx with rfl | rfl <;> simp

theorem two_eq_zero_F4 : (1 : F4) + 1 = 0 := CharTwo.add_self_eq_zero (1 : F4)

theorem pow_three_of_ne_zero {x : F4} (hx : x ≠ 0) : x ^ 3 = 1 := by
  have h := pow_four x
  have : x ^ 4 = x ^ 3 * x := by ring
  rw [this] at h
  have hx' : x * (x ^ 3 - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 hx' with h1 | h1
  · exact absurd h1 hx
  · linear_combination h1

@[expose] def IsUnitaryMat {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F4) : Prop :=
  (A.map fr)ᵀ * A = 1

theorem fr_eq_sq_fun : (fun x : F4 => x ^ 2) = fr := funext fun x => (fr_apply x).symm

@[expose] def suSub (n : ℕ) : Subgroup (GL (Fin n) F4) where
  carrier := {A | (A : Matrix (Fin n) (Fin n) F4).det = 1 ∧
    IsUnitaryMat (A : Matrix (Fin n) (Fin n) F4)}
  mul_mem' := by
    rintro A B ⟨hA, hUA⟩ ⟨hB, hUB⟩
    refine ⟨?_, ?_⟩
    · simp only [Units.val_mul, Matrix.det_mul, hA, hB, one_mul]
    · unfold IsUnitaryMat at *
      simp only [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
      have key : ((B : Matrix (Fin n) (Fin n) F4).map fr)ᵀ * ((A : Matrix (Fin n) (Fin n) F4).map fr)ᵀ *
          ((A : Matrix (Fin n) (Fin n) F4) * (B : Matrix (Fin n) (Fin n) F4)) =
          ((B : Matrix (Fin n) (Fin n) F4).map fr)ᵀ *
            ((((A : Matrix (Fin n) (Fin n) F4).map fr)ᵀ * (A : Matrix (Fin n) (Fin n) F4)) *
              (B : Matrix (Fin n) (Fin n) F4)) := by
        simp only [Matrix.mul_assoc]
      rw [key, hUA, Matrix.one_mul, hUB]
  one_mem' := by
    refine ⟨?_, ?_⟩
    · simp
    · unfold IsUnitaryMat
      simp
  inv_mem' := by
    rintro A ⟨hA, hUA⟩
    unfold IsUnitaryMat at *
    set a : Matrix (Fin n) (Fin n) F4 := (A : Matrix (Fin n) (Fin n) F4) with ha
    set B : Matrix (Fin n) (Fin n) F4 := ((A⁻¹ : GL (Fin n) F4) : Matrix (Fin n) (Fin n) F4)
      with hB
    have hAB : a * B = 1 := by
      rw [ha, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hBA : B * a = 1 := by
      rw [ha, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hBeq : B = (a.map fr)ᵀ := by
      calc B = ((a.map fr)ᵀ * a) * B := by rw [hUA, Matrix.one_mul]
        _ = (a.map fr)ᵀ * (a * B) := by rw [Matrix.mul_assoc]
        _ = (a.map fr)ᵀ := by rw [hAB, Matrix.mul_one]
    refine ⟨?_, ?_⟩
    · have h1 : B.det * a.det = 1 := by rw [← Matrix.det_mul, hBA, Matrix.det_one]
      rw [hA, mul_one] at h1
      exact h1
    · have hTB : (B.map fr)ᵀ = a := by
        ext i j
        simp [hBeq, fr_fr]
      rw [hTB]
      exact hAB

theorem statedSU_two_eq (n : ℕ) : StatedSU n 2 F4 = suSub n := by
  apply le_antisymm
  · unfold StatedSU
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro A ⟨hA, hUA⟩
    refine ⟨hA, ?_⟩
    unfold IsUnitaryMat
    rw [← fr_eq_sq_fun]
    exact hUA
  · intro A hA
    unfold StatedSU
    apply Subgroup.subset_closure
    obtain ⟨hA1, hA2⟩ := hA
    unfold IsUnitaryMat at hA2
    rw [← fr_eq_sq_fun] at hA2
    exact ⟨hA1, hA2⟩

theorem mem_statedSU_iff {n : ℕ} (A : GL (Fin n) F4) :
    A ∈ StatedSU n 2 F4 ↔ (A : Matrix (Fin n) (Fin n) F4).det = 1 ∧
      IsUnitaryMat (A : Matrix (Fin n) (Fin n) F4) := by
  rw [statedSU_two_eq]
  rfl

variable {w : ℕ}

@[expose] noncomputable def e0 (w : ℕ) : Fin (w + 2) → F4 := fun i => if w ≤ i.val then 1 else 0

theorem e0_val_zero_of_castAdd (i : Fin w) : e0 w (Fin.castAdd 2 i) = 0 := by
  unfold e0
  simp only [Fin.coe_castAdd]
  rw [if_neg]
  omega

theorem e0_natAdd_zero : e0 w (Fin.natAdd w 0) = 1 := by
  unfold e0
  simp

theorem e0_natAdd_one : e0 w (Fin.natAdd w 1) = 1 := by
  unfold e0
  simp

theorem e0_cases (i : Fin (w + 2)) : e0 w i = 0 ∨ e0 w i = 1 := by
  unfold e0
  split_ifs <;> simp

theorem e0_dot : e0 w ⬝ᵥ e0 w = 0 := by
  unfold dotProduct
  rw [Fin.sum_univ_add]
  simp only [e0_val_zero_of_castAdd, mul_zero, Finset.sum_const_zero, zero_add]
  rw [Fin.sum_univ_two]
  simp only [e0_natAdd_zero, e0_natAdd_one]
  exact two_eq_zero_F4 ▸ (by norm_num)

@[expose] noncomputable def tau0 (w : ℕ) : Matrix (Fin (w + 2)) (Fin (w + 2)) F4 :=
  1 + vecMulVec (e0 w) (e0 w)

theorem vecMulVec_e0_mul_self :
    vecMulVec (e0 w) (e0 w) * vecMulVec (e0 w) (e0 w) = 0 := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.zero_apply]
  have h : ∀ k, e0 w i * e0 w k * (e0 w k * e0 w j) = (e0 w i * e0 w j) * (e0 w k * e0 w k) :=
    fun k => by ring
  simp only [h]
  rw [← Finset.mul_sum]
  have := e0_dot (w := w)
  unfold dotProduct at this
  rw [this, mul_zero]

theorem tau0_mul_self : tau0 w * tau0 w = 1 := by
  have h2 : vecMulVec (e0 w) (e0 w) + vecMulVec (e0 w) (e0 w) = 0 := by
    ext i j
    simp only [Matrix.add_apply, vecMulVec_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hexp : tau0 w * tau0 w = 1 + (vecMulVec (e0 w) (e0 w) + vecMulVec (e0 w) (e0 w)) +
      vecMulVec (e0 w) (e0 w) * vecMulVec (e0 w) (e0 w) := by
    unfold tau0
    noncomm_ring
  rw [hexp, h2, vecMulVec_e0_mul_self, add_zero, add_zero]

theorem tau0_symm : (tau0 w)ᵀ = tau0 w := by
  unfold tau0
  rw [transpose_add, transpose_one, transpose_vecMulVec]

theorem tau0_entry01 (i j : Fin (w + 2)) : tau0 w i j = 0 ∨ tau0 w i j = 1 := by
  unfold tau0
  rw [Matrix.add_apply, Matrix.one_apply, vecMulVec_apply]
  rcases e0_cases i with hi | hi <;> rcases e0_cases j with hj | hj <;>
    by_cases hij : i = j <;> simp [hi, hj, hij, two_eq_zero_F4]

theorem tau0_map_fr : (tau0 w).map fr = tau0 w := by
  ext i j
  rw [Matrix.map_apply]
  exact fr_fix01 (tau0_entry01 i j)

theorem tau0_unitary : IsUnitaryMat (tau0 w) := by
  unfold IsUnitaryMat
  rw [tau0_map_fr, tau0_symm, tau0_mul_self]

theorem tau0_det : (tau0 w).det = 1 := by
  have h := congrArg Matrix.det (tau0_mul_self (w := w))
  rw [Matrix.det_mul, Matrix.det_one] at h
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact h1
  · rw [h1]
    exact CharTwo.neg_eq (1 : F4)

@[expose] noncomputable def tau0GL (w : ℕ) : GL (Fin (w + 2)) F4 :=
  Units.mk (tau0 w) (tau0 w) tau0_mul_self tau0_mul_self

theorem tau0GL_val : ((tau0GL w : GL (Fin (w + 2)) F4) : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) =
    tau0 w := rfl

theorem tau0GL_mem : tau0GL w ∈ suSub (w + 2) :=
  ⟨tau0_det, tau0_unitary⟩

theorem mul_vecMulVec_e (A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) :
    A * vecMulVec (e0 w) (e0 w) = vecMulVec (A *ᵥ e0 w) (e0 w) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul,
    mul_assoc]

theorem vecMulVec_e_mul (A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) :
    vecMulVec (e0 w) (e0 w) * A = vecMulVec (e0 w) (e0 w ᵥ* A) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum,
    mul_assoc]

theorem row_act {A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4} (hU : IsUnitaryMat A) {μ : F4}
    (hμ : A *ᵥ e0 w = μ • e0 w) : e0 w ᵥ* A = μ • e0 w := by
  have hfix : ∀ j, fr (e0 w j) = e0 w j := fun j => fr_fix01 (e0_cases j)
  have hA2 : A.map fr *ᵥ e0 w = (μ ^ 2) • e0 w := by
    funext i
    have hi := congrFun hμ i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    have hk : (A.map fr *ᵥ e0 w) i = fr ((A *ᵥ e0 w) i) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, hfix]
    rw [hk, hi, map_mul, hfix, fr_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hid : e0 w ᵥ* ((A.map fr)ᵀ * A) = e0 w := by
    rw [hU, Matrix.vecMul_one]
  rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hA2, Matrix.smul_vecMul] at hid
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have h0 : e0 w (Fin.natAdd w 0) = 0 := by
      have := congrFun hid (Fin.natAdd w 0)
      simp at this
      exact this.symm
    rw [e0_natAdd_zero] at h0
    exact one_ne_zero h0
  have h3 : μ ^ 3 = 1 := pow_three_of_ne_zero hμ0
  calc e0 w ᵥ* A = (μ ^ 3) • (e0 w ᵥ* A) := by rw [h3, one_smul]
    _ = μ • (μ ^ 2 • (e0 w ᵥ* A)) := by rw [smul_smul]; ring_nf
    _ = μ • e0 w := by rw [hid]

theorem comm_tau0_iff {A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4} (hU : IsUnitaryMat A) :
    A * tau0 w = tau0 w * A ↔ ∃ μ : F4, A *ᵥ e0 w = μ • e0 w := by
  constructor
  · intro h
    have hEA : A * vecMulVec (e0 w) (e0 w) = vecMulVec (e0 w) (e0 w) * A := by
      unfold tau0 at h
      rw [mul_add, add_mul, mul_one, one_mul] at h
      exact add_left_cancel h
    rw [mul_vecMulVec_e, vecMulVec_e_mul] at hEA
    refine ⟨(e0 w ᵥ* A) (Fin.natAdd w 0), ?_⟩
    funext i
    have hi := congrFun (congrFun hEA i) (Fin.natAdd w 0)
    simp only [vecMulVec_apply, e0_natAdd_zero, mul_one, Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [hi, mul_comm]
  · rintro ⟨μ, hμ⟩
    have hrow := row_act hU hμ
    unfold tau0
    rw [mul_add, add_mul, mul_one, one_mul, mul_vecMulVec_e, vecMulVec_e_mul, hμ, hrow]
    ext i j
    simp [vecMulVec_apply, mul_comm, mul_left_comm]

@[expose] noncomputable def stabSet (w : ℕ) : Subgroup (GL (Fin (w + 2)) F4) where
  carrier := {A | ∃ μ : F4, (A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ e0 w = μ • e0 w}
  mul_mem' := by
    rintro A B ⟨μ, hμ⟩ ⟨ν, hν⟩
    refine ⟨μ * ν, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hν, Matrix.mulVec_smul, hμ, smul_smul,
      mul_comm ν μ]
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro A ⟨μ, hμ⟩
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      have h0 : (A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ e0 w = 0 := by
        rw [hμ, zero_smul]
      have h1 : (↑A⁻¹ : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ
          ((A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ e0 w) = e0 w := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [h0, Matrix.mulVec_zero] at h1
      have h2 := congrFun h1 (Fin.natAdd w 0)
      rw [e0_natAdd_zero] at h2
      simp at h2
    refine ⟨μ⁻¹, ?_⟩
    have h1 : (↑A⁻¹ : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ
        ((A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ e0 w) = e0 w := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hμ, Matrix.mulVec_smul] at h1
    funext i
    have hi := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [← hi]
    field_simp

@[expose] noncomputable def stabSU (w : ℕ) : Subgroup (GL (Fin (w + 2)) F4) := suSub (w + 2) ⊓ stabSet w

theorem mem_stabSU_iff (A : GL (Fin (w + 2)) F4) :
    A ∈ stabSU w ↔ (A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4).det = 1 ∧
      IsUnitaryMat (A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) ∧
      ∃ μ : F4, (A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ e0 w = μ • e0 w := by
  unfold stabSU
  rw [Subgroup.mem_inf]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

theorem mem_centralizer_tau0_iff (A : GL (Fin (w + 2)) F4) (hA : A ∈ suSub (w + 2)) :
    A * tau0GL w = tau0GL w * A ↔ ∃ μ : F4, (A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ
      e0 w = μ • e0 w := by
  rw [Units.ext_iff, Units.val_mul, Units.val_mul, tau0GL_val]
  exact comm_tau0_iff hA.2

end CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

end
