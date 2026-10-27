module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalShearHerm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical

public section

namespace CFSG.SeitzReduction

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace SesqShear

section Abstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K}
  {B : V →ₛₗ[σ] V →ₗ[K] K}

theorem orthogonalBilin_orthogonalBilin_eq [FiniteDimensional K V] (hσ : Function.Involutive σ)
    (hB : B.IsSymm) (hBs : B.SeparatingLeft) (W : Submodule K V) :
    (W.orthogonalBilin B).orthogonalBilin B = W := by
  let F : CFSG.LieType.BorelTits.ReflForm K V :=
    { σ := RingEquiv.ofBijective σ hσ.bijective
      β := fun x y => B x y
      add_left := fun u u' v => by simp
      smul_left := fun c u v => by simp
      add_right := fun u v v' => by simp
      smul_right := fun c u v => by simp
      refl := fun u v huv => by rw [← hB.eq u v, huv, map_zero]
      nondeg := hBs }
  have hperp : ∀ U : Submodule K V, F.perp U = U.orthogonalBilin B := fun U =>
    Submodule.ext fun v => F.mem_perp.trans Submodule.mem_orthogonalBilin.symm
  rw [← hperp, ← hperp]
  exact F.perp_perp W

end Abstract

variable {p f : ℕ} {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ker_sub_one_eq_orthogonalBilin_range (h : UnitaryFieldData p f K) {G : Matrix ι ι K}
    (hG : (G.map h.bar)ᵀ = G) (hdet : G.det ≠ 0) {s : GL ι K}
    (hs : ∀ x y, gramForm h G ((s : Matrix ι ι K) *ᵥ x) ((s : Matrix ι ι K) *ᵥ y) =
      gramForm h G x y) :
    LinearMap.ker ((s : Matrix ι ι K) - 1).mulVecLin =
      (LinearMap.range ((s : Matrix ι ι K) - 1).mulVecLin).orthogonalBilin (gramForm h G) := by
  have hH := gramForm_isSymm h hG
  have hsub : ∀ v, ((s : Matrix ι ι K) - 1) *ᵥ v = (s : Matrix ι ι K) *ᵥ v - v := fun v => by
    rw [sub_mulVec, one_mulVec]
  ext v
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hsub, sub_eq_zero, Submodule.mem_orthogonalBilin]
  constructor
  · rintro hv _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply, hsub, map_sub, LinearMap.sub_apply, ← hs x v, hv, sub_self]
  · intro hv
    have h1 : ∀ x, gramForm h G ((s : Matrix ι ι K) *ᵥ x) ((s : Matrix ι ι K) *ᵥ v - v) = 0 := by
      intro x
      have h2 := hv _ ⟨x, rfl⟩
      rw [Matrix.mulVecLin_apply, hsub, map_sub, LinearMap.sub_apply, sub_eq_zero] at h2
      rw [map_sub, hs, h2, sub_self]
    have h3 : ∀ y, gramForm h G ((s : Matrix ι ι K) *ᵥ v - v) y = 0 := by
      intro y
      have h4 := h1 (((s⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y)
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h4
      rw [← hH.eq, h4, map_zero]
    exact sub_eq_zero.mp (gramForm_separatingLeft h hdet _ h3)

theorem gramForm_orthogonalBilin_orthogonalBilin (h : UnitaryFieldData p f K) {G : Matrix ι ι K}
    (hG : (G.map h.bar)ᵀ = G) (hdet : G.det ≠ 0) (W : Submodule K (ι → K)) :
    (W.orthogonalBilin (gramForm h G)).orthogonalBilin (gramForm h G) = W :=
  orthogonalBilin_orthogonalBilin_eq h.bar_bar (gramForm_isSymm h hG)
    (gramForm_separatingLeft h hdet) W

variable {n : ℕ}

theorem ringEquiv_gramForm (h : UnitaryFieldData p f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (φ : K ≃+* K) (x y : Fin n → K) :
    φ (gramForm h (C : Matrix (Fin n) (Fin n) K) x y) =
      gramForm h (C : Matrix (Fin n) (Fin n) K) (fun i => φ (x i)) (fun i => φ (y i)) := by
  rw [gramForm_apply, gramForm_apply]
  simp only [dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_bar_comm, show φ (((C : Matrix (Fin n) (Fin n) K) *ᵥ y) a) =
    (φ : K →+* K) (((C : Matrix (Fin n) (Fin n) K) *ᵥ y) a) from rfl, RingHom.map_mulVec,
    hC.map_eq (φ : K →+* K)]
  rfl

@[expose] def semilinearCoord (A : Matrix (Fin n) (Fin n) K) (φ : K ≃+* K) :
    (Fin n → K) →+ (Fin n → K) where
  toFun v := A *ᵥ fun i => φ (v i)
  map_zero' := by
    change (A *ᵥ fun i => φ ((0 : Fin n → K) i)) = 0
    rw [show (fun i => φ ((0 : Fin n → K) i)) = 0 from funext fun i => map_zero φ, mulVec_zero]
  map_add' x y := by
    change (A *ᵥ fun i => φ ((x + y) i)) = (A *ᵥ fun i => φ (x i)) + A *ᵥ fun i => φ (y i)
    rw [show (fun i => φ ((x + y) i)) = (fun i => φ (x i)) + fun i => φ (y i) from
      funext fun i => map_add φ _ _, mulVec_add]

theorem semilinearCoord_apply (A : Matrix (Fin n) (Fin n) K) (φ : K ≃+* K) (v : Fin n → K) :
    semilinearCoord A φ v = A *ᵥ fun i => φ (v i) :=
  rfl

theorem eichlerMatrix_shear (h : UnitaryFieldData p f K) {G : Matrix (Fin n) (Fin n) K}
    {W L : Submodule K (Fin n → K)} (hL : L = W.orthogonalBilin (gramForm h G))
    {w : Fin n → K} (hw : w ∈ W) (u : Fin n → K) (c : K) :
    (∀ v ∈ L, eichlerMatrix h G w u c *ᵥ v = v - gramForm h G u v • w) ∧
      ∀ v, eichlerMatrix h G w u c *ᵥ v - v - gramForm h G w v • u ∈ W := by
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have hwv : gramForm h G w v = 0 := by
      rw [hL] at hv
      exact hv w hw
    rw [eichlerMatrix_mulVec, hwv, zero_smul, add_zero, mul_zero, zero_smul, add_zero]
  · rw [eichlerMatrix_mulVec,
      show v + gramForm h G w v • u - gramForm h G u v • w + (c * gramForm h G w v) • w - v -
        gramForm h G w v • u = (c * gramForm h G w v - gramForm h G u v) • w by module]
    exact W.smul_mem _ hw

theorem primeFormConjHom_sq_eq_one_of_mul_self (h : UnitaryFieldData p f K)
    {C : Matrix (Fin n) (Fin n) K} (A : primeFormUnitary h C) {d : K}
    (hA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = d • (1 : Matrix (Fin n) (Fin n) K)) :
    primeFormConjHom h C (A ^ 2) = 1 := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, MulAut.one_apply]
  have hcomm : ((A ^ 2 : primeFormUnitary h C) : GL (Fin n) K) * (g : GL (Fin n) K) =
      g * ((A ^ 2 : primeFormUnitary h C) : GL (Fin n) K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, sq, hA,
      smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one]
  have hg : (⟨((A ^ 2 : primeFormUnitary h C) : GL (Fin n) K) * g *
      ((A ^ 2 : primeFormUnitary h C) : GL (Fin n) K)⁻¹,
      conj_mem_gramSU h C (A ^ 2).2 g.2⟩ : gramSU h C) = g :=
    Subtype.ext (by
      change ((A ^ 2 : primeFormUnitary h C) : GL (Fin n) K) * (g : GL (Fin n) K) *
        ((A ^ 2 : primeFormUnitary h C) : GL (Fin n) K)⁻¹ = g
      rw [hcomm, mul_inv_cancel_right])
  rw [hg]

end SesqShear

open SesqShear

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem gramForm_shear_rigidity (h : UnitaryFieldData p f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) {W L : Submodule K (Fin n → K)}
    (hL : L = W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K))) (hW0 : W ≠ ⊥)
    (hLW : ¬L ≤ W) {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K)
    (hAL : ∀ v ∈ L, (A : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (v i)) ∈ L)
    (hsh : ∀ w ∈ W, ∀ u ∈ L, ∃ M : Matrix (Fin n) (Fin n) K,
      (A : Matrix (Fin n) (Fin n) K) * M.map φ = M * A ∧
      (∀ v ∈ L, M *ᵥ v = v - gramForm h (C : Matrix (Fin n) (Fin n) K) u v • w) ∧
      ∀ v, M *ᵥ v - v - gramForm h (C : Matrix (Fin n) (Fin n) K) w v • u ∈ W) :
    φ = RingEquiv.refl K ∧ ∃ c : K, c ≠ 0 ∧ h.bar c * c = 1 ∧
      (∀ v ∈ L, (A : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v) ∧
      ∀ v, (A : Matrix (Fin n) (Fin n) K) *ᵥ v - c • v ∈ W := by
  set Am := (A : Matrix (Fin n) (Fin n) K) with hAm
  set Hf := gramForm h (C : Matrix (Fin n) (Fin n) K) with hHf
  have hW : W = L.orthogonalBilin Hf := by
    rw [hL, hHf, gramForm_orthogonalBilin_orthogonalBilin h (hC.barTranspose h)
      (primeFormGram_det_ne_zero C)]
  have hT : ∀ (a : K) (v : Fin n → K),
      semilinearCoord Am φ (a • v) = (φ : K →+* K) a • semilinearCoord Am φ v := by
    intro a v
    rw [semilinearCoord_apply, semilinearCoord_apply,
      show (fun i => φ ((a • v) i)) = φ a • fun i => φ (v i) from
        funext fun i => by simp only [Pi.smul_apply, smul_eq_mul, map_mul],
      mulVec_smul]
    rfl
  have hTB : ∀ x y, Hf (semilinearCoord Am φ x) (semilinearCoord Am φ y) =
      1 * (φ : K →+* K) (Hf x y) := by
    intro x y
    rw [semilinearCoord_apply, semilinearCoord_apply, hHf, gramForm_mulVec,
      mem_primeFormUnitary.mp hA, one_mul]
    exact (ringEquiv_gramForm h hC φ x y).symm
  have hsh' : ∀ w ∈ W, ∀ u ∈ L, ∃ g : (Fin n → K) →ₗ[K] (Fin n → K),
      (∀ v, semilinearCoord Am φ (g v) = g (semilinearCoord Am φ v)) ∧
      (∀ v ∈ L, g v = v - Hf u v • w) ∧ ∀ v, g v - v - Hf w v • u ∈ W := by
    intro w hw u hu
    obtain ⟨M, hAM, hM1, hM2⟩ := hsh w hw u hu
    refine ⟨M.mulVecLin, fun v => ?_, fun v hv => hM1 v hv, fun v => hM2 v⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, semilinearCoord_apply,
      semilinearCoord_apply,
      show (fun i => φ ((M *ᵥ v) i)) = M.map φ *ᵥ fun i => φ (v i) from
        funext fun i => RingHom.map_mulVec (φ : K →+* K) M v i,
      mulVec_mulVec, hAM, ← mulVec_mulVec]
  obtain ⟨hφ, c, hc0, hμc, hTLc, hTWc⟩ :=
    sesq_shear_rigidity (B := Hf) (gramForm_separatingLeft h (primeFormGram_det_ne_zero C))
      (Or.inl h.exists_bar_ne) hL hW hW0 hLW one_ne_zero (semilinearCoord Am φ) hT hTB hAL hsh'
  have hφv : ∀ v : Fin n → K, (fun i => φ (v i)) = v := fun v => funext fun i => hφ (v i)
  have hTv : ∀ v, semilinearCoord Am φ v = Am *ᵥ v := fun v => by
    rw [semilinearCoord_apply, hφv]
  refine ⟨RingEquiv.ext hφ, c, hc0, hμc, fun v hv => ?_, fun v => ?_⟩
  · rw [← hTv]
    exact hTLc v hv
  · rw [← hTv]
    exact hTWc v

theorem gramForm_shear_rigidity_sq (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) {W L : Submodule K (Fin n → K)}
    (hL : L = W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K))) (hW0 : W ≠ ⊥)
    (hLW : ¬L ≤ W) (hWL : W ≤ L) {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K)
    (hAL : ∀ v ∈ L, (A : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (v i)) ∈ L)
    (hsh : ∀ w ∈ W, ∀ u ∈ L, ∃ M : Matrix (Fin n) (Fin n) K,
      (A : Matrix (Fin n) (Fin n) K) * M.map φ = M * A ∧
      (∀ v ∈ L, M *ᵥ v = v - gramForm h (C : Matrix (Fin n) (Fin n) K) u v • w) ∧
      ∀ v, M *ᵥ v - v - gramForm h (C : Matrix (Fin n) (Fin n) K) w v • u ∈ W) :
    φ = RingEquiv.refl K ∧ ∃ c : K, c ≠ 0 ∧ h.bar c * c = 1 ∧
      (∀ v ∈ L, (A : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v) ∧
      (∀ v, (A : Matrix (Fin n) (Fin n) K) *ᵥ v - c • v ∈ W) ∧
      (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
        (c * c) • (1 : Matrix (Fin n) (Fin n) K) := by
  have : CharP K 2 := h.charP
  obtain ⟨hφ, c, hc0, hμc, hAL', hAW⟩ := gramForm_shear_rigidity h hC hL hW0 hLW hA φ hAL hsh
  refine ⟨hφ, c, hc0, hμc, hAL', hAW, ?_⟩
  have key : ∀ v, (A : Matrix (Fin n) (Fin n) K) *ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (c * c) • v :=
    SesqShear.apply_apply_eq_mul_self_smul
      (T := (A : Matrix (Fin n) (Fin n) K).mulVecLin.toAddMonoidHom) hWL
      (fun v => mulVec_smul _ c v) hAL' hAW
  refine Matrix.ext fun i j => ?_
  have h1 := congrFun (key (Pi.single j 1)) i
  rw [mulVec_mulVec, mulVec_single_one, col_apply, Pi.smul_apply, Pi.single_apply] at h1
  rw [h1, Matrix.smul_apply, Matrix.one_apply]

theorem primeFormPsi_sq_eq_one_of_shear (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) {W L : Submodule K (Fin n → K)}
    (hL : L = W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K))) (hW0 : W ≠ ⊥)
    (hLW : ¬L ≤ W) (hWL : W ≤ L) (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))
    (φ : K ≃+* K)
    (hAL : ∀ v ∈ L, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (v i)) ∈ L)
    (hsh : ∀ w ∈ W, ∀ u ∈ L, ∃ M : Matrix (Fin n) (Fin n) K,
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M.map φ =
        M * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      (∀ v ∈ L, M *ᵥ v = v - gramForm h (C : Matrix (Fin n) (Fin n) K) u v • w) ∧
      ∀ v, M *ᵥ v - v - gramForm h (C : Matrix (Fin n) (Fin n) K) w v • u ∈ W) :
    φ = RingEquiv.refl K ∧ primeFormPsi h hC ⟨A, φ⟩ ^ 2 = 1 := by
  obtain ⟨hφ, c, -, -, -, -, hAA⟩ :=
    gramForm_shear_rigidity_sq h hC hL hW0 hLW hWL A.2 φ hAL hsh
  subst hφ
  refine ⟨rfl, ?_⟩
  rw [primeFormPsi_apply, show RingEquiv.refl K = 1 from rfl, map_one, mul_one, ← map_pow]
  exact primeFormConjHom_sq_eq_one_of_mul_self h A hAA

theorem primeFormPsi_sq_eq_one_of_involution_shear (h : UnitaryFieldData 2 f K)
    {C : GL (Fin n) K} (hC : IsPrimeFormGram C) {s : GL (Fin n) K}
    (hs : s ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hsWL : LinearMap.range ((s : Matrix (Fin n) (Fin n) K) - 1).mulVecLin ≠
      LinearMap.ker ((s : Matrix (Fin n) (Fin n) K) - 1).mulVecLin)
    (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K)
    (hAs : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K).map φ =
      (s : Matrix (Fin n) (Fin n) K) * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hsh : ∀ w ∈ LinearMap.range ((s : Matrix (Fin n) (Fin n) K) - 1).mulVecLin,
      ∀ u ∈ LinearMap.ker ((s : Matrix (Fin n) (Fin n) K) - 1).mulVecLin,
      ∃ M : Matrix (Fin n) (Fin n) K,
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M.map φ =
          M * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
        (∀ v ∈ LinearMap.ker ((s : Matrix (Fin n) (Fin n) K) - 1).mulVecLin,
          M *ᵥ v = v - gramForm h (C : Matrix (Fin n) (Fin n) K) u v • w) ∧
        ∀ v, M *ᵥ v - v - gramForm h (C : Matrix (Fin n) (Fin n) K) w v • u ∈
          LinearMap.range ((s : Matrix (Fin n) (Fin n) K) - 1).mulVecLin) :
    φ = RingEquiv.refl K ∧ primeFormPsi h hC ⟨A, φ⟩ ^ 2 = 1 := by
  have : CharP K 2 := h.charP
  set sm := (s : Matrix (Fin n) (Fin n) K) with hsm
  set W := LinearMap.range (sm - 1).mulVecLin with hWdef
  set L := LinearMap.ker (sm - 1).mulVecLin with hLdef
  have hsub : ∀ v, (sm - 1) *ᵥ v = sm *ᵥ v - v := fun v => by rw [sub_mulVec, one_mulVec]
  have hss : ∀ v, sm *ᵥ (sm *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, hsm, ← Units.val_mul, hs2, Units.val_one, one_mulVec]
  have hLm : ∀ v, v ∈ L ↔ sm *ᵥ v = v := fun v => by
    rw [hLdef, LinearMap.mem_ker, Matrix.mulVecLin_apply, hsub, sub_eq_zero]
  have hL : L = W.orthogonalBilin (gramForm h (C : Matrix (Fin n) (Fin n) K)) :=
    ker_sub_one_eq_orthogonalBilin_range h (hC.barTranspose h) (primeFormGram_det_ne_zero C)
      ((gramForm_isometry_iff h _ _).mpr (mem_primeFormUnitary.mp hs))
  have hW0 : W ≠ ⊥ := by
    intro hW0
    apply hs1
    have h0 : sm - 1 = 0 := eq_zero_of_forall_mulVec_eq_zero fun v => by
      have h1 : (sm - 1).mulVecLin v ∈ W := LinearMap.mem_range_self _ v
      rw [hW0, Submodule.mem_bot, Matrix.mulVecLin_apply] at h1
      exact h1
    exact Units.ext (sub_eq_zero.mp h0)
  have hWL : W ≤ L := by
    rintro _ ⟨x, rfl⟩
    rw [hLm, Matrix.mulVecLin_apply, hsub, mulVec_sub, hss]
    have h2 : (2 : K) • x = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
    have h3 : (2 : K) • (sm *ᵥ x) = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
    linear_combination (norm := module) h2 - h3
  have hLW : ¬L ≤ W := fun hLW => hsWL (le_antisymm hWL hLW)
  have hAL : ∀ v ∈ L,
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (v i)) ∈ L := by
    intro v hv
    rw [hLm] at hv ⊢
    rw [mulVec_mulVec, ← hAs, ← mulVec_mulVec,
      show sm.map φ *ᵥ (fun i => φ (v i)) = fun i => φ ((sm *ᵥ v) i) from
        funext fun i => (RingHom.map_mulVec (φ : K →+* K) sm v i).symm, hv]
  exact primeFormPsi_sq_eq_one_of_shear h hC hL hW0 hLW hWL A φ hAL hsh

end CFSG.SeitzReduction
