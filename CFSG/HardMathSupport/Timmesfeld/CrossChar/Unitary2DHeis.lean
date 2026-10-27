module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DNonsplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DCube
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DSchur
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DGood

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryLines CFSG.RankThree.PartOne.KCUnitaryOne
  CFSG.RankThree.PartOne.KCUnitaryFrame CFSG.RankThree.PartOne.KCUnitaryBlock
  CFSG.RankThree.PartOne.KCUnitaryScalar CFSG.RankThree.PartOne.KCUnitaryPair
  CFSG.RankThree.PartOne.KCUnitaryGt CFSG.HardMathSupport.Timmesfeld.Balance

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

section Matrices

theorem mulVec_comm_of_mul_eq {X Y : primeFormUnitary h (idGram K n)} (hXY : X * Y = Y * X)
    (v : Fin n → K) :
    ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  have := congrArg (fun y : primeFormUnitary h (idGram K n) =>
    ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hXY
  simpa using this

theorem mulVec_cube {X : primeFormUnitary h (idGram K n)} (hX : X ^ 3 = 1) (v : Fin n → K) :
    ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)) = v := by
  have := congrArg (fun y : primeFormUnitary h (idGram K n) =>
    ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hX
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one] at this
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_three', this, Matrix.one_mulVec]

theorem mulVec_injective_of_unitary (X : primeFormUnitary h (idGram K n)) :
    Function.Injective (fun v : Fin n → K =>
      ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
  intro v w hvw
  have key : ∀ u : Fin n → K, (((X : GL (Fin n) K)⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ (((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) = u :=
    fun u => by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
  rw [← key v, ← key w]
  exact congrArg _ hvw

end Matrices

section Tau

theorem tau_eq_one_of_heis (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hq : ℓ ^ f = 2)
    {A B M : primeFormUnitary h (idGram K n)} {τ : K ≃+* K} {w : Kˣ}
    (hAB : (A : GL (Fin n) K) * (B : GL (Fin n) K) =
      (B : GL (Fin n) K) * (A : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) w)
    (hw1 : w ≠ 1)
    (hgA : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ *
        primeFormConjHom h (idGram K n) A =
      primeFormConjHom h (idGram K n) A *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩)
    (hgB : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ *
        primeFormConjHom h (idGram K n) B =
      primeFormConjHom h (idGram K n) B *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩) :
    τ = RingEquiv.refl K := by
  have : NeZero n := ⟨by omega⟩
  set α := primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ with hα
  obtain ⟨dA, hdA⟩ := exists_scalar_of_commute_conj hn hne hgA
  obtain ⟨dB, hdB⟩ := exists_scalar_of_commute_conj hn hne hgB
  set a : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with ha
  set b : Matrix (Fin n) (Fin n) K := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hb
  rw [scalar_coe_eq_smul_one] at hdA hdB
  have hABm : a * b = (w : K) • (b * a) := by
    have := congrArg Units.val hAB
    rw [Units.val_mul, Units.val_mul, Units.val_mul, scalar_coe_eq_smul_one] at this
    rw [ha, hb, this, Matrix.mul_smul, Matrix.mul_one]
  have hwτ : idAct' h n hn hne α ((w : K) • (1 : Matrix (Fin n) (Fin n) K)) =
      (τ (w : K)) • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [hα, idAct'_psi_apply]
    have hmap : ((w : K) • (1 : Matrix (Fin n) (Fin n) K)).map τ =
        (τ (w : K)) • (1 : Matrix (Fin n) (Fin n) K) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  have e1 : idAct' h n hn hne α (a * b) = ((dA : K) * dB) • (a * b) := by
    rw [map_mul, hdA, hdB]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
    congr 1
    ring
  have e2 : idAct' h n hn hne α ((w : K) • (b * a)) =
      (τ (w : K) * (dB * dA)) • (b * a) := by
    rw [show (w : K) • (b * a) = ((w : K) • (1 : Matrix (Fin n) (Fin n) K)) * (b * a) by
      rw [Matrix.smul_mul, Matrix.one_mul], map_mul, hwτ, map_mul, hdA, hdB]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul]
    congr 1
    ring
  have key := congrArg (idAct' h n hn hne α) hABm
  rw [e1, e2, hABm, smul_smul] at key
  have hBA : IsUnit (b * a) := by
    rw [hb, ha, ← Units.val_mul]
    exact Units.isUnit _
  have h3 := smul_matrix_cancel hBA key
  have hdd : ((dA : K) * dB) ≠ 0 := mul_ne_zero dA.ne_zero dB.ne_zero
  have h4 : τ (w : K) = w := by
    have : ((dA : K) * dB) * w = ((dA : K) * dB) * τ (w : K) := by
      rw [h3]
      ring
    exact (mul_left_cancel₀ hdd this).symm
  exact ringEquiv_eq_one_of_fix h hq w.ne_zero (fun h1 => hw1 (Units.ext h1)) h4

end Tau

section Main

theorem localDeltaIn_eq_bot_of_heis (hn : 4 ≤ n) (hq : ℓ ^ f = 2)
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 27) (hDl : D ≤ primeFormD h (idGram K n))
    (hcube : ∀ Y : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) Y ∈ D →
      Y ^ 3 = 1)
    {A B : primeFormUnitary h (idGram K n)} (hA : primeFormConjHom h (idGram K n) A ∈ D)
    (hB : primeFormConjHom h (idGram K n) B ∈ D) (hAB : A * B ≠ B * A)
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  classical
  have := h.finite
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  obtain ⟨w, hw⟩ := exists_scalar_of_conj_commute hn3 hne (commute_of_isElemAbelian hD _ hA _ hB)
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hAB
    apply Subtype.ext
    rw [map_one, mul_one] at hw
    exact hw
  have hw3 : w ^ 3 = 1 := unit_pow_three_eq_one h hq w
  obtain ⟨Z, hZD, hZ1, hAZ, hBZ⟩ := exists_commuting_lift_two hn3 hne hq hD hcard hDl A B hA hB
  have hZ3 : Z ^ 3 = 1 := hcube Z hZD
  have hB3 : B ^ 3 = 1 := hcube B hB
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨⟨M, τ⟩, rfl⟩ := surjective_primeFormPsi_of_ne (h := h) hn3 hne g
  have hτ : τ = RingEquiv.refl K := tau_eq_one_of_heis hn3 hne hq hw hw1
    (commute_of_mem_localDeltaIn hg hA) (commute_of_mem_localDeltaIn hg hB)
  subst hτ
  rw [psi_refl_eq] at hg ⊢
  have hcop : Nat.Coprime 3 (orderOf (primeFormConjHom h (idGram K n) M)) :=
    coprime_orderOf_of_mem_localDeltaIn hp3 hg hZD hZ1
  have hMA : M * A = A * M :=
    commute_of_commute_psi_coprime hn3 hne hq hcop (commute_of_mem_localDeltaIn hg hA)
  have hMB : M * B = B * M :=
    commute_of_commute_psi_coprime hn3 hne hq hcop (commute_of_mem_localDeltaIn hg hB)
  have hMZ : M * Z = Z * M :=
    commute_of_commute_psi_coprime hn3 hne hq hcop (commute_of_mem_localDeltaIn hg hZD)
  have hABv : ∀ v : Fin n → K, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) = (w : K) •
        (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)) := by
    intro v
    have := congrArg Units.val hw
    rw [Units.val_mul, Units.val_mul, Units.val_mul, scalar_coe_eq_smul_one] at this
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, this, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mulVec]
  have hscal : ∀ ν : K, ∃ c : K, ∀ v : Fin n → K,
      ((Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = ν • v →
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v := by
    intro ν
    by_cases hdim : 4 ≤ Module.finrank K (primaryComponent ((toLinU h n Z :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (X - C ν))
    · obtain ⟨c, hc⟩ := good_eigen_scalar hn3 hne hq hZ3 hdim hH hg hZD hZ1 hMZ
      exact ⟨c, fun v hv => hc v hv⟩
    · push Not at hdim
      set W := primaryComponent ((toLinU h n Z : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) (X - C ν) with hW
      have hmemW : ∀ v, v ∈ W ↔ ((Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = ν • v :=
        fun v => mem_primaryComponent_X_sub_C
      have hpres : ∀ Y : primeFormUnitary h (idGram K n), Y * Z = Z * Y → ∀ v ∈ W,
          ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W := by
        intro Y hYZ v hv
        rw [hmemW] at hv ⊢
        rw [← mulVec_comm_of_mul_eq hYZ, hv, Matrix.mulVec_smul]
      obtain ⟨c, hc⟩ := heis_scalar
        (A := Matrix.toLin' ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (B := Matrix.toLin' ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (M := Matrix.toLin' ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (mulVec_injective_of_unitary A) (w := (w : K)) (fun h1 => hw1 (Units.ext h1))
        (by rw [← Units.val_pow_eq_pow_val, hw3, Units.val_one])
        (fun v => hABv v) (fun v => mulVec_cube hB3 v)
        (fun v => mulVec_comm_of_mul_eq hMA v) (fun v => mulVec_comm_of_mul_eq hMB v)
        W (hpres A hAZ) (hpres B hBZ) (hpres M hMZ) (by omega)
      exact ⟨c, fun v hv => hc v ((hmemW v).2 hv)⟩
  have hM3 := pow_three_eq_one_of_eigen_scalar hq hZ3 hscal
  have h1 : orderOf (primeFormConjHom h (idGram K n) M) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hM3, map_one])
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop.symm h1)

end Main

end CFSG.HardMathSupport.Timmesfeld.CrossChar
