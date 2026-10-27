module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieCore
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonEmb
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieConj

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore Matrix Equiv Fin.NatCast
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
open CFSG.SectionRank.OddCover

section Fourier

variable {K : Type} [Field K]

@[expose] noncomputable def e5 (ζ : Kˣ) (hζ : ζ ^ 5 = 1) : C5 →* Kˣ where
  toFun c := ζ ^ (Multiplicative.toAdd c).val
  map_one' := by simp
  map_mul' a b := by
    change ζ ^ (Multiplicative.toAdd a + Multiplicative.toAdd b).val =
      ζ ^ (Multiplicative.toAdd a).val * ζ ^ (Multiplicative.toAdd b).val
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add]

theorem e5_injective (ζ : Kˣ) (hζ : orderOf ζ = 5) :
    Function.Injective (e5 ζ (by rw [← hζ]; exact pow_orderOf_eq_one ζ)) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have h1 : ζ ^ (Multiplicative.toAdd c).val = 1 := hc
  have h2 : 5 ∣ (Multiplicative.toAdd c).val := by
    have := orderOf_dvd_of_pow_eq_one h1
    rwa [hζ] at this
  have h3 : (Multiplicative.toAdd c).val < 5 := ZMod.val_lt _
  have h4 : (Multiplicative.toAdd c).val = 0 := by omega
  have h5 : Multiplicative.toAdd c = 0 := (ZMod.val_eq_zero _).mp h4
  exact h5

theorem pow_five_of_orderOf {ζ : Kˣ} (h : orderOf ζ = 5) : ζ ^ 5 = 1 := by
  rw [← h]
  exact pow_orderOf_eq_one ζ

@[expose] noncomputable def e5' (ζ : Kˣ) (h : orderOf ζ = 5) : C5 →* Kˣ :=
  e5 ζ (pow_five_of_orderOf h)

theorem e5'_injective (ζ : Kˣ) (h : orderOf ζ = 5) : Function.Injective (e5' ζ h) :=
  e5_injective ζ h

end Fourier

section Dft

variable {K : Type} [Field K] {ζ : K}

theorem sum_pow_five_eq_zero {u : K} (hu : u ^ 5 = 1) (hne : u ≠ 1) :
    ∑ k : Fin 5, u ^ (k : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => u ^ k) 5]
  have h := geom_sum_mul u 5
  rw [hu, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)

@[expose] def dftMat (ζ : K) : Matrix (Fin 5) (Fin 5) K :=
  Matrix.of fun j k => ζ ^ ((j : ℕ) * (k : ℕ))

@[expose] def dftMat' (ζ : K) : Matrix (Fin 5) (Fin 5) K :=
  Matrix.of fun k l => ζ ^ (4 * ((k : ℕ) * (l : ℕ)))

theorem dft_sum (hζ : IsPrimitiveRoot ζ 5) (j l : Fin 5) :
    ∑ k : Fin 5, ζ ^ ((j : ℕ) * (k : ℕ)) * ζ ^ (4 * ((k : ℕ) * (l : ℕ))) =
      if j = l then (5 : K) else 0 := by
  have hu : ∀ k : ℕ, ζ ^ ((j : ℕ) * k) * ζ ^ (4 * (k * (l : ℕ))) =
      (ζ ^ ((j : ℕ) + 4 * (l : ℕ))) ^ k := by
    intro k
    rw [← pow_add, ← pow_mul]
    congr 1
    ring
  simp_rw [hu]
  split_ifs with h
  · subst h
    have h1 : ζ ^ ((j : ℕ) + 4 * (j : ℕ)) = 1 := by
      rw [show (j : ℕ) + 4 * (j : ℕ) = 5 * (j : ℕ) by ring, pow_mul, hζ.pow_eq_one, one_pow]
    simp [h1]
  · have h1 : (ζ ^ ((j : ℕ) + 4 * (l : ℕ))) ^ 5 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have h2 : ζ ^ ((j : ℕ) + 4 * (l : ℕ)) ≠ 1 := by
      intro h3
      have h4 := (hζ.pow_eq_one_iff_dvd _).mp h3
      apply h
      have hdec : ∀ j l : Fin 5, 5 ∣ (j : ℕ) + 4 * (l : ℕ) → j = l := by decide
      exact hdec j l h4
    exact sum_pow_five_eq_zero h1 h2

theorem dftMat_mul (hζ : IsPrimitiveRoot ζ 5) :
    dftMat ζ * dftMat' ζ = (5 : K) • (1 : Matrix (Fin 5) (Fin 5) K) := by
  ext j l
  simp only [Matrix.mul_apply, dftMat, dftMat', Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply]
  rw [dft_sum hζ j l]
  split_ifs <;> simp

@[expose] noncomputable def dftGL (hζ : IsPrimitiveRoot ζ 5) (h5 : (5 : K) ≠ 0) (c : K)
    (hc : c ≠ 0) : GL (Fin 5) K where
  val := c • dftMat ζ
  inv := (c * 5)⁻¹ • dftMat' ζ
  val_inv := by
    rw [smul_mul_smul_comm, dftMat_mul hζ, smul_smul]
    have h3 : c * (c * 5)⁻¹ * 5 = 1 := by
      field_simp
    rw [h3, one_smul]
  inv_val := by
    have h1 : dftMat ζ * ((5 : K)⁻¹ • dftMat' ζ) = 1 := by
      rw [Matrix.mul_smul, dftMat_mul hζ, smul_smul, inv_mul_cancel₀ h5, one_smul]
    have h2 := mul_eq_one_comm.mp h1
    rw [smul_mul_smul_comm]
    have h3 : (c * 5)⁻¹ * c = (5 : K)⁻¹ := by
      field_simp
    rw [h3]
    rw [Matrix.smul_mul] at h2
    exact h2

theorem pow_eq_of_mod_eq {a b : ℕ} (hζ : ζ ^ 5 = 1) (h : a % 5 = b % 5) : ζ ^ a = ζ ^ b := by
  rw [pow_eq_pow_mod a hζ, pow_eq_pow_mod b hζ, h]

theorem perm_mul_dftMat (hζ : IsPrimitiveRoot ζ 5) :
    ((sig5⁻¹ : Perm (Fin 5)).permMatrix K) * dftMat ζ =
      dftMat ζ * Matrix.diagonal (fun k : Fin 5 => ζ ^ (4 * (k : ℕ))) := by
  have h1 : ((sig5⁻¹ : Perm (Fin 5)).permMatrix K) * dftMat ζ =
      (dftMat ζ).submatrix (sig5⁻¹ : Perm (Fin 5)) id := PEquiv.toMatrix_toPEquiv_mul _ _
  rw [h1]
  ext i k
  rw [Matrix.submatrix_apply, Matrix.mul_diagonal]
  simp only [dftMat, Matrix.of_apply, id_eq]
  rw [← pow_add]
  refine pow_eq_of_mod_eq hζ.pow_eq_one ?_
  have hdec : ∀ i k : Fin 5, (((i - 1 : Fin 5) : ℕ) * (k : ℕ)) % 5 =
      ((i : ℕ) * (k : ℕ) + 4 * (k : ℕ)) % 5 := by decide
  have : (sig5⁻¹ : Perm (Fin 5)) i = i - 1 := sig5_symm_apply i
  rw [this]
  exact hdec i k

theorem isPrimitiveRoot_coe {ζ : Kˣ} (h : orderOf ζ = 5) : IsPrimitiveRoot (ζ : K) 5 :=
  IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr h)

theorem monEmb_mT_ddv (ζ : Kˣ) (h : orderOf ζ = 5) :
    monEmb (e5' ζ h) 5 (mT ddv) = diagHom 5 (fun i : Fin 5 => ζ ^ (i : ℕ)) := by
  unfold mT
  rw [monEmb_monT]
  congr 1
  funext i
  change ζ ^ ((ddv i).val) = ζ ^ (i : ℕ)
  simp [ddv, ZMod.val_natCast, Nat.mod_eq_of_lt i.2]

theorem inv_monEmb_mT_ddv (ζ : Kˣ) (h : orderOf ζ = 5) :
    (monEmb (e5' ζ h) 5 (mT ddv))⁻¹ = diagHom 5 (fun i : Fin 5 => ζ ^ (4 * (i : ℕ))) := by
  rw [monEmb_mT_ddv]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← map_mul]
  have : (fun i : Fin 5 => ζ ^ (i : ℕ)) * (fun i : Fin 5 => ζ ^ (4 * (i : ℕ))) = 1 := by
    funext i
    simp only [Pi.mul_apply, Pi.one_apply]
    rw [← pow_add, show (i : ℕ) + 4 * (i : ℕ) = 5 * (i : ℕ) by ring, pow_mul,
      pow_five_of_orderOf h, one_pow]
  rw [this, map_one]

theorem dftGL_conj (ζ : Kˣ) (h : orderOf ζ = 5) (h5 : (5 : K) ≠ 0) (c : K) (hc : c ≠ 0) :
    (dftGL (isPrimitiveRoot_coe h) h5 c hc)⁻¹ * monEmb (e5' ζ h) 5 (monS sig5) *
        dftGL (isPrimitiveRoot_coe h) h5 c hc =
      (monEmb (e5' ζ h) 5 (mT ddv))⁻¹ := by
  set W := dftGL (isPrimitiveRoot_coe h) h5 c hc with hW
  rw [inv_monEmb_mT_ddv, monEmb_monS]
  have hPW : monPermGL 5 sig5 * W = W * diagHom 5 (fun i : Fin 5 => ζ ^ (4 * (i : ℕ))) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_monPermGL, coe_diagHom]
    have hWv : ((W : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = c • dftMat (ζ : K) := rfl
    rw [hWv, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [perm_mul_dftMat (isPrimitiveRoot_coe h)]
    congr 2
  calc W⁻¹ * monPermGL 5 sig5 * W = W⁻¹ * (monPermGL 5 sig5 * W) := mul_assoc _ _ _
    _ = W⁻¹ * (W * diagHom 5 (fun i : Fin 5 => ζ ^ (4 * (i : ℕ)))) := by rw [hPW]
    _ = diagHom 5 (fun i : Fin 5 => ζ ^ (4 * (i : ℕ))) := by group

end Dft

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M
