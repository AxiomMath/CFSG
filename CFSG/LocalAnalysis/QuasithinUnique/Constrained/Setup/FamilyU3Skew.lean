module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Hilbert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Sym

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix

section Skew

variable {p : ℕ} [Fact p.Prime] {K F : Type} [Field K] [Field F] [Fintype F] [DecidableEq F]
  [CharP F p] (ι : F →+* K) (σ : K ≃+* K)

theorem exists_skew_nilpotent (hFcard : Fintype.card F = p) (hp5 : 5 ≤ p) (hσ : ∀ x, σ (σ x) = x)
    (hι : ∀ x, σ (ι x) = ι x) (hfix : ∀ m : K, σ m = m → ∃ x : F, ι x = m) {ω : K}
    (hω : σ ω = -ω) (hω0 : ω ≠ 0) (h2 : (2 : K) ≠ 0) {A : Matrix (Fin 3) (Fin 3) K}
    (hAs : Aᵀ = A) (hAA : A * A.map σ = 1) :
    ∃ N : Matrix (Fin 3) (Fin 3) K, N * N * N = 0 ∧ N * N ≠ 0 ∧ (N.map σ)ᵀ = -N ∧
      A * N.map σ = -(N * A) := by
  classical
  have hcard : 3 < Fintype.card F := by omega
  obtain ⟨C, hCdet, hAC⟩ := exists_hilbert90 ι σ hcard hι hω hω0 h2 hAA
  set Cb : Matrix (Fin 3) (Fin 3) K := C.map σ with hCb
  have hCunit : IsUnit C.det := isUnit_iff_ne_zero.2 hCdet
  set Ci : Matrix (Fin 3) (Fin 3) K := C⁻¹ with hCi
  have hCCi : C * Ci = 1 := Matrix.mul_nonsing_inv C hCunit
  have hCiC : Ci * C = 1 := Matrix.nonsing_inv_mul C hCunit
  set Cib : Matrix (Fin 3) (Fin 3) K := Ci.map σ with hCib
  have hCbCib : Cb * Cib = 1 := by
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M.map σ) hCCi
    simpa only [hCb, hCib, Matrix.map_mul, map_one_ringEquiv] using this
  have hCibCb : Cib * Cb = 1 := by
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M.map σ) hCiC
    simpa only [hCb, hCib, Matrix.map_mul, map_one_ringEquiv] using this
  have hCbb : Cb.map σ = C := by
    ext i j
    simp [hCb, hσ]
  have hCibA : Cib = Ci * A := by
    calc Cib = 1 * Cib := (Matrix.one_mul _).symm
      _ = (Ci * C) * Cib := by rw [hCiC]
      _ = Ci * (A * Cb) * Cib := by rw [hAC]
      _ = Ci * A * (Cb * Cib) := by simp only [Matrix.mul_assoc]
      _ = Ci * A := by rw [hCbCib, Matrix.mul_one]
  set M : Matrix (Fin 3) (Fin 3) K := Cbᵀ * C with hM
  have hMs : Mᵀ = M := by
    have h1 : M = Cbᵀ * A * Cb := by rw [hM, ← hAC, Matrix.mul_assoc]
    calc Mᵀ = (Cbᵀ * A * Cb)ᵀ := by rw [h1]
      _ = Cbᵀ * Aᵀ * Cb := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = M := by rw [hAs, h1]
  have hMσ : M.map σ = M := by
    have : M.map σ = Cᵀ * Cb := by
      rw [hM, Matrix.map_mul, Matrix.transpose_map, hCbb]
    rw [this, ← hMs, hM, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hMfix : ∀ i j, σ (M i j) = M i j := fun i j => by
    have := congrFun (congrFun hMσ i) j
    simpa using this
  choose MF' hMF' using fun i j => hfix (M i j) (hMfix i j)
  set MF : Matrix (Fin 3) (Fin 3) F := Matrix.of MF' with hMFdef
  have hMFmap : MF.map ι = M := Matrix.ext fun i j => hMF' i j
  have hMFs : MFᵀ = MF := by
    apply Matrix.map_injective ι.injective
    show MFᵀ.map ι = MF.map ι
    rw [Matrix.transpose_map, hMFmap, hMs]
  have hdetM : M.det ≠ 0 := by
    rw [hM, Matrix.det_mul, Matrix.det_transpose]
    refine mul_ne_zero ?_ hCdet
    have : Cb.det = σ C.det := (RingHom.map_det σ.toRingHom C).symm
    rw [this]
    exact (map_ne_zero σ).2 hCdet
  have hdetMF : MF.det ≠ 0 := by
    intro h0
    apply hdetM
    rw [← hMFmap]
    have := RingHom.map_det ι MF
    rw [h0, map_zero] at this
    exact this.symm
  have h2F : (2 : F) ≠ 0 := fun h0 => h2 (by
    have := congrArg ι h0
    rwa [map_ofNat, map_zero] at this)
  obtain ⟨e, he, hiso⟩ := exists_isotropic (p := p) MF
  obtain ⟨X, hX3, hX2, hXs⟩ := exists_regular_nilpotent h2F hdetMF hMFs he hiso
  set Xk : Matrix (Fin 3) (Fin 3) K := X.map ι with hXk
  have hXk3 : Xk * Xk * Xk = 0 := by
    rw [hXk, ← Matrix.map_mul, ← Matrix.map_mul, hX3]
    ext i j
    simp
  have hXk2 : Xk * Xk ≠ 0 := by
    intro h0
    apply hX2
    apply Matrix.map_injective ι.injective
    show (X * X).map ι = (0 : Matrix (Fin 3) (Fin 3) F).map ι
    rw [Matrix.map_mul, ← hXk, h0]
    ext i j
    simp
  have hXkσ : Xk.map σ = Xk := Matrix.ext fun i j => hι _
  have hXkM : Xkᵀ * M = M * Xk := by
    rw [← hMFmap, hXk, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hXs]
  set N₀ : Matrix (Fin 3) (Fin 3) K := ω • Xk with hN₀
  have hN₀σ : N₀.map σ = -N₀ := by
    rw [hN₀, map_smul_ringEquiv, hXkσ, hω, neg_smul]
  have hN₀M : N₀ᵀ * (Cbᵀ * C) = (Cbᵀ * C) * N₀ := by
    have := hXkM
    rw [hM] at this
    rw [hN₀, Matrix.transpose_smul, Matrix.smul_mul, this, Matrix.mul_smul]
  have hN₀3 : N₀ * N₀ * N₀ = 0 := by
    rw [hN₀]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hXk3, smul_zero]
  have hN₀2' : N₀ * N₀ = (ω * ω) • (Xk * Xk) := by
    rw [hN₀]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hN₀2 : N₀ * N₀ ≠ 0 := by
    rw [hN₀2']
    exact smul_ne_zero (mul_ne_zero hω0 hω0) hXk2
  have hmul : ∀ Y Z : Matrix (Fin 3) (Fin 3) K, (C * Y * Ci) * (C * Z * Ci) = C * (Y * Z) * Ci := by
    intro Y Z
    calc (C * Y * Ci) * (C * Z * Ci) = C * Y * (Ci * C) * Z * Ci := by simp only [Matrix.mul_assoc]
      _ = C * (Y * Z) * Ci := by rw [hCiC, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hcancel : ∀ Y : Matrix (Fin 3) (Fin 3) K, Ci * (C * Y * Ci) * C = Y := by
    intro Y
    calc Ci * (C * Y * Ci) * C = (Ci * C) * Y * (Ci * C) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [hCiC, Matrix.one_mul, Matrix.mul_one]
  have hCibCbT : Cibᵀ * Cbᵀ = 1 := by
    rw [← Matrix.transpose_mul, hCbCib, Matrix.transpose_one]
  have hNσ : (C * N₀ * Ci).map σ = -(Cb * N₀ * Cib) := by
    rw [Matrix.map_mul, Matrix.map_mul, hN₀σ, Matrix.mul_neg, Matrix.neg_mul]
  refine ⟨C * N₀ * Ci, ?_, ?_, ?_, ?_⟩
  · rw [hmul, hmul, hN₀3]
    simp
  · rw [hmul]
    intro h0
    apply hN₀2
    rw [← hcancel (N₀ * N₀), h0]
    simp
  · rw [hNσ, Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_mul]
    congr 1
    calc Cibᵀ * (N₀ᵀ * Cbᵀ) = Cibᵀ * (N₀ᵀ * Cbᵀ) * (C * Ci) := by rw [hCCi, Matrix.mul_one]
      _ = Cibᵀ * (N₀ᵀ * (Cbᵀ * C)) * Ci := by simp only [Matrix.mul_assoc]
      _ = Cibᵀ * ((Cbᵀ * C) * N₀) * Ci := by rw [hN₀M]
      _ = (Cibᵀ * Cbᵀ) * C * N₀ * Ci := by simp only [Matrix.mul_assoc]
      _ = C * N₀ * Ci := by rw [hCibCbT, Matrix.one_mul]
  · rw [hNσ, Matrix.mul_neg]
    congr 1
    calc A * (Cb * N₀ * Cib) = (A * Cb) * N₀ * Cib := by simp only [Matrix.mul_assoc]
      _ = C * N₀ * Cib := by rw [hAC]
      _ = C * N₀ * Ci * A := by rw [hCibA, Matrix.mul_assoc _ Ci A]

end Skew

end CFSG.QuasithinUnique.Setup.Family
