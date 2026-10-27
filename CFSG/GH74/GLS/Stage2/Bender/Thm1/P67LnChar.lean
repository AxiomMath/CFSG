module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnAut
public import CFSG.GH74.GLS.Stage2.OddAut.KerFlag

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.Stage2.OddAut.KerFlag

section Q

open CFSG.GH74.GLS.Stage2.OddAut.KerFlag

variable {K : Type} [Field K] [Finite K] {n : ℕ}

omit [Finite K] in
theorem det_eq_one_of_pow_eq_one {p : ℕ} [Fact p.Prime] [CharP K p] {M : Matrix (Fin n) (Fin n) K}
    (hM : M ^ p = 1) : M.det = 1 := by
  have h2 : M.det ^ p = 1 := by rw [← Matrix.det_pow, hM, Matrix.det_one]
  have h3 : (M.det - 1) ^ p = 0 := by rw [sub_pow_char, h2, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp h3)

omit [Finite K] in
theorem pow_eq_zero_of_one_add_pow_eq_one (p : ℕ) [Fact p.Prime] [CharP K p]
    {M : Matrix (Fin n) (Fin n) K} (hM : ((1 : Matrix (Fin n) (Fin n) K) + M) ^ p = 1) :
    M ^ p = 0 := by
  have h := congrArg (Polynomial.aeval M)
    (add_pow_char (R := Polynomial K) (p := p) (1 : Polynomial K) Polynomial.X)
  simp only [map_pow, map_add, map_one, Polynomial.aeval_X] at h
  rw [hM, one_pow] at h
  have h' : (1 : Matrix (Fin n) (Fin n) K) + 0 = 1 + M ^ p := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

end Q

section Qgrp

open CFSG.GH74.GLS.Stage2.OddAut.KerFlag

variable {K : Type} [Field K] [Finite K] {n : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]

omit [Finite K] in
theorem one_add_pow_p {N θ : Matrix (Fin n) (Fin n) K} (hθ : θ ∈ TN N) :
    ((1 : Matrix (Fin n) (Fin n) K) + θ) ^ p = 1 := by
  have h := one_add_pow_char_pow p (K := K) (M := θ) (m := 2) (e := 1)
    (by rw [sq]; exact TN_mul_eq_zero hθ hθ) (by simpa using (Fact.out : p.Prime).two_le)
  simpa using h

@[expose] def slOf (N : Matrix (Fin n) (Fin n) K) (θ : ↥(TN N)) :
    Matrix.SpecialLinearGroup (Fin n) K :=
  ⟨1 + (θ : Matrix (Fin n) (Fin n) K), det_eq_one_of_pow_eq_one (p := p) (one_add_pow_p p θ.2)⟩

omit [Finite K] in
theorem coe_slOf (N : Matrix (Fin n) (Fin n) K) (θ : ↥(TN N)) :
    ((slOf p N θ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + (θ : Matrix (Fin n) (Fin n) K) := rfl

omit [Finite K] in
theorem slOf_add (N : Matrix (Fin n) (Fin n) K) (θ θ' : ↥(TN N)) :
    slOf p N (θ + θ') = slOf p N θ * slOf p N θ' := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_slOf, coe_slOf, coe_slOf]
  have := TN_mul_eq_zero θ.2 θ'.2
  simp only [Submodule.coe_add, mul_add, add_mul, Matrix.mul_one, Matrix.one_mul, this]
  abel

omit [Finite K] in
theorem slOf_zero (N : Matrix (Fin n) (Fin n) K) : slOf p N 0 = 1 := by
  apply Subtype.ext
  simp [coe_slOf]

@[expose] def qHom (N : Matrix (Fin n) (Fin n) K) :
    Multiplicative ↥(TN N) →* projectiveSL n K where
  toFun θ := proj n K (slOf p N (Multiplicative.toAdd θ))
  map_one' := by simp [slOf_zero]
  map_mul' θ θ' := by
    simp only [toAdd_mul, slOf_add, map_mul]

end Qgrp

section Inv

variable {K : Type} [Field K] {n : ℕ}

theorem map_mul_ringEquiv (σ : K ≃+* K) (L M : Matrix (Fin n) (Fin n) K) :
    (L * M).map σ = L.map σ * M.map σ :=
  Matrix.map_mul (f := σ.toRingHom)

theorem map_mulVec_ringEquiv (σ : K ≃+* K) (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    M.map σ *ᵥ (σ ∘ v) = σ ∘ (M *ᵥ v) := by
  funext i
  exact (RingHom.map_mulVec σ.toRingHom M v i).symm

theorem conj_map_mem_TN {N : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} {σ : K ≃+* K}
    (hBN : (B : Matrix (Fin n) (Fin n) K) * N.map σ = N * (B : Matrix (Fin n) (Fin n) K))
    {θ : Matrix (Fin n) (Fin n) K} (hθ : θ ∈ TN N) :
    (B : Matrix (Fin n) (Fin n) K) * θ.map σ * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      ∈ TN N := by
  have hB1 : (B : Matrix (Fin n) (Fin n) K) *
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.mul_inv B
  have hB2 : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.inv_mul B
  have hBN' : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N =
      N.map σ * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    calc ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N
        = ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N *
          ((B : Matrix (Fin n) (Fin n) K) * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [hB1, Matrix.mul_one]
      _ = ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (N * (B : Matrix (Fin n) (Fin n) K)) *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by simp only [Matrix.mul_assoc]
      _ = ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((B : Matrix (Fin n) (Fin n) K) * N.map σ) *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hBN]
      _ = N.map σ * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [← Matrix.mul_assoc, hB2, Matrix.one_mul]
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · calc N * ((B : Matrix (Fin n) (Fin n) K) * θ.map σ *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        = (N * (B : Matrix (Fin n) (Fin n) K)) * θ.map σ *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by simp only [Matrix.mul_assoc]
      _ = ((B : Matrix (Fin n) (Fin n) K) * N.map σ) * θ.map σ *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [← hBN]
      _ = (B : Matrix (Fin n) (Fin n) K) * (N * θ).map σ *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [map_mul_ringEquiv]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hθ.1]; simp
  · calc (B : Matrix (Fin n) (Fin n) K) * θ.map σ *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N
        = (B : Matrix (Fin n) (Fin n) K) * θ.map σ *
          (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N) := by
          simp only [Matrix.mul_assoc]
      _ = (B : Matrix (Fin n) (Fin n) K) * θ.map σ *
          (N.map σ * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [hBN']
      _ = (B : Matrix (Fin n) (Fin n) K) * (θ * N).map σ *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [map_mul_ringEquiv]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hθ.2.1]; simp
  ·
    set y : Fin n → K := ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x with hy
    have hBy : (B : Matrix (Fin n) (Fin n) K) *ᵥ y = x := by
      rw [hy, Matrix.mulVec_mulVec, hB1, Matrix.one_mulVec]
    have hNy : N.map σ *ᵥ y = 0 := by
      have h1 : (B : Matrix (Fin n) (Fin n) K) *ᵥ (N.map σ *ᵥ y) = 0 := by
        rw [Matrix.mulVec_mulVec, hBN, ← Matrix.mulVec_mulVec, hBy, hx]
      have h2 := congrArg (fun v => ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) h1
      simpa [Matrix.mulVec_mulVec, hB2] using h2
    set w : Fin n → K := σ.symm ∘ y with hw
    have hσw : σ ∘ w = y := by
      funext i; simp [hw]
    have hNw : N *ᵥ w = 0 := by
      have h1 : N.map σ *ᵥ (σ ∘ w) = σ ∘ (N *ᵥ w) := map_mulVec_ringEquiv σ N w
      rw [hσw, hNy] at h1
      funext i
      have := congrFun h1 i
      simpa using this.symm
    have hθw : θ *ᵥ w = 0 := hθ.2.2 w hNw
    have hθy : θ.map σ *ᵥ y = 0 := by
      have h1 : θ.map σ *ᵥ (σ ∘ w) = σ ∘ (θ *ᵥ w) := map_mulVec_ringEquiv σ θ w
      rw [hσw, hθw] at h1
      rw [h1]; funext i; simp
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change (B : Matrix (Fin n) (Fin n) K) *ᵥ (θ.map σ *ᵥ y) = 0
    rw [hθy, Matrix.mulVec_zero]

end Inv

section Act

variable {K : Type} [Field K] [Finite K] {n : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem map_one_add (σ : K ≃+* K) (θ : Matrix (Fin n) (Fin n) K) :
    (1 + θ).map σ = 1 + θ.map σ := by
  ext i j
  by_cases h : i = j <;> simp [h]

omit [Finite K] in
theorem semilin_qHom {N : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} {σ : K ≃+* K}
    (hBN : (B : Matrix (Fin n) (Fin n) K) * N.map σ = N * (B : Matrix (Fin n) (Fin n) K))
    (θ : Multiplicative ↥(TN N)) :
    (conjAut n K B * fieldAut n K σ) (qHom p N θ) =
      qHom p N (Multiplicative.ofAdd (⟨(B : Matrix (Fin n) (Fin n) K) *
        ((Multiplicative.toAdd θ : ↥(TN N)) : Matrix (Fin n) (Fin n) K).map σ *
        ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        conj_map_mem_TN hBN (Multiplicative.toAdd θ).2⟩ : ↥(TN N))) := by
  have hB1 : (B : Matrix (Fin n) (Fin n) K) *
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.mul_inv B
  change (conjAut n K B * fieldAut n K σ) (proj n K (slOf p N (Multiplicative.toAdd θ))) =
    proj n K (slOf p N _)
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe, coe_slOf, coe_slOf]
  simp only [RingHom.mapMatrix_apply, toAdd_ofAdd]
  change (B : Matrix (Fin n) (Fin n) K) *
    (1 + ((Multiplicative.toAdd θ : ↥(TN N)) : Matrix (Fin n) (Fin n) K)).map σ *
    ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
  rw [map_one_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hB1]

end Act

section Eq

variable {K : Type} [Field K] {n : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]

theorem eq_one_of_pow_char {r : K} (h : r ^ p = 1) : r = 1 := by
  have h3 : (r - 1) ^ p = 0 := by rw [sub_pow_char, h, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp h3)

theorem eq_of_proj_eq_of_pow (hn : 0 < n) {g h : Matrix.SpecialLinearGroup (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K) ^ p = 1) (hh : (h : Matrix (Fin n) (Fin n) K) ^ p = 1)
    (hgh : proj n K g = proj n K h) : g = h := by
  have h2 := proj_eq_proj_iff.mp hgh
  rw [scalars_eq_center] at h2
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h2
  have hh' : (h : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * Matrix.scalar (Fin n) r := by
    rw [hr, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have hcomm : Commute (g : Matrix (Fin n) (Fin n) K) (Matrix.scalar (Fin n) r) :=
    (Matrix.scalar_commute r (fun _ => Commute.all _ _) _).symm
  have h3 : (Matrix.scalar (Fin n) (r ^ p) : Matrix (Fin n) (Fin n) K) = 1 := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) K => M ^ p) hh'
    simp only [hh, hcomm.mul_pow, hg, one_mul, ← map_pow] at this
    exact this.symm
  have h4 : r ^ p = 1 := by
    have := congrFun (congrFun h3 ⟨0, hn⟩) ⟨0, hn⟩
    simpa [Matrix.scalar_apply] using this
  have h5 : r = 1 := eq_one_of_pow_char p h4
  rw [h5] at hh'
  apply Subtype.ext
  rw [hh']
  simp

end Eq

section Fix

variable {K : Type} [Field K] [Finite K] {n : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]

omit [Finite K] in
theorem conj_proj_qHom {N : Matrix (Fin n) (Fin n) K} {g : Matrix.SpecialLinearGroup (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K) = 1 + N) (θ : Multiplicative ↥(TN N)) :
    MulAut.conj (proj n K g) (qHom p N θ) = qHom p N θ := by
  have hcomm : g * slOf p N (Multiplicative.toAdd θ) = slOf p N (Multiplicative.toAdd θ) * g := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, coe_slOf]
    have h1 := (Multiplicative.toAdd θ).2.1
    have h2 := (Multiplicative.toAdd θ).2.2.1
    simp only [mul_add, add_mul, Matrix.mul_one, Matrix.one_mul]
    rw [h1, h2]
    abel
  change proj n K g * proj n K (slOf p N _) * (proj n K g)⁻¹ = proj n K (slOf p N _)
  rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, hcomm]

omit [Finite K] in
theorem isPGroup_range_qHom (N : Matrix (Fin n) (Fin n) K) : IsPGroup p (qHom p N).range := by
  have h1 : IsPGroup p (Multiplicative ↥(TN N)) := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hx : x ^ p = 1 := by
      rw [← ofAdd_toAdd x, ← ofAdd_nsmul]
      have : p • (Multiplicative.toAdd x) = 0 := by
        rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
      rw [this]
      rfl
    have h2 := orderOf_dvd_of_pow_eq_one hx
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
      (by simpa using h2 : orderOf x ∣ p ^ 1)
    exact ⟨k, hk⟩
  exact h1.of_surjective (qHom p N).rangeRestrict (MonoidHom.rangeRestrict_surjective _)

end Fix

section Norm

variable {K : Type} [Field K] [Finite K] {n : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]

theorem normalizes_N_of_comm (hn : 3 ≤ n) {g : Matrix.SpecialLinearGroup (Fin n) K}
    {N : Matrix (Fin n) (Fin n) K} (hg : (g : Matrix (Fin n) (Fin n) K) = 1 + N)
    (hgp : (g : Matrix (Fin n) (Fin n) K) ^ p = 1) {B : GL (Fin n) K} {σ : K ≃+* K}
    (hcomm : MulAut.conj (proj n K g) * (conjAut n K B * fieldAut n K σ) =
      (conjAut n K B * fieldAut n K σ) * MulAut.conj (proj n K g)) :
    (B : Matrix (Fin n) (Fin n) K) * N.map σ = N * (B : Matrix (Fin n) (Fin n) K) := by
  set G : GL (Fin n) K := Matrix.SpecialLinearGroup.toGL g with hG
  have hvG : MulAut.conj (proj n K g) = conjAut n K G := (conjAut_toGL g).symm
  have htr := standard_automorphism_transport (K := K) (n := n)
  set X : GL (Fin n) K :=
    G⁻¹ * (B * Matrix.GeneralLinearGroup.map (σ : K →+* K) G * B⁻¹) with hX
  have hzv : conjAut n K B * fieldAut n K σ * conjAut n K G *
      (conjAut n K B * fieldAut n K σ)⁻¹ = conjAut n K G := by
    rw [← hvG, mul_inv_eq_iff_eq_mul]
    exact hcomm.symm
  have hcX : conjAut n K X * fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, hX, map_mul, map_mul, map_mul, map_inv, map_inv,
      ← htr.2.2.1 σ G]
    simp only [_root_.mul_inv_rev] at hzv
    calc (conjAut n K G)⁻¹ * (conjAut n K B * (fieldAut n K σ * conjAut n K G *
          (fieldAut n K σ)⁻¹) * (conjAut n K B)⁻¹)
        = (conjAut n K G)⁻¹ * (conjAut n K B * fieldAut n K σ * conjAut n K G *
          ((fieldAut n K σ)⁻¹ * (conjAut n K B)⁻¹)) := by group
      _ = 1 := by rw [hzv]; group
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn X 1 hcX
  have hGp : G ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hgp
  have hBG : B * Matrix.GeneralLinearGroup.map (σ : K →+* K) G * B⁻¹ =
      G * Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    rw [hc, hX]; group
  have hc1 : c = 1 := by
    have h1 : (B * Matrix.GeneralLinearGroup.map (σ : K →+* K) G * B⁻¹) ^ p = 1 := by
      rw [conj_pow, ← map_pow, hGp, map_one]
      group
    rw [hBG, (scalar_commute' c G).symm.mul_pow, hGp, one_mul, ← map_pow] at h1
    have h2 := congrArg (fun U : GL (Fin n) K =>
      (U : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at h2
    apply Units.ext
    exact eq_one_of_pow_char p (by rw [← Units.val_pow_eq_pow_val]; exact h2)
  subst hc1
  rw [map_one] at hc
  have hB : B * Matrix.GeneralLinearGroup.map (σ : K →+* K) G = G * B := by
    rw [hX] at hc
    have h1 : G⁻¹ * (B * Matrix.GeneralLinearGroup.map (σ : K →+* K) G * B⁻¹) = 1 := hc.symm
    calc B * Matrix.GeneralLinearGroup.map (σ : K →+* K) G
        = G * (G⁻¹ * (B * Matrix.GeneralLinearGroup.map (σ : K →+* K) G * B⁻¹)) * B := by group
      _ = G * B := by rw [h1]; group
  have hBm := congrArg Units.val hB
  rw [Units.val_mul, Units.val_mul] at hBm
  have hGm : ((G : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + N := hg
  have hσG : ((Matrix.GeneralLinearGroup.map (σ : K →+* K) G : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (1 + N).map σ := by
    rw [← hGm]; rfl
  rw [hσG, hGm, map_one_add] at hBm
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at hBm
  exact add_left_cancel hBm

end Norm

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.Stage2.OddAut.KerFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem cf67_Ln_char (hn : 3 ≤ n) (p : ℕ) [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hcen : Subgroup.center (projectiveSL n K) = ⊥)
    {V Z : Subgroup (MulAut (projectiveSL n K))} (h2 : N2Cfg (projectiveSL n K) p V Z)
    (h3 : N3Full (projectiveSL n K) V Z) : False := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨-, -, hVe, hVc, -, hZodd, hZcop, hZbot, hcomm⟩ := id h2
  have hVE : ∀ α ∈ V, α ∈ semilinearAutGroup n K := by
    intro α hα
    have hpow : α ^ (p ^ 2) = 1 := by
      have := pow_card_eq_one' (G := ↥V) (x := (⟨α, hα⟩ : ↥V))
      rw [hVc] at this
      exact congrArg Subtype.val this
    obtain ⟨A, σ, h⟩ := exists_conj_field_of_odd hn (hpodd.pow) hpow
    exact mem_semilinearAutGroup_iff.mpr ⟨A, σ, h⟩
  obtain ⟨v, hvV, hv1, A, hvA⟩ := exists_inner_diag_of_elem hn hVe hVc hVE
  have hvp : v ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := V) v hvV
  obtain ⟨g, hvg, hgp⟩ := exists_unipotent_lift hn p (A := A) (by rw [← hvA]; exact hvp)
  have hvg' : v = MulAut.conj (proj n K g) := hvA.trans hvg
  set N : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K) - 1 with hNdef
  have hgN : (g : Matrix (Fin n) (Fin n) K) = 1 + N := by rw [hNdef]; abel
  have hNp : N ^ p = 0 := pow_eq_zero_of_one_add_pow_eq_one p (by rw [← hgN]; exact hgp)
  have hNne : N ≠ 0 := by
    intro h0
    apply hv1
    have hg1 : g = 1 := by
      apply Subtype.ext
      rw [hgN, h0]
      simp
    rw [hvg', hg1, map_one, map_one]
  set Q := (qHom p N).range with hQ
  have hQle : Q ≤ fixSub v := by
    rintro _ ⟨θ, rfl⟩
    rw [mem_fixSub, hvg']
    exact conj_proj_qHom p hgN θ
  have hQr : IsPGroup p ↥Q := isPGroup_range_qHom p N
  have hZstruct : ∀ z ∈ Z, ∃ (B : GL (Fin n) K) (σ : K ≃+* K),
      z = conjAut n K B * fieldAut n K σ ∧
        (B : Matrix (Fin n) (Fin n) K) * N.map σ = N * (B : Matrix (Fin n) (Fin n) K) := by
    intro z hz
    have hpow : z ^ (Nat.card ↥Z) = 1 := by
      have := pow_card_eq_one' (G := ↥Z) (x := (⟨z, hz⟩ : ↥Z))
      exact congrArg Subtype.val this
    obtain ⟨B, σ, hBσ⟩ := exists_conj_field_of_odd hn hZodd hpow
    refine ⟨B, σ, hBσ, normalizes_N_of_comm p hn hgN hgp (B := B) (σ := σ) ?_⟩
    have := hcomm v hvV z hz
    rw [hvg', hBσ] at this
    exact this
  have hQinv : ∀ z ∈ Z, ∀ c ∈ Q, z c ∈ Q := by
    intro z hz c hc
    obtain ⟨B, σ, hzBσ, hBN⟩ := hZstruct z hz
    obtain ⟨θ, rfl⟩ := hc
    rw [hzBσ, semilin_qHom p hBN θ]
    exact ⟨_, rfl⟩
  have hfix := rstep_fix hcen h2 h3 hvV hv1 hQle hQr hQinv
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZbot
  obtain ⟨B, σ, hzBσ, hBN⟩ := hZstruct z z.2
  have hBθ : ∀ θ ∈ TN N, (B : Matrix (Fin n) (Fin n) K) * θ.map σ =
      θ * (B : Matrix (Fin n) (Fin n) K) := by
    intro θ hθ
    have h1 : (z : MulAut (projectiveSL n K)) (qHom p N (Multiplicative.ofAdd ⟨θ, hθ⟩)) =
        qHom p N (Multiplicative.ofAdd ⟨θ, hθ⟩) := hfix z z.2 _ ⟨_, rfl⟩
    rw [hzBσ, semilin_qHom p hBN] at h1
    change proj n K (slOf p N _) = proj n K (slOf p N _) at h1
    have hu : ∀ θ' : ↥(TN N), ((slOf p N θ' : Matrix.SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) ^ p = 1 := fun θ' => by
      rw [coe_slOf]; exact one_add_pow_p p θ'.2
    have h2 := eq_of_proj_eq_of_pow p (by omega) (hu _) (hu _) h1
    have h3 := congrArg (fun s : Matrix.SpecialLinearGroup (Fin n) K =>
      (s : Matrix (Fin n) (Fin n) K)) h2
    simp only [coe_slOf, toAdd_ofAdd] at h3
    have h4 := add_left_cancel h3
    have hB2 : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
        1 := Units.inv_mul B
    calc (B : Matrix (Fin n) (Fin n) K) * θ.map σ
        = (B : Matrix (Fin n) (Fin n) K) * θ.map σ *
          (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) := by
          rw [hB2, Matrix.mul_one]
      _ = ((B : Matrix (Fin n) (Fin n) K) * θ.map σ *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * (B : Matrix (Fin n) (Fin n) K) := by
          simp only [Matrix.mul_assoc]
      _ = θ * (B : Matrix (Fin n) (Fin n) K) := by rw [h4]
  obtain ⟨y, w, hy, hNy, hw⟩ := exists_ker_range hNp hNne
  obtain ⟨ψ, hψ0, hψ1, hψ2⟩ := exists_dual_vanishing hy hNy hw
  have hBB : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      1 := Units.inv_mul B
  obtain ⟨hσ1, a, ha⟩ := sigma_one_and_scalar hy hNy hψ0 hψ1 hψ2 hBB hBθ
  subst hσ1
  have hBN' : (B : Matrix (Fin n) (Fin n) K) * N = N * (B : Matrix (Fin n) (Fin n) K) := by
    simpa using hBN
  have hnil := nilpotent_of_scalar_on_ker hNp hBN' ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h1 : (B : Matrix (Fin n) (Fin n) K) ^ p = 0 := by simpa using hnil
    have h2 : (B : Matrix (Fin n) (Fin n) K).det ^ p = 0 := by
      have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      rw [← Matrix.det_pow, h1, Matrix.det_zero]
    exact Matrix.GeneralLinearGroup.det_ne_zero B
      ((pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp h2)
  set U : GL (Fin n) K := Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 a ha0)⁻¹ * B with hU
  have hUm : (U : Matrix (Fin n) (Fin n) K) = a⁻¹ • (B : Matrix (Fin n) (Fin n) K) := by
    rw [hU, Units.val_mul]
    have h1 : ((Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 a ha0)⁻¹ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = a⁻¹ • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      simp
    rw [h1, Matrix.smul_mul, Matrix.one_mul]
  have hMp : (a⁻¹ • ((B : Matrix (Fin n) (Fin n) K) - a • 1)) ^ p = 0 := by
    rw [smul_pow, hnil, smul_zero]
  have hUp' : (U : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
    have h1 : (U : Matrix (Fin n) (Fin n) K) =
        1 + a⁻¹ • ((B : Matrix (Fin n) (Fin n) K) - a • 1) := by
      rw [hUm, smul_sub, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      abel
    rw [h1]
    have := one_add_pow_char_pow p (K := K) (M := a⁻¹ • ((B : Matrix (Fin n) (Fin n) K) - a • 1))
      (m := p) (e := 1) hMp (by simp)
    simpa using this
  have hUp : U ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hUp']; rfl)
  have hzp : (z : MulAut (projectiveSL n K)) ^ p = 1 := by
    rw [hzBσ, map_one, mul_one]
    have hB : B = Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 a ha0) * U := by
      rw [hU, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    rw [hB, map_mul, conjAut_scalar', one_mul, ← map_pow, hUp, map_one]
  have hord : orderOf (z : MulAut (projectiveSL n K)) ∣ Nat.card ↥Z := by
    have := orderOf_dvd_natCard z
    rwa [← Subgroup.orderOf_coe] at this
  have h1 : orderOf (z : MulAut (projectiveSL n K)) ∣ p := orderOf_dvd_of_pow_eq_one hzp
  have h2 : orderOf (z : MulAut (projectiveSL n K)) = 1 := Nat.eq_one_of_dvd_coprimes hZcop hord h1
  exact hz1 (Subtype.ext (orderOf_eq_one_iff.mp h2))

end CFSG.GH74.GLS.Stage2.Bender.Thm1
