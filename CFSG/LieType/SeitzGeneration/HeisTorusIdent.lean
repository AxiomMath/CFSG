module

public import CFSG.LieType.SeitzGeneration.HeisTorusDefs
public import CFSG.LieType.SeitzGeneration.HeisLinearFourier

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F] {p : ℕ}

theorem inv_diagonal_of_ne_zero {n : Type*} [Fintype n] [DecidableEq n] {d : n → F}
    (hd : ∀ i, d i ≠ 0) : (diagonal d)⁻¹ = diagonal (fun i => (d i)⁻¹) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [diagonal_mul_diagonal]
  simp [hd]

theorem zFix_comm_of_fix [NeZero p] {x : Matrix (Fin p) (Fin p) F} (hx : IsUnit x.det)
    (hx0 : x *ᵥ Pi.single 0 1 = Pi.single 0 1) {ν : F} (hν : ν ≠ 0) :
    zFix ν * x * (zFix ν)⁻¹ * x⁻¹ =
      1 + (1 - (ν ^ p)⁻¹) •
        vecMulVec (Pi.single 0 1) (Pi.single 0 1 ᵥ* x⁻¹ - Pi.single 0 1) := by
  have hcolfun : x.col 0 = Pi.single 0 1 := by
    rw [← mulVec_single_one]
    exact hx0
  have hcol : ∀ a : Fin p, x a 0 = (Pi.single (0 : Fin p) (1 : F) : Fin p → F) a :=
    fun a => congrFun hcolfun a
  have hx00 : x 0 0 = 1 := by rw [hcol 0, Pi.single_eq_same]
  have hxa0 : ∀ a : Fin p, a ≠ 0 → x a 0 = 0 := fun a ha => by
    rw [hcol a, Pi.single_eq_of_ne ha]
  have hpow : ν ^ p = ν ^ (p - 1) * ν := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne p))]
  have hcp : ν ^ (p - 1) ≠ 0 := pow_ne_zero _ hν
  have hρ : (ν ^ (p - 1))⁻¹ * ν⁻¹ = (ν ^ p)⁻¹ := by
    rw [← mul_inv, ← hpow]
  have hdn : ∀ i : Fin p, (if (i : ℕ) = 0 then (ν ^ (p - 1))⁻¹ else ν) ≠ 0 := by
    intro i
    split_ifs
    · exact inv_ne_zero hcp
    · exact hν
  have hconj : zFix ν * x * (zFix ν)⁻¹ =
      x + ((ν ^ p)⁻¹ - 1) • vecMulVec (Pi.single 0 1) (Pi.single 0 1 ᵥ* x - Pi.single 0 1) := by
    rw [zFix, inv_diagonal_of_ne_zero hdn]
    ext a b
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.smul_apply,
      vecMulVec_apply, Pi.sub_apply, single_vecMul, Pi.smul_apply, one_smul, Matrix.row_apply,
      smul_eq_mul]
    rcases eq_or_ne a 0 with rfl | ha <;> rcases eq_or_ne b 0 with rfl | hb
    · simp [hx00, hcp, Fin.val_eq_zero_iff]
    · simp [hb, hcp, Fin.val_eq_zero_iff, Pi.single_apply, hx00]
      linear_combination (x 0 b) * hρ
    · simp [ha, Fin.val_eq_zero_iff, Pi.single_apply, hxa0 a ha]
    · simp [ha, hb, Fin.val_eq_zero_iff, Pi.single_apply]
      rw [mul_right_comm, mul_inv_cancel₀ hν, one_mul]
  have hxinv : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv x hx
  rw [hconj, add_mul, Matrix.smul_mul, Matrix.vecMulVec_mul, Matrix.sub_vecMul,
    Matrix.vecMul_vecMul, hxinv, Matrix.vecMul_one]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.sub_apply,
    Matrix.one_apply, smul_eq_mul]
  ring

theorem diag_comm_of_range {I : Finset (Fin p)} {Y : Matrix (Fin p) (Fin p) F}
    (hY : ∀ a b, a ∉ I → Y a b = 0)
    (hx : IsUnit (1 + Y).det) {z : Fin p → F} (hz0 : ∀ i, z i ≠ 0) (hz1 : ∀ i ∈ I, z i = 1) :
    diagonal z * (1 + Y) * (diagonal z)⁻¹ * (1 + Y)⁻¹ = 1 + Y * ((diagonal z)⁻¹ - 1) := by
  rw [inv_diagonal_of_ne_zero hz0]
  have hDE : diagonal z * diagonal (fun i => (z i)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal]
    simp [hz0]
  have hwY : ∀ w : Fin p → F, (∀ i ∈ I, w i = 1) → diagonal w * Y = Y := by
    intro w hw
    ext a b
    by_cases ha : a ∈ I
    · rw [diagonal_mul, hw a ha, one_mul]
    · rw [diagonal_mul, hY a b ha, mul_zero]
  have h1 : diagonal z * Y = Y := hwY z hz1
  have h2 : diagonal (fun i => (z i)⁻¹) * Y = Y := hwY _ fun i hi => by simp [hz1 i hi]
  have hEY : (diagonal (fun i => (z i)⁻¹) - 1) * Y = 0 := by
    rw [sub_mul, h2, one_mul, sub_self]
  have hYEY : Y * (diagonal (fun i => (z i)⁻¹) - 1) * Y = 0 := by
    rw [mul_assoc, hEY, mul_zero]
  have hconj : diagonal z * (1 + Y) * diagonal (fun i => (z i)⁻¹) =
      1 + Y * diagonal (fun i => (z i)⁻¹) := by
    rw [mul_add, mul_one, h1, add_mul, hDE]
  have hfac : (1 + Y * (diagonal (fun i => (z i)⁻¹) - 1)) * (1 + Y) =
      1 + Y * diagonal (fun i => (z i)⁻¹) := by
    rw [add_mul, one_mul, mul_add, mul_one, hYEY, add_zero, mul_sub, mul_one]
    abel
  rw [hconj, ← hfac, mul_assoc, Matrix.mul_nonsing_inv (1 + Y) hx, mul_one]

theorem geom_sum_fin_eq_zero {u : F} (hu : u ^ p = 1) (hu1 : u ≠ 1) :
    ∑ k : Fin p, u ^ (k : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => u ^ k) p]
  have h := geom_sum_mul u p
  rw [hu, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hu1)

theorem heis_natCast_ne_zero {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp : 2 ≤ p) :
    (p : F) ≠ 0 := by
  haveI : NeZero p := ⟨by omega⟩
  haveI := hζ.neZero'
  exact NeZero.ne _

theorem heisFourierMat_mul_inv_entries {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp : 2 ≤ p) :
    heisFourierMat ζ * Matrix.of (fun i j : Fin p => (p : F)⁻¹ * (ζ ^ ((i : ℕ) * (j : ℕ)))⁻¹) =
      1 := by
  haveI : NeZero p := ⟨by omega⟩
  have hp0 : (p : F) ≠ 0 := heis_natCast_ne_zero hζ hp
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hpow : ∀ n : ℕ, (ζ ^ n) ^ p = 1 := fun n => by
    rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ k : Fin p, heisFourierMat ζ a k *
      Matrix.of (fun i j : Fin p => (p : F)⁻¹ * (ζ ^ ((i : ℕ) * (j : ℕ)))⁻¹) k b =
      (p : F)⁻¹ * (ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) ^ (k : ℕ) := by
    intro k
    simp only [heisFourierMat, Matrix.of_apply]
    rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (k : ℕ) (b : ℕ)]
    ring
  simp only [key]
  rw [← Finset.mul_sum]
  by_cases hab : a = b
  · subst hab
    have hu : ζ ^ (a : ℕ) * (ζ ^ (a : ℕ))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hζ0)
    simp [hu, hp0]
  · have hu1 : ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹ ≠ 1 := by
      intro h
      apply hab
      apply Fin.ext
      exact hζ.pow_inj a.isLt b.isLt ((mul_inv_eq_one₀ (pow_ne_zero _ hζ0)).mp h)
    have hup : (ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) ^ p = 1 := by
      rw [mul_pow, inv_pow, hpow, hpow, inv_one, mul_one]
    rw [geom_sum_fin_eq_zero hup hu1, mul_zero, if_neg hab]

theorem heisFourierMat_inv {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp : 2 ≤ p) :
    (heisFourierMat ζ)⁻¹ = Matrix.of (fun i j : Fin p => (p : F)⁻¹ * (ζ ^ ((i : ℕ) * (j : ℕ)))⁻¹) :=
  Matrix.inv_eq_right_inv (heisFourierMat_mul_inv_entries hζ hp)

theorem fourierBirefl_apply (hp : 2 ≤ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p) {ν : F} (hν : ν ≠ 0)
    (a b : Fin p) : fourierBirefl ζ ν a b = (if a = b then 1 else 0) +
      (p : F)⁻¹ * ((ν - 1) + (ν⁻¹ - 1) * ζ ^ (a : ℕ) * (ζ ^ (b : ℕ))⁻¹) := by
  haveI : NeZero p := ⟨by omega⟩
  obtain ⟨Ψ, hΨinv, hΨe⟩ : ∃ Ψ : Matrix (Fin p) (Fin p) F, (heisFourierMat ζ)⁻¹ = Ψ ∧
      ∀ i j : Fin p, Ψ i j = (p : F)⁻¹ * (ζ ^ ((i : ℕ) * (j : ℕ)))⁻¹ :=
    ⟨_, heisFourierMat_inv hζ hp, fun i j => by simp⟩
  have hΦΨ : heisFourierMat ζ * Ψ = 1 := by
    rw [← hΨinv]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_heisFourierMat_ne_zero hζ))
  have hv1 : ((1 : Fin p) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < p by omega)]
  have h10 : (1 : Fin p) ≠ 0 := by
    intro h
    have h' := congrArg Fin.val h
    rw [hv1, Fin.val_zero] at h'
    exact one_ne_zero h'
  have hp1 : p ≠ 1 := by omega
  have hk1 : ∀ k : Fin p, (k : ℕ) = 1 ↔ k = 1 := fun k =>
    ⟨fun h => Fin.ext (h.trans hv1.symm), fun h => by rw [h]; exact hv1⟩
  have hT : ∀ k : Fin p, (if (k : ℕ) = 0 then ν else if (k : ℕ) = 1 then ν⁻¹ else 1) =
      1 + (ν - 1) * (if k = 0 then 1 else 0) + (ν⁻¹ - 1) * (if k = 1 then 1 else 0) := by
    intro k
    simp only [Fin.val_eq_zero_iff, hk1]
    by_cases h0 : k = 0
    · subst h0
      simp [h10.symm, hp1] <;> ring
    · by_cases h1 : k = 1
      · subst h1
        simp [h10, hp1] <;> ring
      · simp [h0, h1]
  have hsplit : ∀ A B : Fin p → F,
      ∑ k : Fin p, A k * (1 + (ν - 1) * (if k = 0 then 1 else 0) +
        (ν⁻¹ - 1) * (if k = 1 then 1 else 0)) * B k =
      ∑ k : Fin p, A k * B k + (ν - 1) * (A 0 * B 0) + (ν⁻¹ - 1) * (A 1 * B 1) := by
    intro A B
    rw [Finset.sum_congr rfl fun k _ => (show A k * (1 + (ν - 1) * (if k = 0 then 1 else 0) +
        (ν⁻¹ - 1) * (if k = 1 then 1 else 0)) * B k = A k * B k +
        (ν - 1) * (if k = 0 then A k * B k else 0) +
        (ν⁻¹ - 1) * (if k = 1 then A k * B k else 0) by split_ifs <;> ring)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp
  have hΦ0 : heisFourierMat ζ a 0 = 1 := by simp [heisFourierMat]
  have hΦ1 : heisFourierMat ζ a 1 = ζ ^ (a : ℕ) := by
    simp only [heisFourierMat, Matrix.of_apply, hv1, mul_one]
  have hΨ0 : Ψ 0 b = (p : F)⁻¹ := by rw [hΨe]; simp
  have hΨ1 : Ψ 1 b = (p : F)⁻¹ * (ζ ^ (b : ℕ))⁻¹ := by rw [hΨe, hv1, one_mul]
  have hsum1 : ∑ k : Fin p, heisFourierMat ζ a k * Ψ k b = if a = b then 1 else 0 := by
    have h := congrFun (congrFun hΦΨ a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  have hmain : ∑ k : Fin p, heisFourierMat ζ a k * (1 + (ν - 1) * (if k = 0 then 1 else 0) +
      (ν⁻¹ - 1) * (if k = 1 then 1 else 0)) * Ψ k b =
      ∑ k : Fin p, heisFourierMat ζ a k * Ψ k b + (ν - 1) * (heisFourierMat ζ a 0 * Ψ 0 b) +
      (ν⁻¹ - 1) * (heisFourierMat ζ a 1 * Ψ 1 b) :=
    hsplit (fun k => heisFourierMat ζ a k) (fun k => Ψ k b)
  rw [fourierBirefl, hΨinv, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, hT]
  rw [hmain, hsum1, hΦ0, hΦ1, hΨ0, hΨ1]
  ring

theorem sparse_mul_heisFourierMat [NeZero p] {ζ : F} (hζ : ζ ^ p = 1) :
    (1 + heisShiftMat F p + heisShiftMat F p ^ 2) * heisFourierMat ζ =
      heisFourierMat ζ * diagonal (fun j : Fin p => 1 + ζ ^ (j : ℕ) + ζ ^ (2 * (j : ℕ))) := by
  have hS := heisShiftMat_mul_heisFourierMat hζ
  have hS2 : heisShiftMat F p ^ 2 * heisFourierMat ζ =
      heisFourierMat ζ * diagonal (fun j : Fin p => ζ ^ (j : ℕ)) *
        diagonal (fun j : Fin p => ζ ^ (j : ℕ)) := by
    rw [sq, mul_assoc (heisShiftMat F p) (heisShiftMat F p) (heisFourierMat ζ), hS, ← mul_assoc,
      hS]
  have hdiag : diagonal (fun j : Fin p => 1 + ζ ^ (j : ℕ) + ζ ^ (2 * (j : ℕ))) =
      1 + diagonal (fun j : Fin p => ζ ^ (j : ℕ)) +
        diagonal (fun j : Fin p => ζ ^ (j : ℕ)) * diagonal (fun j : Fin p => ζ ^ (j : ℕ)) := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply, Matrix.one_apply] <;> ring
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  rw [add_mul, add_mul, one_mul, hS2, hS, hdiag, mul_add, mul_add, mul_one, mul_assoc]

theorem det_sparse (hp : 5 ≤ p) (hp3 : ¬ 3 ∣ p) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    (1 + heisShiftMat F p + heisShiftMat F p ^ 2).det = 3 := by
  haveI : NeZero p := ⟨by omega⟩
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hΦ : (heisFourierMat ζ : Matrix (Fin p) (Fin p) F).det ≠ 0 :=
    det_heisFourierMat_ne_zero hζ
  have hdet : (1 + heisShiftMat F p + heisShiftMat F p ^ 2).det *
      (heisFourierMat ζ : Matrix (Fin p) (Fin p) F).det =
      (heisFourierMat ζ : Matrix (Fin p) (Fin p) F).det *
        (diagonal fun j : Fin p => 1 + ζ ^ (j : ℕ) + ζ ^ (2 * (j : ℕ))).det := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, sparse_mul_heisFourierMat hζp]
  have hδ := mul_right_cancel₀ hΦ (hdet.trans (mul_comm _ _))
  have hg0 : ∀ j : Fin p, j ≠ 0 → ζ ^ (j : ℕ) - 1 ≠ 0 := by
    intro j hj h
    apply hj
    apply Fin.ext
    rw [Fin.val_zero]
    apply hζ.pow_inj j.isLt (NeZero.pos p)
    rw [pow_zero]
    exact sub_eq_zero.mp h
  have hfg : ∀ j : Fin p, (ζ ^ (j : ℕ) - 1) * (1 + ζ ^ (j : ℕ) + ζ ^ (2 * (j : ℕ))) =
      ζ ^ (3 * (j : ℕ)) - 1 := by
    intro j
    have e2 : ζ ^ (2 * (j : ℕ)) = (ζ ^ (j : ℕ)) ^ 2 := by rw [← pow_mul, mul_comm]
    have e3 : ζ ^ (3 * (j : ℕ)) = (ζ ^ (j : ℕ)) ^ 3 := by rw [← pow_mul, mul_comm]
    rw [e2, e3]
    ring
  have hcop : Nat.Coprime p 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hp3).symm
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin p → Fin p, ∀ j : Fin p, ((σ j : Fin p) : ℕ) = (3 * (j : ℕ)) % p :=
    ⟨fun j => ⟨(3 * (j : ℕ)) % p, Nat.mod_lt _ (NeZero.pos p)⟩, fun j => rfl⟩
  have hσinj : Function.Injective σ := by
    intro i j hij
    have h1 : (3 * (i : ℕ)) % p = (3 * (j : ℕ)) % p := by rw [← hσ, ← hσ, hij]
    have h2 : (i : ℕ) ≡ (j : ℕ) [MOD p] := Nat.ModEq.cancel_left_of_coprime hcop h1
    apply Fin.ext
    have h3 : (i : ℕ) % p = (j : ℕ) % p := h2
    rwa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at h3
  have hσsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hσinj
  have hσ0 : σ 0 = 0 := Fin.ext (by rw [hσ]; simp)
  have hσne : ∀ j : Fin p, j ≠ 0 ↔ σ j ≠ 0 := fun j =>
    ⟨fun hj h => hj (hσinj (h.trans hσ0.symm)), fun hj h => hj (by rw [h]; exact hσ0)⟩
  have hσval : ∀ j : Fin p, ζ ^ (3 * (j : ℕ)) = ζ ^ ((σ j : Fin p) : ℕ) := fun j => by
    rw [hσ, pow_eq_pow_mod (3 * (j : ℕ)) hζp]
  have hreindex : ∏ j ∈ Finset.univ.erase (0 : Fin p), (ζ ^ (3 * (j : ℕ)) - 1) =
      ∏ j ∈ Finset.univ.erase (0 : Fin p), (ζ ^ (j : ℕ) - 1) := by
    refine Finset.prod_nbij σ ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_erase] at hj ⊢
      exact ⟨(hσne j).mp hj.1, Finset.mem_univ _⟩
    · intro i _ j _ hij
      exact hσinj hij
    · intro k hk
      obtain ⟨j, rfl⟩ := hσsurj k
      have hk' : σ j ≠ 0 := (Finset.mem_erase.mp (Finset.mem_coe.mp hk)).1
      exact ⟨j, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨(hσne j).mpr hk', Finset.mem_univ _⟩),
        rfl⟩
    · intro j _
      show ζ ^ (3 * (j : ℕ)) - 1 = ζ ^ ((σ j : Fin p) : ℕ) - 1
      rw [hσval j]
  have hprod1 : ∏ j ∈ Finset.univ.erase (0 : Fin p),
      (1 + ζ ^ (j : ℕ) + ζ ^ (2 * (j : ℕ))) = 1 := by
    have hne : ∏ j ∈ Finset.univ.erase (0 : Fin p), (ζ ^ (j : ℕ) - 1) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j hj => hg0 j (Finset.ne_of_mem_erase hj)
    refine mul_left_cancel₀ hne ?_
    rw [mul_one, ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun j _ => hfg j, hreindex]
  have hprod : ∏ j : Fin p, (1 + ζ ^ (j : ℕ) + ζ ^ (2 * (j : ℕ))) = 3 := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : Fin p)), hprod1, mul_one]
    norm_num
  rw [hδ, Matrix.det_diagonal]
  exact hprod

end CFSG.LieType.SeitzGeneration

end
