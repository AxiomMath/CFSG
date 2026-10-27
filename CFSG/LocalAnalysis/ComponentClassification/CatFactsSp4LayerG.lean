module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerF
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4F2Model

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K] {a : K}

variable (a) in
@[expose] def Xw (w : QuadraticAlgebra K a 0) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  bA a * kron 1 (qEmb a w) * bAinv a

theorem Xw_mul (ha : a ≠ 0) (v w : QuadraticAlgebra K a 0) :
    Xw a (v * w) = Xw a v * Xw a w := by
  have hk : kron (1 : Matrix (Fin 2) (Fin 2) K) (qEmb a (v * w)) =
      kron 1 (qEmb a v) * kron 1 (qEmb a w) := by
    rw [map_mul, kron_mul, Matrix.one_mul]
  rw [Xw, Xw, Xw, hk]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (bAinv a) (bA a), bAinv_mul_bA ha, Matrix.one_mul]

theorem Xw_one (ha : a ≠ 0) : Xw a 1 = 1 := by
  rw [Xw, map_one, kron_one_one, Matrix.mul_one, bA_mul_bAinv ha]

theorem qEmb_comm_sA (w : QuadraticAlgebra K a 0) : qEmb a w * sA a = sA a * qEmb a w := by
  rw [qEmb_apply, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem Xw_symplectic (ha : a ≠ 0) {w : QuadraticAlgebra K a 0}
    (hn : QuadraticAlgebra.norm w = 1) : (Xw a w)ᵀ * formJ 2 K * Xw a w = formJ 2 K := by
  apply bA_conj_symplectic ha
  have hsw : star w * w = 1 := by
    rw [mul_comm, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hn, map_one]
  rw [kron_transpose, transpose_one, kron_mul, kron_mul, Matrix.one_mul, Matrix.mul_one,
    qEmb_transpose_mul, Matrix.mul_assoc, ← map_mul, hsw, map_one, Matrix.mul_one]

theorem aI_comm_Xw (ha : a ≠ 0) (w : QuadraticAlgebra K a 0) :
    aI a * Xw a w = Xw a w * aI a := by
  have hk : kron 1 (sA a) * kron (1 : Matrix (Fin 2) (Fin 2) K) (qEmb a w) =
      kron 1 (qEmb a w) * kron 1 (sA a) := by
    rw [kron_mul, kron_mul, Matrix.one_mul, qEmb_comm_sA]
  rw [aI, Xw]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (bAinv a) (bA a), bAinv_mul_bA ha, Matrix.one_mul,
    ← Matrix.mul_assoc (bAinv a) (bA a), bAinv_mul_bA ha, Matrix.one_mul,
    ← Matrix.mul_assoc (kron 1 (sA a)), hk, Matrix.mul_assoc]

theorem gI_comm_Xw (ha : a ≠ 0) (k : Matrix.SpecialLinearGroup (Fin 2) K)
    (w : QuadraticAlgebra K a 0) :
    (bA a * kron (k : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a) * Xw a w =
      Xw a w * (bA a * kron (k : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a) := by
  have hk : kron (k : Matrix (Fin 2) (Fin 2) K) 1 * kron 1 (qEmb a w) =
      kron 1 (qEmb a w) * kron (k : Matrix (Fin 2) (Fin 2) K) 1 := by
    rw [kron_mul, kron_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  rw [Xw]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (bAinv a) (bA a), bAinv_mul_bA ha, Matrix.one_mul,
    ← Matrix.mul_assoc (bAinv a) (bA a), bAinv_mul_bA ha, Matrix.one_mul,
    ← Matrix.mul_assoc (kron (k : Matrix (Fin 2) (Fin 2) K) 1), hk, Matrix.mul_assoc]

variable (a) in
abbrev torus : Subgroup (QuadraticAlgebra K a 0)ˣ :=
  (Units.map (QuadraticAlgebra.norm : QuadraticAlgebra K a 0 →* K)).ker

theorem norm_of_mem_torus {u : (QuadraticAlgebra K a 0)ˣ} (hu : u ∈ torus a) :
    QuadraticAlgebra.norm (u : QuadraticAlgebra K a 0) = 1 := by
  have := congrArg Units.val (MonoidHom.mem_ker.mp hu)
  exact this

@[expose] def torusHom (ha : a ≠ 0) : torus a →* StatedSp 2 K where
  toFun u := toSp (Xw a ((u : (QuadraticAlgebra K a 0)ˣ) : QuadraticAlgebra K a 0))
    (Xw_symplectic ha (norm_of_mem_torus u.2))
  map_one' := by
    apply sp_ext
    rw [coe_toSp]
    simp only [OneMemClass.coe_one, Units.val_one]
    rw [Xw_one ha]
  map_mul' u v := by
    apply sp_ext
    simp only [coe_toSp, Subgroup.coe_mul, Units.val_mul]
    exact Xw_mul ha _ _

theorem coe_torusHom (ha : a ≠ 0) (u : torus a) :
    (((torusHom ha u : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Xw a ((u : (QuadraticAlgebra K a 0)ˣ) : QuadraticAlgebra K a 0) :=
  coe_toSp _ (Xw_symplectic ha (norm_of_mem_torus u.2))

theorem eq_one_or_neg_of_proj_torusHom (ha : a ≠ 0) {u : torus a}
    (hu : proj 2 K (torusHom ha u) = 1) :
    ((u : (QuadraticAlgebra K a 0)ˣ) : QuadraticAlgebra K a 0) = 1 ∨
      ((u : (QuadraticAlgebra K a 0)ˣ) : QuadraticAlgebra K a 0) = -1 := by
  rw [← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff, coe_torusHom] at hu
  set w := ((u : (QuadraticAlgebra K a 0)ˣ) : QuadraticAlgebra K a 0)
  have hk : ∀ c : K, Xw a w = c • 1 → kron (1 : Matrix (Fin 2) (Fin 2) K) (qEmb a w) = c • 1 := by
    intro c hc
    have h1 := congrArg (fun M => bAinv a * M * bA a) hc
    simp only [Xw, Matrix.mul_assoc] at h1
    rw [← Matrix.mul_assoc (bAinv a) (bA a), bAinv_mul_bA ha, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, bAinv_mul_bA ha] at h1
    exact h1
  have hq : ∀ c : K, kron (1 : Matrix (Fin 2) (Fin 2) K) (qEmb a w) = c • 1 →
      w = algebraMap K _ c := by
    intro c hc
    apply qEmb_injective a
    rw [qEmb_algebraMap]
    have e1 : kron (1 : Matrix (Fin 2) (Fin 2) K) (qEmb a w) =
        fromBlocks (qEmb a w) 0 0 (qEmb a w) := by simp [kron]
    have e2 : (c • 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks (c • 1) 0 0 (c • 1) := by
      rw [← fromBlocks_one, fromBlocks_smul, smul_zero]
    rw [e1, e2] at hc
    exact (fromBlocks_inj.mp hc).1
  rcases hu with h | h
  · left
    have := hq 1 (hk 1 (by rw [one_smul]; exact h))
    rw [this, map_one]
  · right
    have := hq (-1) (hk (-1) (by rw [neg_one_smul]; exact h))
    rw [this, map_neg, map_one]

theorem exists_y_alphaI [Finite K] (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) (h5 : 5 ≤ Nat.card K)
    (hna : ∀ l : K, l ^ 2 ≠ -a) (hs : IsSimpleGroup (StatedProj (StatedSp 2 K))) :
    ∃ y ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range,
      y * alphaI ha = alphaI ha * y ∧ (∀ t ∈ JI ha, y t = t) ∧ Odd (orderOf y) ∧ y ≠ 1 := by
  have h4 : 4 ≤ Nat.card K := by omega
  have : Finite (QuadraticAlgebra K a 0) := Finite.of_equiv _ (QuadraticAlgebra.equivProd a 0).symm
  obtain ⟨v, hvn, hvo, hv1⟩ := exists_odd_order_torus h2 h5 ha hna
  have hvT : v ∈ torus a := by
    rw [MonoidHom.mem_ker]
    exact Units.ext hvn
  set x := proj 2 K (torusHom ha ⟨v, hvT⟩) with hx
  have hxo : orderOf x = orderOf v := by
    have hφ : ∀ n : ℕ, x ^ n = 1 → v ^ n = 1 := by
      intro n hn
      rw [hx, ← map_pow, ← map_pow] at hn
      have hpow : ((⟨v, hvT⟩ : torus a) ^ n : torus a) = ⟨v ^ n, pow_mem hvT n⟩ := rfl
      rw [hpow] at hn
      rcases eq_one_or_neg_of_proj_torusHom ha hn with h | h
      · exact Units.ext h
      · exfalso
        have h' : v ^ (2 * n) = 1 := by
          apply Units.ext
          rw [pow_mul', Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_two]
          simp only at h
          rw [Units.val_pow_eq_pow_val] at h
          rw [h, neg_mul_neg, one_mul, Units.val_one]
        have hd : orderOf v ∣ 2 * n := orderOf_dvd_of_pow_eq_one h'
        have hcop : Nat.Coprime (orderOf v) 2 := Nat.coprime_two_right.mpr hvo
        have hdn : orderOf v ∣ n := hcop.dvd_of_dvd_mul_left hd
        have hvn' : v ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp hdn
        simp only at h
        rw [Units.val_pow_eq_pow_val] at h
        rw [← Units.val_pow_eq_pow_val, hvn', Units.val_one] at h
        have := congrArg QuadraticAlgebra.re h
        rw [QuadraticAlgebra.re_one, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one] at this
        apply h2
        linear_combination this
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      rw [hx, ← map_pow, ← map_pow]
      have : ((⟨v, hvT⟩ : torus a) ^ orderOf v : torus a) = 1 := by
        apply Subtype.ext
        exact pow_orderOf_eq_one v
      rw [this, map_one, map_one]
    · exact orderOf_dvd_of_pow_eq_one (hφ _ (pow_orderOf_eq_one x))
  have hcinj : Function.Injective (MulAut.conj : StatedProj (StatedSp 2 K) →* _) := by
    intro g h hgh
    exact conj_injective_of_center (fun z hz => eq_one_of_mem_center_P h2 h4 hs hz) hgh
  have hXa : alphaI ha x = x := by
    rw [hx, alphaI, conjAut_proj]
    congr 1
    apply sp_ext
    set A : GL (Fin 2 ⊕ Fin 2) K := ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) with hAdef
    have hA : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = aI a := rfl
    rw [coe_conjSp, ← hAdef, Units.val_mul, Units.val_mul, hA, coe_torusHom, aI_comm_Xw ha,
      Matrix.mul_assoc, ← hA, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  refine ⟨MulAut.conj x, ⟨x, rfl⟩, ?_, ?_, ?_, ?_⟩
  · ext t
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hXa]
  · rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    have hcS : torusHom ha ⟨v, hvT⟩ * gI ha k = gI ha k * torusHom ha ⟨v, hvT⟩ := by
      apply sp_ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_torusHom,
        coe_gI]
      exact (gI_comm_Xw ha k _).symm
    rw [MulAut.conj_apply, hx, ← map_inv, ← map_mul, ← map_mul, hcS, mul_inv_cancel_right]
  · rw [orderOf_injective _ hcinj x, hxo]
    exact hvo
  · intro h
    have h1 : x = 1 := hcinj (h.trans (map_one _).symm)
    have := orderOf_one (G := StatedProj (StatedSp 2 K))
    rw [← h1, hxo] at this
    exact hv1 this

end CFSG.ComponentClassification.CatFactsSp4
