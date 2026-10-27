module

public import CFSG.CGT.Foote81L6.Bridge.SD
public import CFSG.CGT.Foote81L6.Bridge.Arith
public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowSemidihedral
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhSquare

public section

namespace CFSG.CGT.Foote81L6.Bridge

open Matrix

structure GL2Data (K : Type) [Field K] (n : ℕ) where
  ω : GL (Fin 2) K
  σ : GL (Fin 2) K
  orderOf_ω : orderOf ω = 2 ^ n
  ω_pow_hf : ω ^ (hf n).val = -1
  σ_sq : σ ^ 2 = 1
  conj : σ * ω * σ⁻¹ = ω ^ (θ n).val
  σ_not_mem : σ ∉ Subgroup.zpowers ω
  det_ω : (ω : Matrix (Fin 2) (Fin 2) K).det = -1
  det_σ : (σ : Matrix (Fin 2) (Fin 2) K).det = -1

theorem exists_gl2Data {K : Type} [Field K] [Finite K] (hq : Nat.card K % 4 = 3) :
    Nonempty (GL2Data K ((Nat.card K ^ 2 - 1).factorization 2)) := by
  set q := Nat.card K with hqdef
  obtain ⟨u, hu, hqu, hn⟩ := exists_odd_q_add_one hq
  set n := (q ^ 2 - 1).factorization 2 with hndef
  have hn1 : n - 1 + 1 = n := by omega
  have hdvd : 2 ^ (n - 1 + 1) ∣ q ^ 2 - 1 := by
    rw [hn1]
    exact Nat.ordProj_dvd _ _
  obtain ⟨A, hAord, hAhalf, hAconj⟩ := CFSG.BrauerLinearThree.exists_nonsplit_element hq hdvd
  rw [hn1] at hAord
  set σ : GL (Fin 2) K := CFSG.DesarguesianPlanes.diagGL 1 (-1) with hσdef
  have hσ2 : σ ^ 2 = 1 := by
    rw [hσdef, CFSG.DesarguesianPlanes.diagGL_pow, one_pow, neg_one_sq,
      CFSG.DesarguesianPlanes.diagGL_one_one]
  have hσinv : σ⁻¹ = σ := CFSG.BrauerLinearThree.diagGL_one_neg_one_inv
  have hAq : A ^ q = A ^ (θ n).val := by
    rw [← pow_mod_orderOf A q, hAord, mod_two_pow_v2 hq, θ_val (by omega)]
  have hconj : σ * A * σ⁻¹ = A ^ (θ n).val := hAconj.trans hAq
  have hdetσ : (σ : Matrix (Fin 2) (Fin 2) K).det = -1 := by
    simp [hσdef, CFSG.DesarguesianPlanes.diagGL, Matrix.det_fin_two]
  have hsq : (σ * A) * (σ * A) = -1 := by
    have h1 : (σ * A) * (σ * A) = (σ * A * σ⁻¹) * A := by rw [hσinv]; group
    have h2 : A ^ (q + 1) = -1 := by
      rw [hqu, pow_mul, hAhalf, hu.neg_one_pow]
    rw [h1, hAconj, ← pow_succ, h2]
  have hK : ∀ a : K, a * a ≠ -1 := by
    intro a ha
    let := Fintype.ofFinite K
    have h : IsSquare (-1 : K) := ⟨a, ha.symm⟩
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card] at h
    exact h hq
  have hdetσA : ((σ * A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    apply CFSG.EvenSmallLie.OmegaEight.det_eq_one_of_mul_self_eq_neg_one hK
    rw [← Units.val_mul, hsq, Units.val_neg, Units.val_one]
  have hdetA : (A : Matrix (Fin 2) (Fin 2) K).det = -1 := by
    rw [Units.val_mul, Matrix.det_mul, hdetσ] at hdetσA
    linear_combination -hdetσA
  refine ⟨⟨A, σ, hAord, ?_, hσ2, hconj, ?_, hdetA, hdetσ⟩⟩
  · rw [hf_val (by omega)]
    exact hAhalf
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hcomm : σ * A * σ⁻¹ = A := by
      rw [← hk, (Commute.zpow_self A k).eq, mul_inv_cancel_right]
    rw [hconj] at hcomm
    have h4 : A ^ (θ n).val = A ^ 1 := by rw [pow_one]; exact hcomm
    rw [pow_eq_pow_iff_modEq, hAord] at h4
    have h3 : (((θ n).val : ℕ) : ZMod (2 ^ n)) = ((1 : ℕ) : ZMod (2 ^ n)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).2 h4
    rw [ZMod.natCast_zmod_val, Nat.cast_one] at h3
    exact θ_ne_one hn h3

namespace GL2Data

variable {K : Type} [Field K] {n : ℕ} (D : GL2Data K n)

theorem ω_pow : D.ω ^ 2 ^ n = 1 := by
  rw [← D.orderOf_ω]
  exact pow_orderOf_eq_one D.ω

@[expose] def ι : SD n →* GL (Fin 2) K := SD.lift D.ω_pow D.σ_sq D.conj

theorem ι_apply (x : SD n) : D.ι x = D.ω ^ x.i.val * D.σ ^ x.j.val := rfl

theorem ι_injective : Function.Injective D.ι :=
  SD.lift_injective _ _ _ D.orderOf_ω D.σ_not_mem

theorem ι_z (hn : 2 ≤ n) : D.ι SD.z = -1 := by
  rw [ι_apply]
  change D.ω ^ (hf n).val * D.σ ^ (0 : ZMod 2).val = -1
  rw [ZMod.val_zero, pow_zero, mul_one, D.ω_pow_hf]

theorem neg_one_pow_val_add (a b : ZMod 2) :
    (-1 : K) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ (neg_one_sq : (-1 : K) ^ 2 = 1), pow_add]

theorem det_ι (x : SD n) : ((D.ι x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
    (-1) ^ x.det.val := by
  rw [ι_apply, Units.val_mul, Matrix.det_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    Matrix.det_pow, Matrix.det_pow, D.det_ω, D.det_σ, SD.det, neg_one_pow_val_add, par,
    ZMod.val_natCast, ← pow_eq_pow_mod _ (neg_one_sq : (-1 : K) ^ 2 = 1)]

end GL2Data

end CFSG.CGT.Foote81L6.Bridge
