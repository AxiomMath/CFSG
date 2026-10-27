module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainStabNormalizer
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SemilinearConj
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainDet

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly.LowTwoRank

theorem exists_order_nine {G : Type*} [Group G] (Et Z : Subgroup G) (hZ : Z ≤ Et)
    (hZc : Nat.card Z ∣ 3) (hE : Nat.card Et = 27) :
    ∃ F : Subgroup G, F ≤ Et ∧ Z ≤ F ∧ Nat.card F = 9 := by
  have : Finite Et := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨F, hF, hZF, hFE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (p := 3) (n := 2)
    Nat.prime_three (H := Z) (L := Et) (hZc.trans (by norm_num)) (by rw [hE]; norm_num) hZ
  exact ⟨F, hFE, hZF, by simpa using hF⟩

section Tau

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def semilinearTau (φ : K ≃+* K) (At : GL (Fin n) K) :
    (Fin n → K) ≃+ (Fin n → K) where
  toFun v := (At : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (v i)
  invFun w := fun i => φ.symm ((((At⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) i)
  left_inv v := by
    funext i
    simp only
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    simp
  right_inv w := by
    have : (fun i => φ (φ.symm ((((At⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) i))) =
        (((At⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) := by
      funext i; simp
    simp only
    rw [this, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  map_add' v w := by
    show (At : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ ((v + w) i)) =
      ((At : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (v i)) +
        ((At : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (w i))
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp

theorem semilinearTau_apply (φ : K ≃+* K) (At : GL (Fin n) K) (v : Fin n → K) :
    semilinearTau φ At v = (At : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (v i) := rfl

theorem semilinearTau_smul (φ : K ≃+* K) (At : GL (Fin n) K) (c : K) (v : Fin n → K) :
    semilinearTau φ At (c • v) = φ c • semilinearTau φ At v := by
  rw [semilinearTau_apply, semilinearTau_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem glToLin_conj_tau (φ : K ≃+* K) (At A : GL (Fin n) K) (v : Fin n → K) :
    (((glToLin n K (At * glAut φ A * At⁻¹) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) (semilinearTau φ At v) =
    semilinearTau φ At
      (((glToLin n K A : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) v) := by
  rw [glToLin_apply, glToLin_apply, semilinearTau_apply, semilinearTau_apply]
  have h1 : (((At * glAut φ A * At⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((At : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (v i)) =
      (At : Matrix (Fin n) (Fin n) K) *ᵥ
        (((A : Matrix (Fin n) (Fin n) K).map φ) *ᵥ fun i => φ (v i)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, coe_glAut_eq_map,
      mul_assoc, mul_assoc, Units.inv_mul, mul_one]
  rw [h1]
  congr 1
  funext i
  exact (RingHom.map_mulVec (φ : K →+* K) (A : Matrix (Fin n) (Fin n) K) v i).symm

end Tau

section Det

variable {K : Type} [Field K] {n : ℕ}

theorem det_scalar_eq (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) c) : Kˣ) : K) =
      (c : K) ^ n := by
  simp

theorem det_glAut_eq (φ : K ≃+* K) (A : GL (Fin n) K) :
    ((Matrix.GeneralLinearGroup.det (glAut φ A) : Kˣ) : K) =
      φ ((Matrix.GeneralLinearGroup.det A : Kˣ) : K) := by
  simp only [Matrix.GeneralLinearGroup.val_det_apply, coe_glAut_eq_map]
  exact (RingHom.map_det (φ : K →+* K) (A : Matrix (Fin n) (Fin n) K)).symm

theorem exists_order_nine_of_det (hK : Nat.card K = 4) (φ : K ≃+* K) (At : GL (Fin n) K)
    (hn : n = 6) (Et : Subgroup (GL (Fin n) K)) (hcard : Nat.card Et = 27)
    (hZ : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ Et)
    (hstab : ∀ A ∈ Et, At * glAut φ A * At⁻¹ ∈ Et)
    (hex : ∃ A ∈ Et, Matrix.GeneralLinearGroup.det A ≠ 1) :
    ∃ F : Subgroup (GL (Fin n) K), F ≤ Et ∧ Nat.card F = 9 ∧
      (∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ F) ∧
      ∀ A ∈ F, At * glAut φ A * At⁻¹ ∈ F := by
  set ψ : Et →* Kˣ := (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).comp Et.subtype with hψ
  have hKu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have hrange : Nat.card ψ.range = 3 := by
    have h1 : Nat.card ψ.range ∣ 3 := hKu ▸ Subgroup.card_subgroup_dvd_card ψ.range
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exfalso
      obtain ⟨A, hA, hdet⟩ := hex
      have : ψ.range = ⊥ := Subgroup.card_eq_one.1 h
      have h2 : ψ ⟨A, hA⟩ ∈ ψ.range := ⟨⟨A, hA⟩, rfl⟩
      rw [this, Subgroup.mem_bot] at h2
      exact hdet h2
    · exact h
  have hker : Nat.card ψ.ker = 9 := by
    have h1 := ψ.ker.card_mul_index
    rw [Subgroup.index_ker, hrange, hcard] at h1
    omega
  refine ⟨ψ.ker.map Et.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Et.subtype_injective, hker]
  · intro c
    refine ⟨⟨_, hZ c⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    show ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) c) : Kˣ) : K) = 1
    rw [det_scalar_eq, hn]
    have := congrArg Units.val (units_pow_three_of_card_four hK c)
    have h3 : (c : K) ^ 3 = 1 := by simpa using this
    rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, h3, one_pow]
  · rintro A ⟨a, ha, rfl⟩
    refine ⟨⟨_, hstab a.1 a.2⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at ha ⊢
    apply Units.ext
    have h1 : ((ψ a : Kˣ) : K) = 1 := by rw [ha]; rfl
    show ((Matrix.GeneralLinearGroup.det (At * glAut φ a.1 * At⁻¹) : Kˣ) : K) = 1
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, det_glAut_eq]
    have h2 : ((Matrix.GeneralLinearGroup.det a.1 : Kˣ) : K) = 1 := h1
    rw [h2, map_one, mul_one, map_inv, Units.val_inv_eq_inv_val]
    exact mul_inv_cancel₀ (Units.ne_zero _)

end Det

end CFSG.HardMathSupport.Curtis.UnitaryLevi
