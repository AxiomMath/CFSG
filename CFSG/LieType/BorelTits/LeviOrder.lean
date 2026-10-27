module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

open CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.LieType.BorelTits

variable {K : Type*} [Field K]

theorem card_ker_det_eq [Finite K] {N : Type*} [AddCommGroup N] [Module K N]
    [FiniteDimensional K N] :
    Nat.card ↥(Units.map (LinearMap.det : Module.End K N →* K)).ker =
      Nat.card (Matrix.SpecialLinearGroup (Fin (Module.finrank K N)) K) := by
  classical
  set n := Module.finrank K N
  let b := Module.finBasis K N
  let θ : (Module.End K N)ˣ ≃* (Matrix (Fin n) (Fin n) K)ˣ :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  have hdet : ∀ γ : (Module.End K N)ˣ,
      Matrix.GeneralLinearGroup.det (θ γ) =
        Units.map (LinearMap.det : Module.End K N →* K) γ := by
    intro γ
    apply Units.ext
    change Matrix.det (LinearMap.toMatrix b b (γ : Module.End K N)) =
      LinearMap.det (γ : Module.End K N)
    exact LinearMap.det_toMatrix b _
  have hmap : (Units.map (LinearMap.det : Module.End K N →* K)).ker.map θ.toMonoidHom =
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin n) K →* Kˣ).ker := by
    ext A
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      show Matrix.GeneralLinearGroup.det (θ γ) = 1
      rw [hdet]
      exact hγ
    · intro hA
      refine ⟨θ.symm A, ?_, by simp⟩
      show Units.map (LinearMap.det : Module.End K N →* K) (θ.symm A) = 1
      rw [← hdet, θ.apply_symm_apply]
      exact hA
  let e : (Units.map (LinearMap.det : Module.End K N →* K)).ker ≃*
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin n) K →* Kˣ).ker :=
    (θ.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  exact Nat.card_congr (e.trans Matrix.SpecialLinearGroup.toGLKerEquiv.symm).toEquiv

theorem card_specialLinearGroup_fin_one [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 1) K) = 1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_one]
  simp only [Fin.val_zero, pow_zero, pow_one]
  exact Nat.div_self (by omega : 0 < Fintype.card K - 1)

theorem card_specialLinearGroup_fin_two [Finite K] {Q : ℕ} (hK : Nat.card K = Q) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Q * (Q ^ 2 - 1) := by
  letI : Fintype K := Fintype.ofFinite K
  have hQ : Fintype.card K = Q := by rw [← Nat.card_eq_fintype_card, hK]
  have hq : 1 < Q := hQ ▸ Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, hQ]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have h2 : Q ^ 2 - Q = Q * (Q - 1) := by rw [Nat.mul_sub_one, sq]
  rw [h2, ← mul_assoc, Nat.mul_div_cancel _ (by omega : 0 < Q - 1)]
  ring

theorem card_specialLinearGroup_fin_three [Finite K] {Q : ℕ} (hK : Nat.card K = Q) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) =
      Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1) := by
  letI : Fintype K := Fintype.ofFinite K
  have hQ : Fintype.card K = Q := by rw [← Nat.card_eq_fintype_card, hK]
  have hq : 1 < Q := hQ ▸ Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_three, hQ]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  have hfac : (Q ^ 3 - 1) * (Q ^ 3 - Q) * (Q ^ 3 - Q ^ 2) =
      (Q - 1) * (Q ^ 3 * (Q ^ 2 - 1) * (Q ^ 3 - 1)) := by
    have h1 : 1 ≤ Q := by omega
    have h2 : Q ≤ Q ^ 2 := by
      simpa using Nat.pow_le_pow_right (by omega : Q > 0) (by norm_num : 1 ≤ 2)
    have h3 : Q ^ 2 ≤ Q ^ 3 :=
      Nat.pow_le_pow_right (by omega : Q > 0) (by norm_num : 2 ≤ 3)
    have h4 : 1 ≤ Q ^ 3 := Nat.one_le_pow 3 Q (by omega : 0 < Q)
    have h5 : Q ≤ Q ^ 3 := h2.trans h3
    have h6 : 1 ≤ Q ^ 2 := Nat.one_le_pow 2 Q (by omega : 0 < Q)
    zify [h1, h2, h3, h4, h5, h6]
    ring
  rw [hfac, Nat.mul_div_cancel_left _ (by omega : 0 < Q - 1)]

theorem card_sesqSpecialUnitaryGroup_of_finrank_eq_zero {σ : K →+* K} {N : Type*}
    [AddCommGroup N] [Module K N] [FiniteDimensional K N] (B : N →ₛₗ[σ] N →ₗ[K] K)
    (hN : Module.finrank K N = 0) : Nat.card ↥(sesqSpecialUnitaryGroup B) = 1 := by
  haveI : Subsingleton N := Module.finrank_zero_iff.mp hN
  haveI : Subsingleton (LinearMap.GeneralLinearGroup K N) :=
    ⟨fun a b => Units.ext (LinearMap.ext fun v => Subsingleton.elim _ _)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1, Subgroup.one_mem _⟩⟩

theorem card_sesqSpecialUnitaryGroup_two {p f : ℕ} (h : UnitaryFieldData p f K) {N : Type*}
    [AddCommGroup N] [Module K N] [FiniteDimensional K N] {B : N →ₛₗ[h.bar] N →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) (hN : Module.finrank K N = 2) :
    Nat.card ↥(sesqSpecialUnitaryGroup B) = p ^ f * ((p ^ f) ^ 2 - 1) := by
  have hSU := (CFSG.LinearGroups.unitary_full_group_order h hB hBl hN
    (by norm_num : 1 ≤ 2)).2.1
  rw [show 2 * (2 - 1) / 2 = 1 by norm_num, Finset.Icc_self,
    Finset.prod_singleton] at hSU
  norm_num at hSU
  have hcast : ((p ^ f * ((p ^ f) ^ 2 - 1) : ℕ) : ℤ) =
      (p ^ f : ℤ) * ((p ^ f : ℤ) ^ 2 - 1) := by
    have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow 2 (p ^ f) (pow_pos h.prime.pos f)
    push_cast [Nat.cast_sub h1]
    ring_nf
  have hSU' : (Nat.card ↥(sesqSpecialUnitaryGroup B) : ℤ) =
      ((p ^ f * ((p ^ f) ^ 2 - 1) : ℕ) : ℤ) := by
    rw [hcast, hSU]
  exact_mod_cast hSU'

theorem card_sesqSpecialUnitaryGroup_four {p f : ℕ} (h : UnitaryFieldData p f K) {N : Type*}
    [AddCommGroup N] [Module K N] [FiniteDimensional K N] {B : N →ₛₗ[h.bar] N →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) (hN : Module.finrank K N = 4) :
    Nat.card ↥(sesqSpecialUnitaryGroup B) =
      (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) := by
  have hSU := (CFSG.LinearGroups.unitary_full_group_order h hB hBl hN
    (by norm_num : 1 ≤ 4)).2.1
  rw [show 4 * (4 - 1) / 2 = 6 by norm_num,
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3 + 1),
    Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1),
    Finset.Icc_self, Finset.prod_singleton] at hSU
  norm_num at hSU
  have hcast : (((p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) *
      ((p ^ f) ^ 4 - 1) : ℕ) : ℤ) =
      (p ^ f : ℤ) ^ 6 * ((p ^ f : ℤ) ^ 2 - 1) * ((p ^ f : ℤ) ^ 3 + 1) *
        ((p ^ f : ℤ) ^ 4 - 1) := by
    have h2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow 2 (p ^ f) (pow_pos h.prime.pos f)
    have h4 : 1 ≤ (p ^ f) ^ 4 := Nat.one_le_pow 4 (p ^ f) (pow_pos h.prime.pos f)
    push_cast [Nat.cast_sub h2, Nat.cast_sub h4]
    ring_nf
  have hSU' : (Nat.card ↥(sesqSpecialUnitaryGroup B) : ℤ) =
      (((p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) *
        ((p ^ f) ^ 4 - 1) : ℕ) : ℤ) := by
    rw [hcast, hSU]
    ring
  exact_mod_cast hSU'

end CFSG.LieType.BorelTits

end
