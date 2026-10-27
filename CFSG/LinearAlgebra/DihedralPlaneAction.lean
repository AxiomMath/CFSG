module

public import CFSG.LinearAlgebra.SL2CoprimeOrder
public import CFSG.CharacterTheory.Semidihedral.Local.ProperSubgroupForms

public section

namespace CFSG.LinearAlgebra

open Polynomial

section Matrices

variable {k : Type*} [Field k]

theorem mul_self_eq_trace_smul_sub_det_smul (A : Matrix (Fin 2) (Fin 2) k) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) k) := by
  have h := Matrix.aeval_self_charpoly A
  rw [Matrix.charpoly_fin_two] at h
  simp only [map_add, map_sub, map_mul, aeval_X_pow, aeval_C, aeval_X,
    Algebra.algebraMap_eq_smul_one] at h
  rw [← sub_eq_zero, ← h, sq, smul_mul_assoc, one_mul]
  abel

theorem det_eq_one_of_conj_eq_inv (hk : (2 : k) ≠ 0) {A A' B : Matrix (Fin 2) (Fin 2) k}
    (hAA' : A * A' = 1) (hBB : B * B = 1) (hBAB : B * A * B = A') (hA2 : A * A ≠ 1) :
    A.det = 1 := by
  have hdet : A.det * A.det = 1 := by
    have h1 := congrArg Matrix.det hAA'
    have h2 := congrArg Matrix.det hBAB
    have h3 := congrArg Matrix.det hBB
    rw [Matrix.det_mul, Matrix.det_one] at h1 h3
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    linear_combination h1 + A.det * h2 - A.det * A.det * h3
  have hCH := mul_self_eq_trace_smul_sub_det_smul A
  have hA'2 : A' * A' = A.trace • A' - A.det • (1 : Matrix (Fin 2) (Fin 2) k) := by
    have h1 : A' * A' = B * (A * A) * B := by
      rw [← hBAB]
      calc B * A * B * (B * A * B) = B * A * (B * B) * A * B := by simp only [mul_assoc]
        _ = B * (A * A) * B := by rw [hBB, mul_one]; simp only [mul_assoc]
    rw [h1, hCH, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
      mul_one, hBAB, hBB]
  have hkey : A.det • (A' * A') = A.trace • A' - (1 : Matrix (Fin 2) (Fin 2) k) := by
    have h1 : (A * A) * (A' * A') = 1 := by
      calc (A * A) * (A' * A') = A * (A * A') * A' := by simp only [mul_assoc]
        _ = 1 := by rw [hAA', mul_one, hAA']
    rw [hCH, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul] at h1
    have h2 : A * (A' * A') = A' := by rw [← mul_assoc, hAA', one_mul]
    rw [h2] at h1
    rw [← h1]
    abel
  rw [hA'2, smul_sub, smul_smul, smul_smul, hdet, one_smul] at hkey
  have hzero : (A.det * A.trace - A.trace) • A' = 0 := by
    rw [sub_smul]
    have h := congrArg (· + (1 : Matrix (Fin 2) (Fin 2) k)) hkey
    simp only [sub_add_cancel] at h
    rw [h]
    abel
  rcases mul_self_eq_one_iff.mp hdet with hd | hd
  · exact hd
  · exfalso
    rw [hd] at hzero
    have h1 := congrArg (A * ·) hzero
    simp only [mul_smul_comm, hAA', mul_zero] at h1
    have ht : A.trace = 0 := by
      have h2 := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 0) h1
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        Matrix.zero_apply] at h2
      have h3 : (2 : k) * A.trace = 0 := by linear_combination -h2
      exact (mul_eq_zero.mp h3).resolve_left hk
    apply hA2
    rw [hCH, ht, hd, zero_smul, neg_one_smul, zero_sub, neg_neg]

theorem det_eq_neg_one_of_mul_self_eq_one (hk : (2 : k) ≠ 0) {B : Matrix (Fin 2) (Fin 2) k}
    (hBB : B * B = 1) (hB1 : B ≠ 1) (hBm1 : B ≠ -1) : B.det = -1 := by
  have hdet : B.det * B.det = 1 := by
    have h := congrArg Matrix.det hBB
    rwa [Matrix.det_mul, Matrix.det_one] at h
  rcases mul_self_eq_one_iff.mp hdet with hd | hd
  · exfalso
    have hCH := mul_self_eq_trace_smul_sub_det_smul B
    rw [hBB, hd, one_smul] at hCH
    have h2 : B.trace • B = (2 : k) • (1 : Matrix (Fin 2) (Fin 2) k) := by
      rw [two_smul]
      have h := congrArg (· + (1 : Matrix (Fin 2) (Fin 2) k)) hCH
      simp only [sub_add_cancel] at h
      exact h.symm
    by_cases ht : B.trace = 0
    · rw [ht, zero_smul] at h2
      have h3 := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 0) h2
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        Matrix.zero_apply] at h3
      exact hk h3.symm
    · have hBc : B = (B.trace⁻¹ * 2) • (1 : Matrix (Fin 2) (Fin 2) k) := by
        rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ ht, one_smul]
      have hc : (B.trace⁻¹ * 2) * (B.trace⁻¹ * 2) = 1 := by
        have h3 := hBB
        rw [hBc, smul_mul_smul_comm, one_mul] at h3
        have h4 := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 0) h3
        simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using h4
      rcases mul_self_eq_one_iff.mp hc with hc1 | hc1
      · exact hB1 (by rw [hBc, hc1, one_smul])
      · exact hBm1 (by rw [hBc, hc1, neg_one_smul])
  · exact hd

end Matrices

theorem two_dimensional_dihedral_action_rotation_order_bound {k : Type*} [Field k] [Finite k]
    (hq : Odd (Nat.card k)) {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : Module.finrank k V = 2) (e : ℕ) (he : 2 ≤ e)
    (α β : LinearMap.GeneralLinearGroup k V) (hαM : α ^ (2 ^ e) = 1)
    (hαhalf : α ^ (2 ^ e / 2) = -1) (hβ2 : β ^ 2 = 1) (hβαβ : β * α * β = α⁻¹) :
    orderOf α = 2 ^ e ∧ LinearMap.det (α : V →ₗ[k] V) = 1 ∧
      orderOf β = 2 ∧ LinearMap.det (β : V →ₗ[k] V) = -1 ∧
      (∃ φ : DihedralGroup (2 ^ e) ≃*
          Subgroup.closure ({α, β} : Set (LinearMap.GeneralLinearGroup k V)),
        (φ (DihedralGroup.r 1) : LinearMap.GeneralLinearGroup k V) = α ∧
          (φ (DihedralGroup.sr 0) : LinearMap.GeneralLinearGroup k V) = β) ∧
      Nat.card (DihedralGroup (2 ^ e)) = 2 * 2 ^ e ∧
      (2 ^ e ∣ Nat.card k - 1 ∨ 2 ^ e ∣ Nat.card k + 1) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have hchar : ringChar k ≠ 2 := by
    intro h
    have h1 := FiniteField.even_card_iff_char_two.mp h
    rw [Nat.card_eq_fintype_card] at hq
    rw [Nat.odd_iff] at hq
    omega
  have hk : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  let b := Module.finBasisOfFinrankEq k V hV
  let ψ := LinearMap.toMatrixAlgEquiv b
  have hψdet : ∀ g : V →ₗ[k] V, (ψ g).det = LinearMap.det g := fun g =>
    LinearMap.det_toMatrix b g
  have hψinj : Function.Injective ψ := ψ.injective
  have hAA' : ψ (α : V →ₗ[k] V) * ψ ((α⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hBB : ψ (β : V →ₗ[k] V) * ψ (β : V →ₗ[k] V) = 1 := by
    rw [← map_mul, ← Units.val_mul, ← sq, hβ2, Units.val_one, map_one]
  have hBAB : ψ (β : V →ₗ[k] V) * ψ (α : V →ₗ[k] V) * ψ (β : V →ₗ[k] V) =
      ψ ((α⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) := by
    rw [← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, hβαβ]
  have hneg : (-1 : LinearMap.GeneralLinearGroup k V) ≠ 1 := by
    intro h
    have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup k V => ψ (g : V →ₗ[k] V) 0 0) h
    simp only [Units.val_neg, Units.val_one, map_neg, map_one, Matrix.neg_apply,
      Matrix.one_apply_eq] at h1
    apply hk
    linear_combination -h1
  have hα : orderOf α = 2 ^ e := by
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime_pow ?_ hαM
    rw [show 2 ^ (e' + 1) / 2 = 2 ^ e' by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]]
      at hαhalf
    rw [hαhalf]
    exact hneg
  have hα2 : α ^ 2 ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hα] at h1
    have h2 : 2 ^ 2 ∣ 2 ^ e := Nat.pow_dvd_pow 2 he
    have := Nat.le_of_dvd (by norm_num) (h2.trans h1)
    norm_num at this
  have hA2 : ψ (α : V →ₗ[k] V) * ψ (α : V →ₗ[k] V) ≠ 1 := by
    intro h
    apply hα2
    apply Units.ext
    apply hψinj
    rw [Units.val_pow_eq_pow_val, map_pow, sq, h, Units.val_one, map_one]
  have hdetα : LinearMap.det (α : V →ₗ[k] V) = 1 := by
    rw [← hψdet]
    exact det_eq_one_of_conj_eq_inv hk hAA' hBB hBAB hA2
  have hαinv : ∀ γ : LinearMap.GeneralLinearGroup k V, γ * α = α * γ → γ ^ 2 = 1 →
      γ * α * γ = α⁻¹ → False := by
    intro γ hcomm hγ2 hγ
    apply hα2
    have h1 : α = α⁻¹ := by
      rw [← hγ, hcomm, mul_assoc, ← sq, hγ2, mul_one]
    rw [sq]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel α
  have hβ1 : β ≠ 1 := fun h => hαinv β (by rw [h, one_mul, mul_one]) hβ2 hβαβ
  have hβm1 : β ≠ -1 := fun h => hαinv β (by rw [h, neg_one_mul, mul_neg_one]) hβ2 hβαβ
  have hB1 : ψ (β : V →ₗ[k] V) ≠ 1 := by
    intro h
    apply hβ1
    apply Units.ext
    apply hψinj
    rw [h, Units.val_one, map_one]
  have hBm1 : ψ (β : V →ₗ[k] V) ≠ -1 := by
    intro h
    apply hβm1
    apply Units.ext
    apply hψinj
    rw [h, Units.val_neg, Units.val_one, map_neg, map_one]
  have hdetβ : LinearMap.det (β : V →ₗ[k] V) = -1 := by
    rw [← hψdet]
    exact det_eq_neg_one_of_mul_self_eq_one hk hBB hB1 hBm1
  have hβ : orderOf β = 2 := orderOf_eq_prime hβ2 hβ1
  have hdih : ∃ φ : DihedralGroup (2 ^ e) ≃*
      Subgroup.closure ({α, β} : Set (LinearMap.GeneralLinearGroup k V)),
      (φ (DihedralGroup.r 1) : LinearMap.GeneralLinearGroup k V) = α ∧
        (φ (DihedralGroup.sr 0) : LinearMap.GeneralLinearGroup k V) = β := by
    set H := Subgroup.closure ({α, β} : Set (LinearMap.GeneralLinearGroup k V)) with hH
    have hαH : α ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
    have hβH : β ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have hgen := CFSG.Semidihedral.Local.closure_pair_subtype_eq_top hαH hβH hH
    have hu : orderOf (⟨α, hαH⟩ : H) = 2 ^ e := by rw [Subgroup.orderOf_mk, hα]
    have hx : (⟨β, hβH⟩ : H) ∉ Subgroup.zpowers (⟨α, hαH⟩ : H) := by
      intro h
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
      have hj' : α ^ j = β := by simpa using congrArg Subtype.val hj
      exact hαinv β (by rw [← hj', ← zpow_add_one, ← zpow_one_add, add_comm]) hβ2 hβαβ
    have hx2 : (⟨β, hβH⟩ : H) ^ 2 = 1 := Subtype.ext (by simpa using hβ2)
    have hxu : (⟨β, hβH⟩ : H) * ⟨α, hαH⟩ * (⟨β, hβH⟩ : H)⁻¹ = (⟨α, hαH⟩ : H)⁻¹ := by
      apply Subtype.ext
      have hβinv : β⁻¹ = β := by
        rw [inv_eq_iff_mul_eq_one, ← sq, hβ2]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hβinv, hβαβ]
    obtain ⟨φ, hφ1, hφ2⟩ := CFSG.Semidihedral.Local.dihedral_normal_form hgen hu hx hx2 hxu
    exact ⟨φ, congrArg Subtype.val hφ1, congrArg Subtype.val hφ2⟩
  have hdiv : 2 ^ e ∣ Nat.card k - 1 ∨ 2 ^ e ∣ Nat.card k + 1 := by
    have hA : (ψ (α : V →ₗ[k] V)).det = 1 := by rw [hψdet, hdetα]
    have horder : orderOf (ψ (α : V →ₗ[k] V)) = 2 ^ e := by
      have h := orderOf_injective ψ.toRingEquiv.toMonoidHom hψinj (α : V →ₗ[k] V)
      exact h.trans (orderOf_units.trans hα)
    have hp := CharP.char_is_prime k (ringChar k)
    have hcop : Nat.Coprime (orderOf (ψ (α : V →ₗ[k] V))) (ringChar k) := by
      rw [horder]
      apply Nat.Coprime.pow_left
      exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hchar)
    have h := (finite_field_SL2_coprime_cyclic_order (K := k) (ringChar k)).1 _ hA hcop
    rwa [horder] at h
  exact ⟨hα, hdetα, hβ, hdetβ, hdih, DihedralGroup.nat_card, hdiv⟩

end CFSG.LinearAlgebra
